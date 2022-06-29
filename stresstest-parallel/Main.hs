{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Cardano.Api
  ( AddressAny (AddressShelley),
    AddressInEra (AddressInEra),
    AsType (AsAddressAny, AsAddressInEra, AsPaymentKey, AsSigningKey),
    AssetId (AdaAssetId, AssetId),
    BabbageEra,
    CardanoEra (BabbageEra),
    CardanoMode,
    IsCardanoEra,
    Key,
    LocalNodeConnectInfo,
    NetworkId (Testnet),
    NetworkMagic (NetworkMagic),
    PaymentKey,
    PolicyId (PolicyId),
    ScriptData,
    SerialiseAddress (deserialiseAddress, serialiseAddress),
    SerialiseAsCBOR (deserialiseFromCBOR),
    SerialiseAsRawBytes (deserialiseFromRawBytes),
    ShelleyBasedEra (ShelleyBasedEraAlonzo),
    SigningKey,
    TxId,
    TxIn (TxIn),
    TxIx (TxIx),
    TxOut (TxOut),
    TxOutValue (TxOutAdaOnly, TxOutValue),
    UTxO (UTxO),
    Value,
    deterministicSigningKey,
    deterministicSigningKeySeedSize,
    generateSigningKey,
    getTxBody,
    getTxId,
    hashScriptData,
    lovelaceToValue,
    negateValue,
    prettyPrintJSON,
    shelleyAddressInEra,
    valueFromList,
    valueToList,
    valueToLovelace, Tx, TxBody
  )
import Cardano.Api.Shelley (Address (ShelleyAddress), Lovelace (Lovelace), Quantity (Quantity), fromPlutusData, toShelleyAddr)
import Cardano.Kuber.Api
import Cardano.Kuber.Data.Parsers (parseAssetId, parseAssetIdText, parseAssetNQuantity, parseScriptData)
import Cardano.Kuber.Util (addrInEraToPkh, getDefaultSignKey, queryUtxos, readSignKey, skeyToAddr, skeyToAddrInEra, utxoSum)
import qualified Cardano.Ledger.Address as Shelley
import Cardano.Ledger.Crypto (StandardCrypto)
import Control.Concurrent (MVar, forkIO, killThread, newMVar, putMVar, takeMVar, threadDelay, withMVar)
import Control.Concurrent.Async (forConcurrently, forConcurrently_, mapConcurrently, mapConcurrently_, withAsync)
import Control.Exception (SomeException (SomeException), try)
import Control.Monad (foldM, forM, forM_)
import Control.Monad.Reader (MonadIO (liftIO), ReaderT (runReaderT))
import Control.Monad.State
import Criterion.Main
import Criterion.Main.Options
import Criterion.Types (Config (verbosity), Verbosity (Verbose))
import qualified Data.ByteString.Char8 as BS8
import Data.Function (on)
import Data.IORef (IORef, atomicWriteIORef, newIORef, readIORef)
import Data.List.Split (chunksOf)
import qualified Data.Map as Map
import Data.Maybe (fromJust, fromMaybe, isJust, isNothing)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.IO as TIO
import GHC.Conc (atomically, newTVar)
import GHC.IO.Handle.FD (stdout)
import GHC.Int (Int64)
import PlutusTx (Data (Map), toData, FromData (fromBuiltinData))
import PlutusTx.Prelude (divide)
import System.Clock
import System.Directory (doesFileExist)
import System.Environment (getArgs, getEnv)
import System.IO (BufferMode (NoBuffering), IOMode (ReadMode), hFlush, hGetContents, hSetBuffering, openFile)
import System.Random (newStdGen)
import System.Random.Shuffle (shuffle')
import Text.Read (readMaybe)
import Utils

defaultNoOfWallets = 1

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  putStrLn "\ESC[35m"

  putStrLn "Starting...\n"
  args <- getArgs
  let maybeNoOfWallets = case length args of
        0 -> Just defaultNoOfWallets
        _ -> readMaybe $ last args :: Maybe Int
  --Get no of wallets to be used in test from arguments if not present use defaultNoOfWallets
  let noOfWallets = fromMaybe defaultNoOfWallets maybeNoOfWallets

  dcInfo <- getVasilChainInfo

  let shouldPrintUtxosOnly = not (null args) && head args == "print-utxos-only"
  let shouldRunQueryTestOnly = not (null args) && head args == "run-query-test"

  wallets <- readWalletsFromFile noOfWallets

  if noOfWallets > 1000
    then error "Currently max no of wallets supported are 1000"
    else do
      if shouldPrintUtxosOnly then do
        printUtxoOfWallets dcInfo wallets
      else if shouldRunQueryTestOnly then do
        queryParallelTest dcInfo wallets
      else do
        fundedSignKey <- getDefaultSignKey
        setupWallets wallets dcInfo fundedSignKey
        transferTestOfWallets dcInfo wallets

-- TODO Refactor and remove unused code
setupWallets :: [SigningKey PaymentKey] -> DetailedChainInfo -> SigningKey PaymentKey -> IO ()
setupWallets wallets dcInfo fundedSignKey = do
  let walletsAddrs = map (\s -> AddressShelley $ skeyToAddr s (getNetworkId dcInfo)) wallets
  utxosE <- queryUtxos (getConnectInfo dcInfo) $ Set.fromList walletsAddrs
  utxos@(UTxO utxoMap) <- case utxosE of
    Left err -> error $ "Error getting utxos: " ++ show err
    Right utxos -> return utxos

  let utxoList = Map.toList utxoMap
      addrValueMap =
        foldl
          ( \newMap utxo@(_, TxOut aie (TxOutValue _ newValue) _ _) ->
              let addr = toShelleyAddr aie
               in case Map.lookup addr newMap of
                    Nothing -> Map.insert addr newValue newMap
                    Just existingValue -> Map.insert addr (existingValue <> newValue) newMap
          )
          Map.empty
          utxoList

      walletsAddrsInShelley = map (\s -> skeyToAddrInEra s (getNetworkId dcInfo)) wallets
      walletsWithNoUtxos = filter (\addr -> isNothing $ Map.lookup (toShelleyAddr addr) addrValueMap) walletsAddrsInShelley
      balancesWithLess = Map.filter (\v -> not $ v `valueGte` valueFromList [(AdaAssetId, Quantity 20_000_000)]) addrValueMap
      balancesWithLessAddrs = walletsWithNoUtxos <> map (\(Shelley.Addr nw pc scr, _) -> shelleyAddressInEra $ ShelleyAddress nw pc scr) (Map.toList balancesWithLess)

  if not (null balancesWithLessAddrs)
    then do
      putStrLn "Wallets with not enough value in them\n"
      print $ map (\a -> show (serialiseAddress a) ++ "0 Ada") balancesWithLessAddrs
      prettyPrintBalances balancesWithLess
      --TODO Already split the utxo into chunks of main wallet
      let walletAddrsChunks = chunksOf 100 balancesWithLessAddrs
      mapM_
        ( \walletChunk -> do
            putStrLn $ "Funding wallet chunk " ++ show (length walletChunk)
            fundWallets dcInfo walletChunk fundedSignKey
        )
        walletAddrsChunks
      print "Wallet funding completed."
    else print "All wallets have enough value."
  where
    fundWallets :: ChainInfo v => v -> [AddressInEra BabbageEra] -> SigningKey PaymentKey -> IO ()
    fundWallets dcInfo walletAddrs fundedSignKey = do
      let fundAddr = getAddrEraFromSignKey dcInfo fundedSignKey
          utxoValue = valueFromList [(AdaAssetId, Quantity 100_000_000)]
          addressesWithValue = map (,utxoValue) walletAddrs
          hundredAdaPayOperation = foldMap (uncurry txPayTo) addressesWithValue
          txOperations = hundredAdaPayOperation <> txWalletAddress fundAddr
      txBodyE <- txBuilderToTxBodyIO dcInfo txOperations
      txBody <- case txBodyE of
        Left err -> error $ "Error building tx: " ++ show err
        Right txBody -> return txBody
      tx <- signAndSubmitTxBody (getConnectInfo dcInfo) txBody [fundedSignKey]
      let txHash = getTxId $ getTxBody tx
      putStrLn $ "\nSubmitted successfully TxHash " ++ show txHash
      let firstAddrAny = getAddrAnyFromEra $ fst $ head addressesWithValue
      putStrLn "Wait for funds to appear on wallet."
      pollForTxId dcInfo firstAddrAny txHash

queryParallelTest dcInfo wallets = do
  forConcurrently_ wallets $ \wallet -> do
    let addrEra = getAddrEraFromSignKey dcInfo wallet
        addrAny = getAddrAnyFromEra addrEra
    utxos@(UTxO utxoMap) <- loopedQueryUtxos dcInfo addrAny
    printUtxos utxos addrEra


transferTestOfWallets dcInfo wallets = do
  forConcurrently_ wallets $ \wallet -> do
    let addrEra = getAddrEraFromSignKey dcInfo wallet
        addrAny = getAddrAnyFromEra addrEra
    print "Done"
    transferTestOfWallet dcInfo wallet addrEra addrAny

transferTestOfWallet ctx signKey addrEra addrAny = do
  let balance = lovelaceToValue $ Lovelace 5_000_000
      payOperations = txPayTo addrEra balance
      txOperations = payOperations
          <> txWalletAddress addrEra
  txBodyE <- loopedTxBuilderToTxBodyIo txOperations
  txBody <- case txBodyE of
    Left fe -> error $ "Error: " ++ show fe
    Right txBody -> pure txBody
  tx <- loopedSubmitTx txBody
  let txId = getTxId txBody
  putStrLn $ "Wait merge utxos to appear on wallet TxId: " ++ show txId
  pollForTxId ctx addrAny txId
  putStrLn "Wallet utxo merge completed."
  where
    loopedTxBuilderToTxBodyIo txOperations = do
      result <- try (txBuilderToTxBodyIO ctx txOperations ) :: IO (Either SomeException (Either FrameworkError (TxBody BabbageEra)))
      case result of
        Left any -> do
          print any
          loopedTxBuilderToTxBodyIo txOperations
        Right tx -> pure tx

    loopedSubmitTx txBody = do
      result <- try (signAndSubmitTxBody (getConnectInfo ctx) txBody [signKey] ) :: IO (Either SomeException (Tx BabbageEra))
      case result of
        Left any -> do
          print any
          loopedSubmitTx txBody
        Right tx -> pure tx
