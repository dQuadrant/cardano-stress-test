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

module Utils where

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
    valueToLovelace, CtxUTxO, txOutValueToValue, serialiseToRawBytesHexText,
    Tx, TxBody
  )
import Cardano.Api.Shelley (Address (ShelleyAddress), Lovelace (Lovelace), Quantity (Quantity), fromPlutusData, toShelleyAddr)
import Cardano.Kuber.Api
import Cardano.Kuber.Data.Parsers (parseAssetId, parseAssetIdText, parseAssetNQuantity, parseScriptData)
import Cardano.Kuber.Util (addrInEraToPkh, getDefaultSignKey, queryUtxos, readSignKey, skeyToAddr, skeyToAddrInEra)
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
import PlutusTx (Data (Map), toData)
import PlutusTx.Prelude (divide)
import System.Clock
import System.Directory (doesFileExist)
import System.Environment (getArgs, getEnv)
import System.IO (BufferMode (NoBuffering), IOMode (ReadMode), hFlush, hGetContents, hSetBuffering, openFile)
import System.Random (newStdGen)
import System.Random.Shuffle (shuffle')
import Text.Read (readMaybe)


readWalletsFromFile :: Int -> IO [SigningKey PaymentKey]
readWalletsFromFile noOfWallets = do
  readHandle <- openFile "1000-wallets.txt" ReadMode
  content <- hGetContents readHandle
  let linesOfFile = lines content
      walletStrs = take noOfWallets linesOfFile
  mapM parseSigningKey walletStrs

getVasilChainInfo :: IO DetailedChainInfo
getVasilChainInfo = do
  sockEnv <- try $ getEnv "CARDANO_NODE_SOCKET_PATH"
  socketPath <- case sockEnv of
    Left (e::SomeException) -> error "Socket File is Missing: Set environment variable CARDANO_NODE_SOCKET_PATH"
    Right s -> pure s
  let networkId = Testnet (NetworkMagic 9)
      connectInfo = ChainConnectInfo $ localNodeConnInfo networkId socketPath
  withDetails connectInfo

valueGte :: Value -> Value -> Bool
valueGte _vg _vl = not $ any (\(aid, Quantity q) -> q > lookup aid) (valueToList _vl) -- do we find anything that's greater than q
  where
    lookup x = case Map.lookup x v2Map of
      Nothing -> 0
      Just (Quantity v) -> v
    v2Map = Map.fromList $ valueToList _vg

--Convert to Addr any from Addr in era
getAddrAnyFromEra addrEra = fromMaybe (error "unexpected error converting address to another type") (deserialiseAddress AsAddressAny (serialiseAddress addrEra))

--Get Addr any from given sign key
getAddrAnyFromSignKey ctx signKey =
  getAddrAnyFromEra $ skeyToAddrInEra signKey (getNetworkId ctx)

--Get Addr in era from  given sign key
getAddrEraFromSignKey ctx signKey =
  skeyToAddrInEra signKey (getNetworkId ctx)

parseSigningKey :: String -> IO (SigningKey PaymentKey)
parseSigningKey sKeyStr = do
  let skeyBs = T.encodeUtf8 $ T.pack sKeyStr
  case deserialiseFromRawBytes (AsSigningKey AsPaymentKey) skeyBs of
    Nothing -> error "Error parsing signing key: "
    Just skey -> return skey

pollForTxId ctx addrAny txHash = do
  threadDelay 1000000
  utxos@(UTxO utxoMap) <- loopedQueryUtxos ctx addrAny
  putStr "."
  let txIdsKey = map (\(TxIn txId _) -> txId) $ Map.keys utxoMap
  if txHash `elem` txIdsKey
    then putStrLn "\nFunds Transferred successfully."
    else pollForTxId ctx addrAny txHash

loopedQueryUtxos :: ChainInfo v => v -> AddressAny -> IO (UTxO BabbageEra)
loopedQueryUtxos ctx addrAny = do
  result <- try (queryUtxos (getConnectInfo ctx) $ Set.singleton addrAny) :: IO (Either SomeException (Either FrameworkError (UTxO BabbageEra)))
  case result of
    Left any -> loopedQueryUtxos ctx addrAny
    Right utxosE -> case utxosE of
      Left err -> do
        putStrLn $ "Loope error on querying utxos: " <> show err
        print err
        loopedQueryUtxos ctx addrAny
      Right utxos -> return utxos

prettyPrintBalances balances = do
  forM_ (Map.toList balances) $ \(Shelley.Addr _ s _, value) -> do
    TIO.putStrLn $ T.pack (show s) <> ": " <> renderValue value

renderValue :: Value -> Text
renderValue v =
  T.intercalate
    "+"
    (map renderAsset $ valueToList v)

renderAsset :: (AssetId, Quantity) -> Text
renderAsset (ass, q) = T.pack $ case ass of
  AdaAssetId -> renderAda q
  AssetId p n -> show q ++ " " ++ showStr p ++ "." ++ showStr n

renderAda :: Quantity -> String
renderAda (Quantity q) = show ((fromIntegral q :: Double) / 1e6) ++ "Ada"


showStr :: Show a => a -> [Char]
showStr x = init $ tail $ show x

printUtxoOfWallets ctx wallets = do
  forM_ wallets $ \wallet -> printUtxoOfWallet ctx wallet

--Print all utxos of given wallet
printUtxoOfWallet :: ChainInfo v => v -> SigningKey PaymentKey -> IO ()
printUtxoOfWallet ctx wallet = do
  utxos@(UTxO utxoMap) <- getUtxosOfWallet ctx wallet
  let addrEra = getAddrEraFromSignKey ctx wallet
  printUtxos utxos addrEra

printUtxos :: UTxO BabbageEra -> AddressInEra BabbageEra -> IO ()
printUtxos utxos@(UTxO utxoMap) addr = do
  putStrLn $ "\n\nUtxos of address " <> T.unpack (serialiseAddress addr) <> " Count: " <> show (Map.size utxoMap)
  forM_ (Map.toList utxoMap) $ \(txIn, txOut) -> do
    TIO.putStrLn $ " " <> renderTxIn txIn <> ": " <> renderTxOut txOut

-- Pack the txIn in text format with # separated
renderTxIn :: TxIn -> Text
renderTxIn (TxIn txId (TxIx ix)) =
  serialiseToRawBytesHexText txId <> "#" <> T.pack (show ix)

renderTxOut :: TxOut CtxUTxO BabbageEra -> Text
renderTxOut (TxOut _ txOutValue _ _) = do
  let value = txOutValueToValue txOutValue
  renderValue value

getUtxosOfWallet ::
  ChainInfo v => v ->
  SigningKey PaymentKey ->
  IO (UTxO BabbageEra)
getUtxosOfWallet ctx wallet = do
  let addrAny = getAddrAnyFromSignKey ctx wallet
  loopedQueryUtxos ctx addrAny

signAndSubmitTxBody :: LocalNodeConnectInfo CardanoMode
  -> TxBody BabbageEra -> [SigningKey PaymentKey] -> IO (Tx BabbageEra)
signAndSubmitTxBody ctx txBody signKeys = do
  let tx = signTxBody txBody signKeys
  res <- submitTx ctx tx
  case res of
    Left err -> error $ "Error: " ++ show err
    Right _ -> pure tx
