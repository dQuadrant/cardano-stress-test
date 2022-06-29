Cardano Stress test for testing node query handling state

**How to run**

Place 1000-wallets.txt containg signing key of 1000 wallets in current directory and place default signkey on ~/.cardano/default.skey

```
cabal run stress-test 1000
