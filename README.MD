Cardano Stress test for testing node query handling state

**How to run**

1. Place 1000-wallets.txt containg signing key of 1000 wallets in current directory

2. Place default signkey on ~/.cardano/default.skey

3. Run the project using cabal run command
```
cabal run stress-test 1000
