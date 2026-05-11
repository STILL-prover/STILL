#!/usr/bin/env bash
# run-tests.sh — compile and run the STILL test suite
# Usage: bash run-tests.sh

set -e

echo "Compiling test suite..."
ghc -threaded -O1 Tests/Main.hs -o still-tests
echo "Running tests..."
./still-tests
