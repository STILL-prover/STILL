# Running STILL

The one liner for benchmarking using Docker is ```docker run $(docker build -q .)```

You can also run the REPL with ```docker run -it $(docker build -q .) repl```

See the compiling section if you don't have docker installed.

The still prover has three modes:

1. repl
    - ```./still repl```
2. file watch
    - ```./still watch FILE_PATH```
3. proof execution
    - ```./still [FILE_PATH ...]```
    - ```./still benchmark [FILE_PATH ...]```

The proof execution mode accepts multiple files as arguments. Each file
is ran as a standalone script and doesn't affect the execution of the other scripts.

# Writing Proofs

Example modules can be found in the Proofs folder. 
Proof modules use the ```.still``` extension. Modules must begin with a module
declaration that includes any optional imports

```module ModuleName \[imports Name1 Name2 ...\] begin```

After the module declaration you may start a theorem with the theorem command.
The proposition of the theorem must be wrapped in quotes.

```theorem TheoremName: "proposition"```

After a theorem is started you can start proving it using the proving commands.
The ```apply``` command must be followed by a tactic expression. Use ```defer```
to move the current subgoal to the end.

See Tactics.md for the tactics in the system. See Syntax.md for tactic expressions.

# Compiling

1. Use ghcup or another method to install ghc 9.6.7 (https://www.haskell.org/ghcup/)
2. Run ```ghc -threaded -O2 Main.hs -o still``` in this folder
3. Run the prover with ```./still``` (still.exe on Windows).
  - See above for the different modes.

## Docker compiling and running

1. Install docker
2. Navigate to the code repository
3. Run ```docker build --tag still .```
4. To run the prover ```docker run still```

# Additional Information

Benchmarking commands:

- ```./still benchmarking ./Proofs/*.still```
- ```./still benchmarking ./Proofs/StressTestTensors/*.still```
- ```./still benchmarking ./Proofs/AdditionalProofs/*.still```

If your system doesn't support file globbing, then manually enter the file names like so:

```./still benchmarking ./Proofs/Auction.still ./Proofs/Bank.still ./Proofs/CloudServer.still ./Proofs/Commutative.still ./Proofs/Counter.still ./Proofs/LargeMul.still```

The ./Proofs/AdditionalProofs directory holds some other interesting test scripts. The ./Proofs/StressTestTensors directory holds the files for stress testing the resource hiding algorithm with large tensor proofs.

# License

Code in a subdirectory (and subdirectories below that) is redistributed
according to the license for that code provided in the same subdirectory e.g.
Parsec code is redistributed according to the license that can be found in the
Text subdirectory of the repository. All other code is provided according to the
license in the root directory of the repository.
