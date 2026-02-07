# Running STILL

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

Proof modules use the ```.still``` extension. Modules must begin with a module
declaration that includes any optional imports

```module ModuleName \[imports Name1 Name2 ...\] begin```

After the module declaration you may start a theorem with the theorem command.
The proposition of the theorem must be wrapped in quotes.

```theorem TheoremName: "proposition"```

After a theorem is started you can start proving it using the proving commands.
The ```apply``` command must be followed by a tactic expression. Use ```defer```
to move the current subgoal to the end.

# Compiling

1. Use ghcup to install ghc 9.6.7
2. ghc Main.hs -o still
3. Run with ./still (still.exe on Windows)

# License

Code in a subdirectory (and subdirectories below that) is redistributed
according to the license for that code provided in the same subdirectory e.g.
Parsec code is redistributed according to the license that can be found in the
Text subdirectory of the repository. All other code is provided according to the
license in the root directory of the repository.
