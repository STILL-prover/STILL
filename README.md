# Running with ghci (Recommended)

1. Use ghcup to install ghc 9.6.7
2. Run ```ghci``` this loads the Main module. See .ghci for details.
3. Create a theorem with the theorem command ```:theorem "theorem_name" 1```
4. Apply a tactic E.g. ```:apply _UnitR```
5. Check the proof ```:done```
6. Extract the process ```:extract "theorem_name"```

You can also save your commands in a module and run the ```:load_module
path/to/module.txt``` command.

For a full list of commands use the ```:help_commands``` command. For a full
list of tactics use the ```:help_tactics``` and ```:help_functional_tactics``` commands.

# Compiling (Not supported at the moment)

1. Use ghcup to install ghc 9.6.7
2. ghc Main.hs -o tac
3. Run with ./tac

# License

Code in a subdirectory (and subdirectories below that) is redistributed
according to the license for that code provided in the same subdirectory e.g.
Parsec code is redistributed according to the license that can be found in the
Text subdirectory of the repository. All other code is provided according to the
license in the root directory of the repository.
