-- End-to-end tests of the built prover binary: exit status and which stream
-- each kind of output goes to. These need ./still (or still.exe) to have been
-- compiled in the repository root first; run-tests.sh does that.
module Tests.Cli.ExitCodeSpec (run) where

import Control.Monad (filterM)
import Data.IORef
import Data.List (isInfixOf, isPrefixOf)
import System.Directory (doesFileExist)
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)
import Tests.Harness

run :: IORef TestState -> IO ()
run ref = group ref "Cli.ExitCode" $ do
    found <- filterM doesFileExist ["./still", "./still.exe"]
    case found of
        [] -> assert ref "prover binary present (build it with: ghc -threaded -O2 Main.hs -o still)" False
        (exe : _) -> do
            let still args = readProcessWithExitCode exe args ""
                passing    = "Tests/Fixtures/Passing.still"
                failing    = "Tests/Fixtures/Failing.still"
                incomplete = "Tests/Fixtures/Incomplete.still"
                missing    = "Tests/Fixtures/DoesNotExist.still"

            -- ===== script mode =====

            (c1, o1, _) <- still [passing]
            assertEqual ref "script mode: passing script exits 0" ExitSuccess c1
            assert ref "script mode: passing script announces the file"
                (("Running: " ++ passing) `isInfixOf` o1)

            (c2, o2, _) <- still [failing]
            assertEqual ref "script mode: failing tactic exits 1" (ExitFailure 1) c2
            assert ref "script mode: failing tactic prints an Errors section" ("Errors:" `isInfixOf` o2)

            (c3, o3, _) <- still [incomplete]
            assertEqual ref "script mode: incomplete proof exits 1" (ExitFailure 1) c3
            assert ref "script mode: incomplete proof is named" ("incomplete" `isInfixOf` o3)

            (c4, o4, _) <- still [missing]
            assertEqual ref "script mode: missing file exits 1" (ExitFailure 1) c4
            assert ref "script mode: missing file is reported" ("file not found" `isInfixOf` o4)

            (c5, o5, _) <- still [passing, failing]
            assertEqual ref "script mode: one failure among several files exits 1" (ExitFailure 1) c5
            assert ref "script mode: all files still run after a failure"
                (("Running: " ++ passing) `isInfixOf` o5 && ("Running: " ++ failing) `isInfixOf` o5)

            -- ===== benchmark mode =====

            (b1, bo1, be1) <- still ["benchmark", passing]
            assertEqual ref "benchmark: passing script exits 0" ExitSuccess b1
            assert ref "benchmark: stdout starts with the table header" ("Module" `isPrefixOf` bo1)
            assertEqual ref "benchmark: stderr is empty for a passing script" "" be1
            assert ref "benchmark: stdout has no escape codes" (notElem '\ESC' bo1)
            assertEqual ref "benchmark: stdout is exactly header, separator, one row"
                3 (length (lines bo1))

            (b2, bo2, be2) <- still ["benchmark", failing, missing]
            assertEqual ref "benchmark: failures exit 1" (ExitFailure 1) b2
            assert ref "benchmark: problems go to stderr, prefixed by file name"
                ((failing ++ ":") `isInfixOf` be2 && "file not found" `isInfixOf` be2)
            assert ref "benchmark: stdout is still only the table"
                ("Module" `isPrefixOf` bo2 && not ("Could not" `isInfixOf` bo2) && length (lines bo2) == 4)
