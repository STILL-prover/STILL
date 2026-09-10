module Tests.Cli.RunnerSpec (run) where

import Data.IORef
import Data.List (isInfixOf, isPrefixOf)
import Tests.Harness
import Utils.Runner

run :: IORef TestState -> IO ()
run ref = group ref "Cli.Runner" $ do

    -- ===== runScriptFile =====

    ok <- runScriptFile "Tests/Fixtures/Passing.still"
    assert ref "passing script: scriptOk" (scriptOk ok)
    assertEqual ref "passing script: no problems" [] (scriptProblems ok)
    assert ref "passing script: output records the completed theorem"
        ("Theorem complete: swap" `isInfixOf` scriptOutput ok)

    bad <- runScriptFile "Tests/Fixtures/Failing.still"
    assert ref "failing tactic: not scriptOk" (not (scriptOk bad))
    assert ref "failing tactic: tactic error is reported"
        (any ("Could not find" `isInfixOf`) (scriptProblems bad))
    assert ref "failing tactic: unfinished theorem is reported"
        (any ("incomplete" `isInfixOf`) (scriptProblems bad))

    inc <- runScriptFile "Tests/Fixtures/Incomplete.still"
    assert ref "incomplete proof: not scriptOk" (not (scriptOk inc))
    assertEqual ref "incomplete proof: exactly one problem, naming the theorem"
        ["Proof of theorem 'unfinished' is incomplete (missing 'done')."]
        (scriptProblems inc)

    unp <- runScriptFile "Tests/Fixtures/Unparseable.still"
    assert ref "unparseable script: not scriptOk" (not (scriptOk unp))
    assert ref "unparseable script: parse error is reported"
        (any ("Parse Error" `isInfixOf`) (scriptProblems unp))

    missing <- runScriptFile "Tests/Fixtures/DoesNotExist.still"
    assert ref "missing file: not scriptOk" (not (scriptOk missing))
    assertEqual ref "missing file: reported as such"
        ["file not found: Tests/Fixtures/DoesNotExist.still"] (scriptProblems missing)

    -- ===== benchmarkFile =====

    (dOk, pOk) <- benchmarkFile 2 "Tests/Fixtures/Passing.still"
    assert ref "benchmark passing: didError is False" (not (didError dOk))
    assertEqual ref "benchmark passing: no problems" [] pOk
    assertEqual ref "benchmark passing: module name" "Passing" (moduleName dOk)
    assertEqual ref "benchmark passing: theorem count" "1" (numTheorems dOk)
    assert ref "benchmark passing: min <= avg <= max time"
        (minExecutionTime dOk <= executionTime dOk && executionTime dOk <= maxExecutionTime dOk)

    (dBad, pBad) <- benchmarkFile 1 "Tests/Fixtures/Failing.still"
    assert ref "benchmark failing tactic: didError is True" (didError dBad)
    assert ref "benchmark failing tactic: problems reported" (not (null pBad))

    (dInc, _) <- benchmarkFile 1 "Tests/Fixtures/Incomplete.still"
    assert ref "benchmark incomplete proof: didError is True" (didError dInc)

    (dMissing, pMissing) <- benchmarkFile 1 "Tests/Fixtures/DoesNotExist.still"
    assert ref "benchmark missing file: didError is True" (didError dMissing)
    assertEqual ref "benchmark missing file: N/A counts" "N/A" (numTheorems dMissing)
    assert ref "benchmark missing file: problem reported"
        (any ("file not found" `isInfixOf`) pMissing)

    -- ===== renderResultsTable =====

    let table = renderResultsTable [dOk, dMissing]
        tableLines = lines table
    assert ref "table: header row first" ("Module" `isPrefixOf` head tableLines)
    assertEqual ref "table: header, separator, one row per module" 4 (length tableLines)
    assert ref "table: no terminal escape codes" (notElem '\ESC' table)
    assert ref "table: contains the passing module row"
        (any (\l -> "Passing" `isPrefixOf` l) tableLines)
    assert ref "table: columns aligned (every row has the same width)"
        (all ((== length (head tableLines)) . length) tableLines)
