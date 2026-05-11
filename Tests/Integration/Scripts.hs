module Tests.Integration.Scripts (run) where

import Tests.Harness
import Utils.Server (runProofScript)
import SessionTypes.Tactics (ProofState(..))
import Data.IORef
import Control.Exception (try, SomeException)

-- Run a proof script from an inline string using a synthetic filename
runInline :: String -> String -> IO (Either String ProofState)
runInline label content = runProofScript ("<test:" ++ label ++ ">") content

-- Assert the script succeeds with no errors and all theorems complete
assertProves :: IORef TestState -> String -> String -> IO ()
assertProves ref label content = do
    result <- runInline label content
    case result of
        Left err ->
            assert ref (label ++ " [parse/run error: " ++ err ++ "]") False
        Right ps ->
            if not (null (errors ps))
                then assert ref (label ++ " [proof errors: " ++ show (errors ps) ++ "]") False
                else assert ref label True

-- Assert the script fails (either parse error or proof errors)
assertFails :: IORef TestState -> String -> String -> IO ()
assertFails ref label content = do
    result <- runInline label content
    case result of
        Left _   -> assert ref label True  -- parse failure counts as failure
        Right ps -> assert ref label (not (null (errors ps)))

-- Run an existing .still file and assert it succeeds
runFileTest :: IORef TestState -> FilePath -> IO ()
runFileTest ref path = do
    result <- try (do
        content <- readFile path
        runProofScript path content) :: IO (Either SomeException (Either String ProofState))
    case result of
        Left ex  ->
            assert ref (path ++ " [exception: " ++ show ex ++ "]") False
        Right (Left err) ->
            assert ref (path ++ " [parse error: " ++ err ++ "]") False
        Right (Right ps) ->
            if not (null (errors ps))
                then assert ref (path ++ " [proof errors: " ++ unlines (errors ps) ++ "]") False
                else assert ref path True

run :: IORef TestState -> IO ()
run ref = group ref "Integration.runProofScript" $ do

    -- ===== Valid proofs =====

    assertProves ref "Unit right rule" $ unlines
        [ "module T begin"
        , "theorem unit: \"1\""
        , "apply UnitR"
        , "done"
        ]

    assertProves ref "Identity axiom (forall A:stype. A -o A)" $ unlines
        [ "module T begin"
        , "theorem identity: \"forall A:stype. A -o A\""
        , "apply Forall2R"
        , "apply ImpliesR"
        , "apply IdA"
        , "done"
        ]

    assertProves ref "Implication introduction (1 -o 1)" $ unlines
        [ "module T begin"
        , "theorem imp: \"1 -o 1\""
        , "apply ImpliesR"
        , "apply UnitLA"
        , "apply UnitR"
        , "done"
        ]

    assertProves ref "Tensor commutativity (forall A:stype. forall B:stype. A * B -o B * A)" $ unlines
        [ "module T begin"
        , "theorem comm: \"forall A:stype. forall B:stype. A * B -o B * A\""
        , "apply Intros"
        , "apply TensorLA"
        , "apply TensorR"
        , "apply IdA"
        , "apply IdA"
        , "done"
        ]

    assertProves ref "With commutativity (forall A:stype. forall B:stype. A & B -o B & A)" $ unlines
        [ "module T begin"
        , "theorem wcomm: \"forall A:stype. forall B:stype. A & B -o B & A\""
        , "apply Intros"
        , "apply WithR"
        , "apply WithL1A"
        , "apply IdA"
        , "apply WithL2A"
        , "apply IdA"
        , "done"
        ]

    assertProves ref "Replication right (!1)" $ unlines
        [ "module T begin"
        , "theorem bang: \"!1\""
        , "apply BangR"
        , "apply UnitR"
        , "done"
        ]

    assertProves ref "Forall intro (forall x:Int.1)" $ unlines
        [ "module T begin"
        , "theorem fq: \"forall x:Int.1\""
        , "apply ForallR"
        , "apply UnitR"
        , "done"
        ]

    -- Intros strips all Forall2 and Implication binders in sequence
    assertProves ref "Intros shorthand (1 -o 1)" $ unlines
        [ "module T begin"
        , "theorem intros_test: \"1 -o 1\""
        , "apply Intros"
        , "apply UnitLA"
        , "apply UnitR"
        , "done"
        ]

    assertProves ref "stype declaration then use" $ unlines
        [ "module T begin"
        , "stype MyT = \"1 -o 1\""
        , "theorem use_stype: \"MyT\""
        , "apply ImpliesR"
        , "apply UnitLA"
        , "apply UnitR"
        , "done"
        ]

    assertProves ref "Multiple theorems in one module" $ unlines
        [ "module T begin"
        , "theorem t1: \"1\""
        , "apply UnitR"
        , "done"
        , "theorem t2: \"1 -o 1\""
        , "apply ImpliesR"
        , "apply UnitLA"
        , "apply UnitR"
        , "done"
        ]

    assertProves ref "CutTheorem: second theorem uses first" $ unlines
        [ "module T begin"
        , "theorem base: \"1\""
        , "apply UnitR"
        , "done"
        , "theorem cut_test: \"1\""
        , "apply CutTheorem base"
        , "apply UnitLA"
        , "apply UnitR"
        , "done"
        ]

    assertProves ref "Plus right injection (PlusR1)" $ unlines
        [ "module T begin"
        , "theorem plus1: \"forall A:stype. 1 + A\""
        , "apply Forall2R"
        , "apply PlusR1"
        , "apply UnitR"
        , "done"
        ]

    assertProves ref "Plus right injection (PlusR2)" $ unlines
        [ "module T begin"
        , "theorem plus2: \"forall A:stype. A + 1\""
        , "apply Forall2R"
        , "apply PlusR2"
        , "apply UnitR"
        , "done"
        ]

    -- Note: !A -o A requires BangLA then Copy (moves to unrestricted context);
    -- channel name is auto-generated and unpredictable, so covered by file-based tests.

    assertProves ref "Second-order forall (forall X:stype.X -o X)" $ unlines
        [ "module T begin"
        , "theorem forall2: \"forall X:stype.X -o X\""
        , "apply Forall2R"
        , "apply ImpliesR"
        , "apply IdA"
        , "done"
        ]

    -- ===== Invalid proofs (should fail) =====

    assertFails ref "UnitR applied to implication goal" $ unlines
        [ "module T begin"
        , "theorem bad: \"1 -o 1\""
        , "apply UnitR"
        , "done"
        ]

    assertFails ref "done before proof is complete" $ unlines
        [ "module T begin"
        , "theorem bad: \"1 -o 1\""
        , "done"
        ]

    assertFails ref "IdA without matching channel in context" $ unlines
        [ "module T begin"
        , "theorem bad: \"forall A:stype. forall B:stype. A -o B\""
        , "apply Forall2R"
        , "apply Forall2R"
        , "apply ImpliesR"
        , "apply IdA"
        , "done"
        ]

    assertFails ref "Free type variable in theorem is rejected" $ unlines
        [ "module T begin"
        , "theorem bad: \"A -o A\""
        , "done"
        ]

    assertFails ref "CutTheorem referencing undefined theorem" $ unlines
        [ "module T begin"
        , "theorem bad: \"1\""
        , "apply CutTheorem undefinedTheorem"
        , "done"
        ]

    assertFails ref "Malformed proposition in theorem statement" $ unlines
        [ "module T begin"
        , "theorem bad: \"-o -o\""
        , "done"
        ]

    assertFails ref "PlusR1 applied to non-Plus goal" $ unlines
        [ "module T begin"
        , "theorem bad: \"1\""
        , "apply PlusR1"
        , "done"
        ]

    assertFails ref "BangR applied to non-Replication goal" $ unlines
        [ "module T begin"
        , "theorem bad: \"1\""
        , "apply BangR"
        , "done"
        ]

    -- ===== Well-formedness: coinductive type checks =====

    assertFails ref "nu x. 1 does not mention x (non-recursive nu)" $ unlines
        [ "module T begin"
        , "theorem bad: \"nu x. 1\""
        , "done"
        ]

    assertFails ref "nu x. x is not a productive coinductive type" $ unlines
        [ "module T begin"
        , "theorem bad: \"nu x. x\""
        , "done"
        ]

    assertProves ref "nu X. 1 -o X is a valid coinductive type" $ unlines
        [ "module T begin"
        , "stype S = \"nu X. 1 -o X\""
        , "theorem wf: \"1\""
        , "apply UnitR"
        , "done"
        ]

    -- ===== File-based integration tests =====

    runFileTest ref "Proofs/TestingFiles/Scratch.still"
    runFileTest ref "Proofs/AdditionalProofs/Commutative.still"
    runFileTest ref "Proofs/AdditionalProofs/ServerClient.still"
    runFileTest ref "Proofs/AdditionalProofs/Semaphore.still"
    runFileTest ref "Proofs/AdditionalProofs/SNat.still"
    runFileTest ref "Proofs/AdditionalProofs/AxiomOfChoice.still"
