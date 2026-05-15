module Tests.SessionTypes.CommittedVarsSpec (run) where

import Tests.Harness
import SessionTypes.Tactics
import Utils.Display (showFiltered, ansiRed)
import Utils.Server (runProofScript)
import SessionTypes.Kernel (Sequent (..), Proposition (..), Context, propToS, linearContext)
import ECC.Kernel (emptyContext)
import qualified Data.Set as DS
import qualified Data.Map as Map
import Data.List (isInfixOf)
import Data.IORef

-- Minimal sequent: no contexts, Unit goal on channel "z".
emptySeq :: Sequent
emptySeq = Sequent
    { tyVarContext       = DS.empty
    , fnContext          = emptyContext
    , unrestrictedContext = Map.empty
    , linearContext      = Map.empty
    , recursiveBindings  = Map.empty
    , channel            = "z"
    , goalProposition    = Unit
    }

-- A minimal root subgoal wrapping the given sequent.
rootSubgoal :: Sequent -> Subgoal
rootSubgoal seq = initializeProof seq

-- A minimal ProofState containing a single named root subgoal.
singletonPS :: String -> Subgoal -> ProofState
singletonPS name sg = S
    { subgoals             = Map.singleton name sg
    , outputs              = []
    , curTheoremName       = "test"
    , curModuleName        = "T"
    , theorems             = Map.empty
    , loadedModules        = Map.empty
    , openGoalStack        = [name]
    , cachedProofStateNames = DS.empty
    , newSubgoalNameList   = allSubgoalNames
    , cachedVarNames       = []
    , stypeDecls           = []
    , fnAssumptions        = emptyContext
    , procAssumptions      = []
    , errors               = []
    , stypeAssumptions     = []
    }

run :: IORef TestState -> IO ()
run ref = do

    group ref "SessionTypes.getContextAvailability" $ do

        -- Root subgoal with no reservedVars: both sets empty.
        let ps0 = singletonPS "?a" (rootSubgoal emptySeq)
        assertEqual ref "root, empty reservedVars: fst = empty"
            DS.empty
            (fst (getContextAvailability "?a" ps0))
        assertEqual ref "root, empty reservedVars: snd = empty"
            DS.empty
            (snd (getContextAvailability "?a" ps0))

        -- Root subgoal with reservedVars = {"x"}: snd = {"x"}, fst still empty.
        let sgWithReserved = (rootSubgoal emptySeq) { reservedVars = DS.singleton "x" }
            ps1 = singletonPS "?a" sgWithReserved
        assertEqual ref "root, reservedVars {x}: fst = empty"
            DS.empty
            (fst (getContextAvailability "?a" ps1))
        assertEqual ref "root, reservedVars {x}: snd = {x}"
            (DS.singleton "x")
            (snd (getContextAvailability "?a" ps1))

        -- Missing subgoal name: both sets empty.
        assertEqual ref "unknown subgoal name: both sets empty"
            (DS.empty, DS.empty)
            (getContextAvailability "?missing" ps0)

        -- Integration: after TensorR + IdA on first branch, second branch sees
        -- the first branch's consumed var as sibling-unavailable (fst non-empty).
        result <- runProofScript "<test:sibling-unavail>" $ unlines
            [ "module T begin"
            , "theorem t: \"forall A:stype. forall B:stype. A -o B -o A * B\""
            , "apply Intros"
            , "apply TensorR"
            , "apply IdA"
            ]
        case result of
            Left err ->
                assert ref ("TensorR/IdA proof step failed: " ++ err) False
            Right ps -> do
                let cur = curSubgoal ps
                let (unavail, _) = getContextAvailability cur ps
                assert ref "after TensorR + IdA: remaining subgoal has non-empty sibling-unavailable set"
                    (not (DS.null unavail))

        -- Regression: TensorLA reuses the variable name for one component, then TensorR
        -- splits. The reused name must NOT bleed into committedToThisBranch via the
        -- ancestor's reservedVars.
        resultTLATR <- runProofScript "<test:tensorla-then-tensorr>" $ unlines
            [ "module T begin"
            , "theorem t: \"forall A:stype. A * A -o A * A\""
            , "apply Intros"
            , "apply TensorLA"
            , "apply TensorR"
            ]
        case resultTLATR of
            Left err ->
                assert ref ("TensorLA/TensorR setup failed: " ++ err) False
            Right ps -> do
                let cur = curSubgoal ps
                let (_, committed) = getContextAvailability cur ps
                assert ref "after TensorLA + TensorR: committedToThisBranch is empty (no ancestor reservation bleeds in)"
                    (DS.null committed)
                assert ref "after TensorLA + TensorR: subgoal is in multiplicative context"
                    (isInMultiplicativeContext cur ps)
                -- Every variable in the linear context must appear RED in the display.
                let sg       = subgoals ps Map.! cur
                    (unavail, committed', multCtx) = getContextInfo cur ps
                    rendered = showFiltered (unavail, committed') multCtx sg
                    linVars  = Map.toList (linearContext (sequent sg))
                mapM_ (\(k, v) ->
                    assert ref ("after TensorLA + TensorR: " ++ k ++ " appears RED in display")
                        (ansiRed (k ++ ":" ++ propToS v) `isInfixOf` rendered)
                    ) linVars

    group ref "SessionTypes.isInMultiplicativeContext" $ do

        -- Root subgoal has no ancestor, so never in a multiplicative context.
        let ps0 = singletonPS "?a" (rootSubgoal emptySeq)
        assert ref "root: isInMultiplicativeContext = False"
            (not (isInMultiplicativeContext "?a" ps0))

        -- Unknown subgoal: not in multiplicative context.
        assert ref "unknown subgoal: isInMultiplicativeContext = False"
            (not (isInMultiplicativeContext "?missing" ps0))

        -- Integration: after TensorR (both siblings still open), the current
        -- subgoal IS in a multiplicative context.
        resultTR <- runProofScript "<test:mult-ctx-open>" $ unlines
            [ "module T begin"
            , "theorem t: \"forall A:stype. forall B:stype. A -o B -o A * B\""
            , "apply Intros"
            , "apply TensorR"
            ]
        case resultTR of
            Left err ->
                assert ref ("TensorR proof step failed: " ++ err) False
            Right ps ->
                assert ref "after TensorR: current subgoal is in multiplicative context (sibling still open)"
                    (isInMultiplicativeContext (curSubgoal ps) ps)

        -- Integration: after TensorR + IdA, the first sibling is closed so the
        -- remaining subgoal's sibling is gone — no longer in multiplicative context.
        resultTRIdA <- runProofScript "<test:mult-ctx-closed>" $ unlines
            [ "module T begin"
            , "theorem t: \"forall A:stype. forall B:stype. A -o B -o A * B\""
            , "apply Intros"
            , "apply TensorR"
            , "apply IdA"
            ]
        case resultTRIdA of
            Left err ->
                assert ref ("TensorR/IdA proof step failed: " ++ err) False
            Right ps ->
                assert ref "after TensorR + IdA: remaining subgoal no longer in multiplicative context (sibling closed)"
                    (not (isInMultiplicativeContext (curSubgoal ps) ps))

        -- Integration: sibling expanded into grandchildren.
        -- Outer TensorR on A*(B*C) creates ?z(B*C) [current] and ?y(A).
        -- Inner TensorR on ?z creates ?e(C) [current], ?d(B), leaving ?y still in stack.
        -- Two defers cycle past ?d and ?e, landing on ?y(A) as current.
        -- ?y's sibling ?z is expanded but has open descendants ?d and ?e, so
        -- isInMultiplicativeContext should still be True.
        resultNested <- runProofScript "<test:mult-ctx-grandchild>" $ unlines
            [ "module T begin"
            , "theorem t: \"forall A:stype. forall B:stype. forall C:stype. A -o B -o C -o A * (B * C)\""
            , "apply Intros"
            , "apply TensorR"   -- outer: current=?z(B*C), stack=[?z,?y(A)]
            , "apply TensorR"   -- inner on ?z: current=?e(C), stack=[?e,?d(B),?y]
            , "defer"           -- stack=[?d,?y,?e], current=?d
            , "defer"           -- stack=[?y,?e,?d], current=?y(A)
            ]
        case resultNested of
            Left err ->
                assert ref ("nested TensorR setup failed: " ++ err) False
            Right ps ->
                assert ref "sibling expanded into grandchildren: outer leaf still sees pending siblings"
                    (isInMultiplicativeContext (curSubgoal ps) ps)

    group ref "Utils.Display.showFiltered" $ do

        let linCtx = Map.fromList [("x", Unit), ("y", Unit)]
            seq'   = emptySeq { linearContext = linCtx }
            sg     = rootSubgoal seq'

        -- In multiplicative context (True): unassigned vars are RED.
        let renderedMult = showFiltered (DS.empty, DS.singleton "y") True sg
        assert ref "showFiltered (multCtx=True): unassigned var x is RED"
            (ansiRed "x:1" `isInfixOf` renderedMult)
        assert ref "showFiltered (multCtx=True): black var y is plain"
            (not (ansiRed "y:1" `isInfixOf` renderedMult))
        assert ref "showFiltered (multCtx=True): plain y:1 still present"
            ("y:1" `isInfixOf` renderedMult)

        -- Outside multiplicative context (False): unassigned vars are plain, not RED.
        let renderedTrunk = showFiltered (DS.empty, DS.singleton "y") False sg
        assert ref "showFiltered (multCtx=False): unassigned var x is plain, not RED"
            (not (ansiRed "x:1" `isInfixOf` renderedTrunk))
        assert ref "showFiltered (multCtx=False): x:1 still present"
            ("x:1" `isInfixOf` renderedTrunk)

        -- When all vars are in blackVars, none are RED regardless of context.
        let renderedAllBlack = showFiltered (DS.empty, DS.fromList ["x", "y"]) True sg
        assert ref "showFiltered (all black, multCtx=True): x:1 not RED"
            (not (ansiRed "x:1" `isInfixOf` renderedAllBlack))
        assert ref "showFiltered (all black, multCtx=True): x:1 still present"
            ("x:1" `isInfixOf` renderedAllBlack)
