module Tests.SessionTypes.CommittedVarsSpec (run) where

import Tests.Harness
import SessionTypes.Tactics
import Utils.Display (showFiltered, ansiRed)
import Utils.Server (runProofScript)
import SessionTypes.Kernel (Sequent (..), Proposition (..), Context)
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

    group ref "Utils.Display.showFiltered" $ do

        -- showFiltered colours vars in the red set with ANSI escape codes,
        -- and leaves other vars plain.
        let linCtx = Map.fromList [("x", Unit), ("y", Unit)]
            seq'   = emptySeq { linearContext = linCtx }
            sg     = rootSubgoal seq'
            rendered = showFiltered (DS.empty, DS.singleton "y") sg

        assert ref "showFiltered: red var x contains ANSI red prefix"
            (ansiRed "x:1" `isInfixOf` rendered)
        assert ref "showFiltered: non-red var y does not have ANSI prefix"
            (not (ansiRed "y:1" `isInfixOf` rendered))
        assert ref "showFiltered: plain y:1 still present"
            ("y:1" `isInfixOf` rendered)

        -- With an full black set, no vars are coloured.
        let renderedNoRed = showFiltered (DS.empty, DS.fromList ["x", "y"]) sg
        assert ref "showFiltered (empty red set): x:1 plain"
            (not (ansiRed "x:1" `isInfixOf` renderedNoRed))
        assert ref "showFiltered (empty red set): x:1 still present"
            ("x:1" `isInfixOf` renderedNoRed)
