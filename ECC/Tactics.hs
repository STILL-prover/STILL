module ECC.Tactics where

import Data.Map
import qualified Data.Set as S
import qualified Control.Monad.State.Lazy as ST
import qualified Control.Monad.Trans.Except as E
import qualified Data.List as L
import Control.Monad (mplus)
import Text.Read (readMaybe)
import Data.Maybe (isJust, fromMaybe, isNothing)
import ECC.Kernel hiding (FunctionalSequent(functionalContext, goalType, goalTerm))
import qualified ECC.Kernel as FS (FunctionalSequent(..))
import Utils.Misc
import Debug.Trace
import Control.Monad.Identity ( Identity(runIdentity) )
import qualified Data.Map as M

data FunctionalTacticsSequent = FunctionalTacticsSequent {
    functionalContext :: FunctionalContext,
    goalTerm :: Maybe FunctionalTerm,
    goalType :: FunctionalTerm
} deriving (Eq)

ftseqToSHelper :: FunctionalTacticsSequent -> String
ftseqToSHelper seq = L.dropWhile (\c -> c == ',' || c == ' ') (L.foldl (\acc (k, v) -> acc ++ ", " ++ k ++ ":" ++ ftToS v) "" (ctxToList ((functionalContext seq)))) ++ --show (Data.Map.toList (FT.functionalContext seq)) ++
    " |- " ++ (case goalTerm seq of Just t -> ftToS t ; Nothing -> "□") ++ ":" ++ ftToS (goalType seq)

getFunctionalTacticsSequentNames :: FunctionalTacticsSequent -> S.Set String
getFunctionalTacticsSequentNames (FunctionalTacticsSequent fc gt gTy) = functionalNames gTy `S.union` maybe S.empty functionalNames gt `S.union` getFunctionalContextNames fc

data Subgoal = Subgoal {
    sequent :: FunctionalTacticsSequent,
    prevGoal :: String,
    nextGoals :: [String],
    subgoalJustification :: ProverState FunctionalProof,
    used :: Bool
} deriving ()

data ProofState = S {
    subgoals :: Map String Subgoal,
    curSubgoal :: String,
    usedSubgoalNames :: S.Set String,
    reservedVars :: S.Set String
} deriving ()

initializeProof :: FunctionalTacticsSequent -> Subgoal
initializeProof seq = Subgoal { sequent = seq, prevGoal = "", nextGoals = [], used = False, subgoalJustification = tacError "No justification." }

initializeState :: Subgoal -> S.Set String -> ProofState
initializeState goal additionalReservedVars =
    let
        fnVars = getFunctionalContextFreeNames . functionalContext . sequent $ goal
    in
        S { subgoals = singleton "?a" goal, curSubgoal = "?a", reservedVars = additionalReservedVars `S.union` fnVars, usedSubgoalNames = S.singleton "?a" }

type ProverStateT m a = ST.StateT ProofState (E.ExceptT String m) a

type ProverState a = ProverStateT Identity a

type Justification m = ProverState FunctionalProof

buildJustification0 :: FunctionalProof -> Justification m
buildJustification0 = return

buildJustification1 :: String -> (FunctionalProof -> FunctionalProof) -> Justification m
buildJustification1 sg p = do
    curSubgoals <- ST.gets subgoals
    case Data.Map.lookup sg curSubgoals of
        (Just sg) -> do
            jst <- subgoalJustification sg
            return $ p jst
        _ -> tacError $ "Child subgoal lost " ++ sg

buildJustification2 :: String -> String -> (FunctionalProof -> FunctionalProof -> FunctionalProof) -> Justification m
buildJustification2 sg1 sg2 p = do
    curSubgoals <- ST.gets subgoals
    case Data.Map.lookup sg1 curSubgoals of
        (Just sg) -> do
            jst <- subgoalJustification sg
            buildJustification1 sg2 (p jst)
        _ -> tacError $ "Child subgoal lost " ++ sg1

buildJustification3 :: String -> String -> String -> (FunctionalProof -> FunctionalProof -> FunctionalProof -> FunctionalProof) -> Justification m
buildJustification3 sg1 sg2 sg3 p = do
    curSubgoals <- ST.gets subgoals
    case Data.Map.lookup sg1 curSubgoals of
        (Just sg) -> do
            jst <- subgoalJustification sg
            buildJustification2 sg2 sg3 (p jst)
        _ -> tacError $ "Child subgoal lost " ++ sg1

instance Show (ProverStateT m FunctionalProof) where
     show :: ProverStateT m FunctionalProof -> String
     show j = "jstf in code"

-- -- data TacticRes = TacSuccess {
-- --     justification :: Justification
-- -- } deriving (Show)

type FunctionalTactic = ProverState String

tacError :: String -> ProverState a
tacError = ST.lift . E.throwE

liftMaybeWithError :: String -> Maybe a -> ProverState a
liftMaybeWithError err res = case res of
    Nothing -> tacError err
    Just x -> return x

allSubgoalNames :: [String]
allSubgoalNames = ('?' :) <$> namesInOrder

getFreshVar :: ProverState String
getFreshVar = do
    curSubgoals <- ST.gets subgoals
    uniqueNames <- reservedVars <$> ST.get
    let vars = S.unions (uniqueNames:(getFunctionalTacticsSequentNames . sequent <$> Data.Map.elems curSubgoals))
    let newVar = head $ Prelude.filter (\l -> not $ S.member l vars) namesInOrder
    ST.modify (\s -> s { reservedVars = S.insert newVar $ reservedVars s })
    return newVar

getFreshVarAttempt :: String -> ProverState String
getFreshVarAttempt z = do
    curSubgoals <- ST.gets subgoals
    uniqueNames <- reservedVars <$> ST.get
    let vars = S.unions (uniqueNames:(getFunctionalTacticsSequentNames . sequent <$> Data.Map.elems curSubgoals))
        zs = [z ++ show i | i <- numbers]
        newVar = head $ Prelude.filter (\l -> not $ S.member l vars) zs
    ST.modify (\s -> s { reservedVars = S.insert newVar $ reservedVars s })
    return newVar

getFreshSubgoalName :: ProverState String
getFreshSubgoalName = do
    curSubgoals <- ST.gets usedSubgoalNames
    let newSubgoalName = head $ Prelude.filter (\l -> not $ S.member l curSubgoals) allSubgoalNames
    ST.modify (\s -> s { usedSubgoalNames = S.insert newSubgoalName $ usedSubgoalNames s })
    return newSubgoalName

createNewSubgoal :: FunctionalTacticsSequent -> ProverState String
createNewSubgoal seq = do
    freshGoal <- getFreshSubgoalName
    curSubgoalName <- ST.gets curSubgoal
    let newSubgoal = Subgoal { sequent = seq, prevGoal = curSubgoalName, nextGoals = [], subgoalJustification = tacError "No justification", used = False }
    ST.modify (\s -> s { subgoals = Data.Map.insert freshGoal newSubgoal $ subgoals s })
    return freshGoal

getCurrentSequent :: ProverState FunctionalTacticsSequent
getCurrentSequent = do
    curSubgoalName <- ST.gets curSubgoal
    curSubgoalMaybe <- Data.Map.lookup curSubgoalName <$> ST.gets subgoals
    sequent <$> liftMaybeWithError ("Cannot find current subgoal " ++ curSubgoalName) curSubgoalMaybe

useCurrentSubgoal :: Justification m -> ProverState ()
useCurrentSubgoal j = do
    curState <- ST.get
    let curSubgoals = subgoals curState
        curSubgoalMaybe = Data.Map.lookup (curSubgoal curState) curSubgoals
    curSubgoalObj <- liftMaybeWithError ("Cannot find current subgoal " ++ curSubgoal curState) curSubgoalMaybe
    ST.modify (\s -> s { subgoals = Data.Map.insert (curSubgoal curState) (curSubgoalObj { subgoalJustification = j, used = True }) (subgoals s) })
    newSubgoals <- ST.gets subgoals
    let availableNextSubgoals = L.dropWhile (\(x, sg) -> used sg) $ Data.Map.toList newSubgoals
    if not (L.null availableNextSubgoals) then ST.modify (\s -> s { curSubgoal = fst . head $ availableNextSubgoals }) else ST.modify (\s -> s { curSubgoal = "" })

cTac :: FunctionalTactic
cTac = do
    seq <- getCurrentSequent
    let ctx = functionalContext seq
    case goalType seq of
        Type 0 -> do
                useCurrentSubgoal . buildJustification0 $ CRule ctx
                return "Ax tactic applied."
        _ -> tacError $ "EXPECTED: " ++ show (Type 0) ++ "\nRECEIVED: " ++ show (goalType seq)

tTac :: FunctionalTactic
tTac = do
    seq <- getCurrentSequent
    let ctx = functionalContext seq
    case goalType seq of
        (Type j) -> if isNothing (goalTerm seq) || goalTerm seq == Just (Type (j-1))
            then (do
                useCurrentSubgoal . buildJustification0 $ TRule (j - 1) ctx
                return "T tactic applied.")
            else tacError "Goal term is not valid. Should be type universe minus 1."
        _ -> tacError "Cannot apply to non-Type j goal."

-- wfTac :: FunctionalTactic
-- wfTac = do
--     seq <- getCurrentSequent
--     let ctx = functionalContext seq
--         p = extractProofFromTermUnderCtx ctx Prop
--     case (p, p >>= (`verifyFunctionalProofM` Data.Map.empty)) of
--         (Right pRes, Right (True, _)) -> do
--                 useCurrentSubgoal . buildJustification0 $ pRes
--                 return "WF tactic applied."
--         (Left e, _) -> tacError e
--         (_, Left e) -> tacError e

varTac :: String -> FunctionalTactic
varTac x = do
    seq <- getCurrentSequent
    let ctx = functionalContext seq
    case ctxLookup x ctx of
        Just xTy -> if xTy == goalType seq && (isNothing (goalTerm seq) || goalTerm seq == Just (Var x))
            then (do
                useCurrentSubgoal . buildJustification0 $ VarRule x ctx
                return "Var tactic applied.")
            else tacError $ "Cannot apply tactic. Goal term or type is mismatched.\nEXPECTED: " ++ maybe "" show (goalTerm seq) ++ show (goalType seq) ++ "\nRECEIVED: " ++ show xTy
        _ -> tacError $ "Cannot find " ++ x ++ " in the context."

varATac :: FunctionalTactic
varATac = do
    seq <- getCurrentSequent
    let ctx = functionalContext seq
    case goalTerm seq of
        Just (Var x) -> varTac x
        Nothing -> case L.filter (\(_, p) -> p == goalType seq) . ctxToList $ ctx of
            ((x,xTy):rest) -> varTac x
            _ -> tacError $ "Cannot find a variable with type " ++ show (goalType seq) ++ " in the context."

safeInsertTacHelper :: String -> FunctionalTerm -> FunctionalContext -> ProverState FunctionalContext
safeInsertTacHelper x a c = case safeInsert x a c of
    Right ctx -> return ctx
    Left e -> tacError e

pi1Tac :: Maybe FunctionalTerm -> FunctionalTactic
pi1Tac fa = do
    seq <- getCurrentSequent
    case goalType seq of
        Prop -> return ()
        _  -> tacError "Pi1 tactic can only be applied to Prop goals!"
    (realX, realA, realB) <- case (fa, goalTerm seq) of
        (Just (Pi x1 a1 b1), Nothing) -> return (x1, a1, b1)
        (Nothing, Just (Pi x2 a2 b2)) -> return (x2, a2, b2)
        (Just (Pi x1 a1 b1), Just (Pi x2 a2 b2)) -> if x1 == x2 && a1 == a2 && b1 == b2
            then return (x1, a1, b1)
            else tacError "Known goal term doesn't equal attempted goal term."
        _ -> tacError "Invalid application of tactic. Goal term or attempted term is not a Pi term."
    extendedCtx <- safeInsertTacHelper realX realA $ functionalContext seq
    freshGoal <- createNewSubgoal $ seq { functionalContext = extendedCtx, goalTerm = Just realB }
    useCurrentSubgoal . buildJustification1 freshGoal $ Pi1Rule realX
    return "Pi1 tactic applied."

pi2Tac :: Maybe FunctionalTerm -> FunctionalTactic
pi2Tac fa = do
    seq <- getCurrentSequent
    (realX, realA, realB) <- case (fa, goalTerm seq) of
        (Just (Pi x1 a1 b1), Nothing) -> return (x1, a1, b1)
        (Nothing, Just (Pi x2 a2 b2)) -> return (x2, a2, b2)
        (Just (Pi x1 a1 b1), Just (Pi x2 a2 b2)) -> if x1 == x2 && a1 == a2 && b1 == b2
            then return (x1, a1, b1)
            else tacError "Known goal term doesn't equal attempted goal term."
        _ -> tacError "Invalid application of tactic. Goal term or attempted term is not a Pi term."
    extendedCtx <- safeInsertTacHelper realX realA $ functionalContext seq
    freshGoalLeft <- createNewSubgoal $ seq { goalTerm = Just realA }
    freshGoalRight <- createNewSubgoal $ seq { functionalContext = extendedCtx, goalTerm = Just realB }
    useCurrentSubgoal . buildJustification2 freshGoalLeft freshGoalRight $ Pi2Rule realX
    return "Pi2 tactic applied."

lambdaTac :: FunctionalTactic
lambdaTac = do
    seq <- getCurrentSequent
    case goalType seq of
        Pi x a b -> do
            realM <- case goalTerm seq of
                Just (Lambda x1 a1 m) -> if x1 /= x || a1 /= a then tacError "Invalid Lambda term for Pi type." else return . Just $ m
                Just _ -> tacError "Expected Lambda term for Pi type."
                Nothing -> return Nothing
            extendedCtx <- safeInsertTacHelper x a (functionalContext seq)
            freshGoal <- createNewSubgoal $ seq { goalTerm = realM, goalType = b, functionalContext = extendedCtx }
            useCurrentSubgoal . buildJustification1 freshGoal $ LambdaRule x
            return "Lambda tactic applied"
        _ -> tacError "Tactic cannot be used on non-Pi goal."

tyAppTac :: String -> FunctionalTerm -> Maybe FunctionalTerm -> FunctionalTactic
tyAppTac x a nMaybe = do
    seq <- getCurrentSequent
    (m, realNTerm) <- case (nMaybe, goalTerm seq) of
            (Just n, Nothing) -> return (Nothing, n)
            (Nothing, Just (App m1 n1)) -> return (Just m1, n1)
            (Just n, Just (App m1 n1)) -> if n == n1 then return (Just m1, n1) else tacError "Cannot apply tactic with given substitution term different than known term."
            (Nothing, Just _) -> tacError "Cannot apply tactic with known non-app term."
            (Nothing, Nothing) -> tacError "Cannot determine substitution term. None provided and none known."
    let newB = abstTermFunctional (goalType seq) x realNTerm
    freshGoalLeft <- createNewSubgoal $ seq { goalTerm = m, goalType = Pi x a newB }
    freshGoalRight <- createNewSubgoal $ seq { goalTerm = Just realNTerm, goalType = a }
    useCurrentSubgoal . buildJustification2 freshGoalLeft freshGoalRight $ AppRule
    return "Tyapp tactic applied."

sigmaTac :: Maybe FunctionalTerm -> FunctionalTactic
sigmaTac fa = do
    seq <- getCurrentSequent
    (realX, realA, realB) <- case (fa, goalTerm seq) of
        (Just (Sigma x1 a1 b1), Nothing) -> return (x1, a1, b1)
        (Nothing, Just (Sigma x2 a2 b2)) -> return (x2, a2, b2)
        (Just (Sigma x1 a1 b1), Just (Pi x2 a2 b2)) -> if x1 == x2 && a1 == a2 && b1 == b2
            then return (x1, a1, b1)
            else tacError "Known goal term doesn't equal attempted goal term."
        _ -> tacError "Invalid application of tactic. Goal term or attempted term is not a Pi term."
    --freshX <- getFreshVarAttempt realX
    --let newB = functionalSubst realB (Var freshX) realX
    extendedCtx <- safeInsertTacHelper realX realA $ functionalContext seq
    freshGoalLeft <- createNewSubgoal $ seq { goalTerm = Just realA }
    freshGoalRight <- createNewSubgoal $ seq { functionalContext = extendedCtx, goalTerm = Just realB }
    useCurrentSubgoal . buildJustification2 freshGoalLeft freshGoalRight $ SigmaRule realX
    return "Sigma tactic applied."

pairTac :: Maybe FunctionalTerm -> Maybe FunctionalTerm -> Integer -> FunctionalTactic
pairTac mMaybe nMaybe j = do
    seq <- getCurrentSequent
    realMTerm <- case (mMaybe, goalTerm seq) of
        (Just suppliedM, Nothing) -> return suppliedM
        (Nothing, Just (Pair m n x a b)) -> return m
        (Nothing, Nothing) -> tacError "Cannot determine M term. Must be supplied."
        _ -> tacError "Invalid terms supplied or found for pair tactic."
    realNTerm <- case (nMaybe, goalTerm seq) of
        (Just suppliedM, Nothing) -> return (Just suppliedM)
        (Nothing, Just (Pair m n x a b)) -> return (Just n)
        (Nothing, Nothing) -> return Nothing
        _ -> tacError "Invalid terms supplied or found for pair tactic."
    (x, a, b) <- case goalType seq of
        Sigma x a b -> return (x, a, b)
    extendedCtx <- safeInsertTacHelper x a (functionalContext seq)
    freshGoal1 <- createNewSubgoal $ seq { goalTerm = Just realMTerm, goalType = a }
    freshGoal2 <- createNewSubgoal $ seq { goalTerm = realNTerm, goalType = functionalSubst b realMTerm x }
    freshGoal3 <- createNewSubgoal $ seq { functionalContext = extendedCtx, goalTerm = Just b, goalType = Type j }
    useCurrentSubgoal . buildJustification3 freshGoal1 freshGoal2 freshGoal3 $ PairRule x
    return "Pair tactic applied."

proj1Tac :: String -> FunctionalTerm -> FunctionalTactic
proj1Tac x b = do
    seq <- getCurrentSequent
    realM <- case goalTerm seq of
        Nothing -> return Nothing
        (Just (Proj1 inner)) -> return (Just inner)
        _ -> tacError "Invalid term for proj1 tactic."
    freshGoal <- createNewSubgoal $ seq { goalTerm = realM, goalType = Sigma x (goalType seq) b }
    useCurrentSubgoal . buildJustification1 freshGoal $ Proj1Rule
    return "Proj1 tactic applied"

proj2Tac :: String -> FunctionalTerm -> Maybe FunctionalTerm -> FunctionalTactic
proj2Tac x a mMaybe = do
    seq <- getCurrentSequent
    realM <- case (mMaybe, goalTerm seq) of
        (Nothing, Just (Proj2 inner)) -> return inner
        (Just inner, Nothing) -> return inner
        (Just inner1, Just (Proj2 inner2)) -> if inner1 == inner2 then return inner1 else tacError "Mismatched M terms supplied and found."
        _ -> tacError "Invalid term for proj2 tactic."
    freshGoal <- createNewSubgoal $ seq { goalTerm = Just realM, goalType = Sigma x a (abstTermFunctional (goalType seq) x (Proj1 realM)) }
    useCurrentSubgoal . buildJustification1 freshGoal $ Proj2Rule
    return "Proj2 tactic applied"

cumulativityTac :: FunctionalTerm -> Integer -> FunctionalTactic
cumulativityTac a j = do
    seq <- getCurrentSequent
    if cumulativiyRelation (goalType seq) a
    then (do
        freshGoalLeft <- createNewSubgoal $ seq { goalType = a }
        freshGoalRight <- createNewSubgoal $ seq { goalTerm = Just $ goalType seq, goalType = Type j }
        useCurrentSubgoal . buildJustification2 freshGoalLeft freshGoalRight $ CumulativiyRule
        return "Cumulativity tactic applied")
    else tacError $ show a ++ " does not reduce to " ++ show (goalType seq)

simpTac :: Integer -> FunctionalTactic
simpTac steps = do
    seq <- getCurrentSequent
    let reductions = L.take (fromInteger steps) $ allConversionSteps (goalType seq) -- avoid infinite loops by limiting to set number of steps.
        newGoal = L.last reductions
    freshGoalLeft <- createNewSubgoal $ seq { goalType = newGoal }
    case extractProofFromTermUnderCtx (functionalContext seq) (goalType seq) of -- Prove the original type was well formed
        Right (_, wfP) ->
            case verifyFunctionalProofM wfP of
                Right j -> (do
                            case FS.goalType j of
                                Type j -> return ()
                                _ -> tacError "Cannot simplify types that are not in a Type j universe."
                            useCurrentSubgoal . buildJustification1 freshGoalLeft $ (`CumulativiyRule` wfP)
                            return "Simp applied.")
                (Left e) -> tacError e
        Left e -> tacError e

exactTac :: FunctionalTerm -> FunctionalTactic
exactTac ft = do
    seq <- getCurrentSequent
    let pMaybe = extractProofFromTermUnderCtx (functionalContext seq) ft
    p <- case pMaybe of
        Right (_, res) -> return res
        Left e -> tacError e
    case verifyFunctionalProofM p of
        Right seq -> do
            useCurrentSubgoal . buildJustification0 $ p
            return "Exact tactic applied"
        Left e -> tacError e

exactKnownTac :: FunctionalTactic
exactKnownTac = do
    seq <- getCurrentSequent
    case goalTerm seq of
        Just res -> exactTac res
        Nothing -> tacError "No term known for goal."

isComplete :: ProofState -> Bool
isComplete s = all used (Data.Map.elems $ subgoals s)

getProof :: ProofState -> Either String FunctionalProof
getProof s = case Data.Map.lookup "?a" $ subgoals s of
    Just sg -> runIdentity $ E.runExceptT (fst <$> ST.runStateT (subgoalJustification sg) s)
    Nothing -> Left "Could not find first subgoal!"

runProofState :: ST.StateT s (E.ExceptT String Identity) a -> s -> Either String (a, s)
runProofState a s = runIdentity $ E.runExceptT $ ST.runStateT a s

applyFTactic :: ProofState -> FunctionalTactic -> Either String ProofState
applyFTactic s t = case runProofState t s of
    Right (notif, newState) -> Right newState
    Left e -> Left e

applyFTacticM :: Either String ProofState -> FunctionalTactic -> Either String ProofState
applyFTacticM s t = s >>= (\s -> applyFTactic s t)

-- ============================================================
-- DSL for FunctionalTactics.hs
-- ============================================================

-- Start a theorem
_FTheorem :: FunctionalContext -> FunctionalTerm -> S.Set String -> ProofState
_FTheorem ctx g reserved =
    initializeState (initializeProof (FunctionalTacticsSequent
        { functionalContext = ctx
        , goalTerm = Nothing
        , goalType = g
        })) reserved

_FApply :: Either String ProofState -> FunctionalTactic -> Either String ProofState
_FApply = applyFTacticM

-- Completion
_FDone :: ProofState -> Bool
_FDone = isComplete

_FQED :: ProofState -> Bool
_FQED = _FDone

-- Extract proof
_FGetProof :: ProofState -> Either String FunctionalProof
_FGetProof st = getProof st

-- Core rules
{-| Tactic: Apply the axiom tactic. Proving Prop:Type 0 -}
_FAx :: FunctionalTactic
_FAx = cTac

{-| Tactic: Apply the well-formed tactic. Attempt to complete a full proof that the types in the context are well formed. -}
-- _FWF :: FunctionalTactic
-- _FWF = wfTac

{-| Tactic: Provide the variable with the type in the context. -}
_FVar :: String -> FunctionalTactic
_FVar = varTac

{-| Tactic: Automatically find the variable with the type in the context. -}
_FVarA :: FunctionalTactic
_FVarA = varATac

{-| Tactic: For goals of the form (Pi x:A . B) : Prop. Supply the Pi term if it is not known. -}
_FPi1 :: Maybe FunctionalTerm -> FunctionalTactic
_FPi1 = pi1Tac

{-| Tactic: For goals of the form (Pi x: A . B) : Type_j. Supply the Pi term if it is not known.  -}
_FPi2 :: Maybe FunctionalTerm -> FunctionalTactic
_FPi2 = pi2Tac

{-| Tactic: For goals of the form (\x:A.N):(Pi x:A.B) -}
_FLambda :: FunctionalTactic
_FLambda = lambdaTac

{-| Tactic: x, the type of x, and the maybe term that x was replaced with. Do not supply optional term if the extract term is known. -}
_FApp :: String -> FunctionalTerm -> Maybe FunctionalTerm -> FunctionalTactic
_FApp = tyAppTac

{-| Tactic: For goals of the form Sigma x : A . B : Type j -}
_FSigma :: Maybe FunctionalTerm -> FunctionalTactic
_FSigma = sigmaTac

{-| Tactic: For goals of the form (M,N):(Sigma x:A.B) -}
_FPair :: Maybe FunctionalTerm -> Maybe FunctionalTerm -> Integer -> FunctionalTactic
_FPair = pairTac

{-| Tactic: For goals of the form fst M:A that refine to M:Sigma x:A.B -}
_FProj1 :: String -> FunctionalTerm -> FunctionalTactic
_FProj1 = proj1Tac

{-| Tactic: For goals of the form snd M:[fst M/x]B that refine to M:Sigma x:A.B -}
_FProj2 :: String -> FunctionalTerm -> Maybe FunctionalTerm -> FunctionalTactic
_FProj2 = proj2Tac

{-| Tactic: Attempt to refine a goal A' to the supplied A within a certain number of reduction steps. -}
_FCumulativity :: FunctionalTerm -> Integer -> FunctionalTactic
_FCumulativity = cumulativityTac

{-| Tactic: Simplify the goal term the provided number of times. -}
_FSimp :: Integer -> FunctionalTactic
_FSimp = simpTac

{-| Tactic: Prove the goal is inhabited with the supplied term. -}
_FExact :: FunctionalTerm -> FunctionalTactic
_FExact = exactTac

{-| Tactic: Attempt to prove the goal automatically if the term is known. -}
_FExactKnown :: FunctionalTactic
_FExactKnown = exactKnownTac

-- Hole / Fiat (alias for axiom/hole-style step)
-- _FHole :: FunctionalTactic
-- _FHole = do
--     seq <- getCurrentSequent
--     useCurrentSubgoal . buildJustification0 $ FHoleRule (functionalContext seq) (fromMaybe FHoleTerm (goalTerm seq)) (goalType seq)
--     return "Hole applied."

-- _FFiat :: FunctionalTactic
-- _FFiat = _FHole

-- Tacticals
{-| Tactic: Apply the first tactic and then the second to the resulting subgoals. -}
_FThen :: FunctionalTactic -> FunctionalTactic -> FunctionalTactic
_FThen t1 t2 = do
    currentSubgoals <- ST.gets subgoals
    res1 <- t1
    newSubgoals <- ST.gets subgoals
    let toApplySubgoals = Data.Map.filter (not . used) $ Data.Map.difference newSubgoals currentSubgoals
    t2Res <- mapM (\sgn -> (do
            ST.modify (\s -> s { curSubgoal = sgn })
            t2)) (Data.Map.keys toApplySubgoals)
    return (res1 ++ "\n" ++ L.foldl' (\a b -> a ++ "\n" ++ b) "" t2Res)

{-| Tactic: Attempt to apply the first tactic and then the second if the first does not succeed. -}
_FAlt :: FunctionalTactic -> FunctionalTactic -> FunctionalTactic
_FAlt t1 t2 = t1 `mplus` t2

{-| Tactic: Skip the tactic application. Always succeeds. -}
_FSkip :: FunctionalTactic
_FSkip = do
    seq <- getCurrentSequent
    newGoal <- createNewSubgoal seq
    useCurrentSubgoal . buildJustification1 newGoal $ id
    return "Skip applied."

{-| Tactic: Repeat the application of a tactic until it fails. -}
_FRepeat :: FunctionalTactic -> FunctionalTactic
_FRepeat t = t `_FThen` (_FRepeat t `_FAlt` return "Repeat applied")
