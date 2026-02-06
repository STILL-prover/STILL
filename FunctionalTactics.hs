module FunctionalTactics where

import Data.Map
import qualified Data.Set as S
import qualified Control.Monad.State.Lazy as ST
import qualified Control.Monad.Trans.Except as E
import qualified Data.List as L
import Control.Monad (mplus)
import Text.Read (readMaybe)
import Data.Maybe (isJust, fromMaybe, isNothing)
import FunctionalSystem hiding (FunctionalSequent(functionalContext, goalType, goalTerm))
import qualified FunctionalSystem as FS (FunctionalSequent(..))
import Util
import Debug.Trace
import Control.Monad.Trans (MonadIO(liftIO))
import Control.Monad.Identity ( Identity(runIdentity) )
import qualified Data.Map as M

data FunctionalTacticsSequent = FunctionalTacticsSequent {
    functionalContext :: FunctionalContext,
    goalTerm :: Maybe FunctionalTerm,
    goalType :: FunctionalTerm
} deriving (Eq)

ftseqToSHelper :: FunctionalTacticsSequent -> String
ftseqToSHelper seq = L.dropWhile (\c -> c == ',' || c == ' ') (L.foldl (\acc (k, v) -> acc ++ ", " ++ k ++ ":" ++ ftToS v) "" (Data.Map.toList ((functionalContext seq)))) ++ --show (Data.Map.toList (FT.functionalContext seq)) ++
    " |- " ++ (case goalTerm seq of Just t -> ftToS t ; Nothing -> "□") ++ ":" ++ ftToS (goalType seq)

getFunctionalTacticsSequentNames :: FunctionalTacticsSequent -> S.Set String
getFunctionalTacticsSequentNames (FunctionalTacticsSequent fc gt gTy) = functionalNames gTy `S.union` maybe S.empty functionalNames gt `S.union` getFunctionalContextNames fc

data Subgoal m = Subgoal {
    sequent :: FunctionalTacticsSequent,
    prevGoal :: String,
    nextGoals :: [String],
    subgoalJustification :: ProverStateT m FunctionalProof,
    used :: Bool
} deriving ()

data ProofState m = S {
    subgoals :: Map String (Subgoal m),
    curSubgoal :: String,
    usedSubgoalNames :: S.Set String,
    reservedVars :: S.Set String
} deriving ()

initializeProof :: Monad m => FunctionalTacticsSequent -> Subgoal m
initializeProof seq = Subgoal { sequent = seq, prevGoal = "", nextGoals = [], used = False, subgoalJustification = tacError "No justification." }

initializeState :: Subgoal m -> S.Set String -> ProofState m
initializeState goal additionalReservedVars =
    let
        fnVars = getFunctionalContextNames . functionalContext . sequent $ goal
    in
        S { subgoals = singleton "?a" goal, curSubgoal = "?a", reservedVars = additionalReservedVars `S.union` fnVars, usedSubgoalNames = S.singleton "?a" }

type ProverStateT m a = ST.StateT (ProofState m) (E.ExceptT String m) a

type Justification m = ProverStateT m FunctionalProof

buildJustification0 :: Monad m => FunctionalProof -> Justification m
buildJustification0 = return

buildJustification1 :: Monad m => String -> (FunctionalProof -> FunctionalProof) -> Justification m
buildJustification1 sg p = do
    curSubgoals <- ST.gets subgoals
    case Data.Map.lookup sg curSubgoals of
        (Just sg) -> do
            jst <- subgoalJustification sg
            return $ p jst
        _ -> tacError $ "Child subgoal lost " ++ sg

buildJustification2 :: Monad m => String -> String -> (FunctionalProof -> FunctionalProof -> FunctionalProof) -> Justification m
buildJustification2 sg1 sg2 p = do
    curSubgoals <- ST.gets subgoals
    case Data.Map.lookup sg1 curSubgoals of
        (Just sg) -> do
            jst <- subgoalJustification sg
            buildJustification1 sg2 (p jst)
        _ -> tacError $ "Child subgoal lost " ++ sg1

buildJustification3 :: Monad m => String -> String -> String -> (FunctionalProof -> FunctionalProof -> FunctionalProof -> FunctionalProof) -> Justification m
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

type FunctionalTactic m = ProverStateT m String

tacError :: Monad m => String -> ProverStateT m a
tacError = ST.lift . E.throwE

liftMaybeWithError :: Monad m => String -> Maybe a -> ProverStateT m a
liftMaybeWithError err res = case res of
    Nothing -> tacError err
    Just x -> return x

allSubgoalNames :: [String]
allSubgoalNames = ('?' :) <$> namesInOrder

getFreshVar :: Monad m => ProverStateT m String
getFreshVar = do
    curSubgoals <- ST.gets subgoals
    uniqueNames <- reservedVars <$> ST.get
    let vars = S.unions (uniqueNames:(getFunctionalTacticsSequentNames . sequent <$> Data.Map.elems curSubgoals))
    let newVar = head $ Prelude.filter (\l -> not $ S.member l vars) namesInOrder
    ST.modify (\s -> s { reservedVars = S.insert newVar $ reservedVars s })
    return newVar

getFreshVarAttempt :: Monad m => String -> ProverStateT m String
getFreshVarAttempt z = do
    curSubgoals <- ST.gets subgoals
    uniqueNames <- reservedVars <$> ST.get
    let vars = S.unions (uniqueNames:(getFunctionalTacticsSequentNames . sequent <$> Data.Map.elems curSubgoals))
        zs = [z ++ show i | i <- numbers]
        newVar = head $ Prelude.filter (\l -> not $ S.member l vars) zs
    ST.modify (\s -> s { reservedVars = S.insert newVar $ reservedVars s })
    return newVar

getFreshSubgoalName :: Monad m => ProverStateT m String
getFreshSubgoalName = do
    curSubgoals <- ST.gets usedSubgoalNames
    let newSubgoalName = head $ Prelude.filter (\l -> not $ S.member l curSubgoals) allSubgoalNames
    ST.modify (\s -> s { usedSubgoalNames = S.insert newSubgoalName $ usedSubgoalNames s })
    return newSubgoalName

createNewSubgoal :: Monad m => FunctionalTacticsSequent -> ProverStateT m String
createNewSubgoal seq = do
    freshGoal <- getFreshSubgoalName
    curSubgoalName <- ST.gets curSubgoal
    let newSubgoal = Subgoal { sequent = seq, prevGoal = curSubgoalName, nextGoals = [], subgoalJustification = tacError "No justification", used = False }
    ST.modify (\s -> s { subgoals = Data.Map.insert freshGoal newSubgoal $ subgoals s })
    return freshGoal

getCurrentSequent :: Monad m => ProverStateT m FunctionalTacticsSequent
getCurrentSequent = do
    curSubgoalName <- ST.gets curSubgoal
    curSubgoalMaybe <- Data.Map.lookup curSubgoalName <$> ST.gets subgoals
    sequent <$> liftMaybeWithError ("Cannot find current subgoal " ++ curSubgoalName) curSubgoalMaybe

useCurrentSubgoal :: Monad m => Justification m -> ProverStateT m ()
useCurrentSubgoal j = do
    curState <- ST.get
    let curSubgoals = subgoals curState
        curSubgoalMaybe = Data.Map.lookup (curSubgoal curState) curSubgoals
    curSubgoalObj <- liftMaybeWithError ("Cannot find current subgoal " ++ curSubgoal curState) curSubgoalMaybe
    ST.modify (\s -> s { subgoals = Data.Map.insert (curSubgoal curState) (curSubgoalObj { subgoalJustification = j, used = True }) (subgoals s) })
    newSubgoals <- ST.gets subgoals
    let availableNextSubgoals = L.dropWhile (\(x, sg) -> used sg) $ Data.Map.toList newSubgoals
    if not (L.null availableNextSubgoals) then ST.modify (\s -> s { curSubgoal = fst . head $ availableNextSubgoals }) else ST.modify (\s -> s { curSubgoal = "" })

axTac :: Monad m => FunctionalTactic m
axTac = do
    seq <- getCurrentSequent
    let ctx = functionalContext seq
    case goalType seq of
        Type 0 -> if ctx == M.empty then do
                useCurrentSubgoal . buildJustification0 $ FunctionalAxiom ctx
                return "Ax tactic applied." else tacError "Empty context required"
        _ -> tacError $ "EXPECTED: " ++ show (Type 0) ++ "\nRECEIVED: " ++ show (goalType seq)

-- cTac :: Monad m => String -> Integer -> FunctionalTactic m
-- cTac x j = do
--     seq <- getCurrentSequent
--     let ctx = functionalContext seq
--     case M.lookup x ctx of
--         Just xTy -> if goalType seq == Type 0 && (isNothing (goalTerm seq) || goalTerm seq == Just Prop) && j >= 0
--             then (do
--                 freshGoal <- createNewSubgoal $ seq { goalTerm = Just xTy, goalType = Type j }
--                 useCurrentSubgoal . buildJustification1 freshGoal $ CRule x
--                 return "C tactic applied.")
--             else tacError "Cannot apply to non- (Prop:Type 0) goal."
--         Nothing -> tacError $ "Could not find " ++ show x ++ " in the context."

tTac :: Monad m => FunctionalTactic m
tTac = do
    seq <- getCurrentSequent
    let ctx = functionalContext seq
    case goalType seq of
        (Type j) -> if isNothing (goalTerm seq) || goalTerm seq == Just (Type (j-1))
            then (do
                freshGoal <- createNewSubgoal $ seq { goalTerm = Just Prop, goalType = Type 0 }
                useCurrentSubgoal . buildJustification1 freshGoal $ TRule (j - 1)
                return "T tactic applied.")
            else tacError "Goal term is not valid. Should be type universe minus 1."
        _ -> tacError "Cannot apply to non-Type j goal."

-- wfTac :: Monad m => FunctionalTactic m
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

varTac :: Monad m => String -> FunctionalTactic m
varTac x = do
    seq <- getCurrentSequent
    let ctx = functionalContext seq
    case Data.Map.lookup x ctx of
        Just xTy -> if xTy == goalType seq && (isNothing (goalTerm seq) || goalTerm seq == Just (Var x))
            then (do
                let wf = extractProofFromTermUnderCtx (M.delete x ctx) xTy
                    verifWf = wf >>= verifyFunctionalProofM
                case (verifWf, wf) of
                    (Right True, Right wfP) -> useCurrentSubgoal . buildJustification0 $ VarRule x wfP
                    _ -> (do
                        freshGoal <- createNewSubgoal $ seq { functionalContext = M.delete x ctx, goalTerm = Just xTy, goalType = Type 0 }
                        useCurrentSubgoal . buildJustification1 freshGoal $ VarRule x)
                return "Var tactic applied.")
            else tacError $ "Cannot apply tactic. Goal term or type is mismatched.\nEXPECTED: " ++ maybe "" show (goalTerm seq) ++ show (goalType seq) ++ "\nRECEIVED: " ++ show xTy
        _ -> tacError $ "Cannot find " ++ x ++ " in the context."

varATac :: Monad m => FunctionalTactic m
varATac = do
    seq <- getCurrentSequent
    let ctx = functionalContext seq
    case goalTerm seq of
        Just (Var x) -> varTac x
        Nothing -> case L.filter (\(_, p) -> p == goalType seq) . Data.Map.toList $ ctx of
            ((x,xTy):rest) -> varTac x
            _ -> tacError $ "Cannot find a variable with type " ++ show (goalType seq) ++ " in the context."

piTac :: Monad m => Maybe FunctionalTerm -> FunctionalTactic m
piTac fa = do
    seq <- getCurrentSequent
    (realX, realA, realB) <- case (fa, goalTerm seq) of
        (Just (Pi x1 a1 b1), Nothing) -> return (x1, a1, b1)
        (Nothing, Just (Pi x2 a2 b2)) -> return (x2, a2, b2)
        (Just (Pi x1 a1 b1), Just (Pi x2 a2 b2)) -> if x1 == x2 && a1 == a2 && b1 == b2
            then return (x1, a1, b1)
            else tacError "Known goal term doesn't equal attempted goal term."
        _ -> tacError "Invalid application of tactic. Goal term or attempted term is not a Pi term."
    --freshX <- getFreshVarAttempt realX
    --let newB = functionalSubst realB (Var freshX) realX
    freshGoalLeft <- createNewSubgoal $ seq { goalTerm = Just realA }
    freshGoalRight <- createNewSubgoal $ seq { functionalContext = Data.Map.insert realX realA $ functionalContext seq, goalTerm = Just realB }
    useCurrentSubgoal . buildJustification2 freshGoalLeft freshGoalRight $ PiRule realX
    return "Pi tactic applied."

lambdaTac :: Monad m => FunctionalTactic m
lambdaTac = do
    seq <- getCurrentSequent
    case goalType seq of
        Pi x a b -> do
            realM <- case goalTerm seq of
                Just (Lambda x1 a1 m) -> if x1 /= x || a1 /= a then tacError "Invalid Lambda term for Pi type." else return . Just $ m
                Just _ -> tacError "Expected Lambda term for Pi type."
                Nothing -> return Nothing
            freshGoal <- createNewSubgoal $ seq { goalTerm = realM, goalType = b, functionalContext = Data.Map.insert x a $ functionalContext seq }
            useCurrentSubgoal . buildJustification1 freshGoal $ LambdaRule x
            return "Lambda tactic applied"
        _ -> tacError "Tactic cannot be used on non-Pi goal."

tyAppTac :: Monad m => String -> FunctionalTerm -> Maybe FunctionalTerm -> FunctionalTactic m
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

sigmaTac :: Monad m => Maybe FunctionalTerm -> FunctionalTactic m
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
    freshGoalLeft <- createNewSubgoal $ seq { goalTerm = Just realA }
    freshGoalRight <- createNewSubgoal $ seq { functionalContext = Data.Map.insert realX realA $ functionalContext seq, goalTerm = Just realB }
    useCurrentSubgoal . buildJustification2 freshGoalLeft freshGoalRight $ SigmaRule realX
    return "Sigma tactic applied."

pairTac :: Monad m => Maybe FunctionalTerm -> Maybe FunctionalTerm -> Integer -> FunctionalTactic m
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
    freshGoal1 <- createNewSubgoal $ seq { goalTerm = Just realMTerm, goalType = a }
    freshGoal2 <- createNewSubgoal $ seq { goalTerm = realNTerm, goalType = functionalSubst b realMTerm x }
    freshGoal3 <- createNewSubgoal $ seq { functionalContext = M.insert x a (functionalContext seq), goalTerm = Just b, goalType = Type j }
    useCurrentSubgoal . buildJustification3 freshGoal1 freshGoal2 freshGoal3 $ PairRule x
    return "Pair tactic applied."

proj1Tac :: Monad m => String -> FunctionalTerm -> FunctionalTactic m
proj1Tac x b = do
    seq <- getCurrentSequent
    realM <- case goalTerm seq of
        Nothing -> return Nothing
        (Just (Proj1 inner)) -> return (Just inner)
        _ -> tacError "Invalid term for proj1 tactic."
    freshGoal <- createNewSubgoal $ seq { goalTerm = realM, goalType = Sigma x (goalType seq) b }
    useCurrentSubgoal . buildJustification1 freshGoal $ Proj1Rule
    return "Proj1 tactic applied"

proj2Tac :: Monad m => String -> FunctionalTerm -> Maybe FunctionalTerm -> FunctionalTactic m
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

cumulativityTac :: Monad m => FunctionalTerm -> Integer -> FunctionalTactic m
cumulativityTac a j = do
    seq <- getCurrentSequent
    if cumulativiyRelation (goalType seq) a
    then (do
        freshGoalLeft <- createNewSubgoal $ seq { goalType = a }
        freshGoalRight <- createNewSubgoal $ seq { goalTerm = Just $ goalType seq, goalType = Type j }
        useCurrentSubgoal . buildJustification2 freshGoalLeft freshGoalRight $ CumulativiyRule
        return "Cumulativity tactic applied")
    else tacError $ show a ++ " does not reduce to " ++ show (goalType seq)

simpTac :: Monad m => Integer -> FunctionalTactic m
simpTac steps = do
    seq <- getCurrentSequent
    let reductions = L.take (fromInteger steps) $ allConversionSteps (goalType seq) -- avoid infinite loops by limiting to set number of steps.
        newGoal = L.last reductions
    freshGoalLeft <- createNewSubgoal $ seq { goalType = newGoal }
    case extractProofFromTermUnderCtx (functionalContext seq) (goalType seq) of -- Prove the original type was well formed
        Right wfP ->
            case verifyFunctionalProofM wfP of
                Right True -> case functionalConcl wfP of
                        Right j -> (do
                            case FS.goalType j of
                                Type j -> return ()
                                _ -> tacError "Cannot simplify types that are not in a Type j universe."
                            useCurrentSubgoal . buildJustification1 freshGoalLeft $ (`CumulativiyRule` wfP)
                            return "Simp applied.")
                        Left e -> tacError e
                (Left e) -> tacError e
                (Right False) -> tacError $ "Could not verify proof"
        Left e -> tacError e

exactTac :: Monad m => FunctionalTerm -> FunctionalTactic m
exactTac ft = do
    seq <- getCurrentSequent
    let pMaybe = extractProofFromTermUnderCtx (functionalContext seq) ft
    p <- case pMaybe of
        Right res -> return res
        Left e -> tacError e
    case verifyFunctionalProofM p of
        Right True -> do
            useCurrentSubgoal . buildJustification0 $ p
            return "Exact tactic applied"
        Right False -> tacError ("Could not extract valid proof from " ++ show ft)
        Left e -> tacError e

exactKnownTac :: Monad m => FunctionalTactic m
exactKnownTac = do
    seq <- getCurrentSequent
    case goalTerm seq of
        Just res -> exactTac res
        Nothing -> tacError "No term known for goal."

axTacAction :: FunctionalTactic IO
axTacAction = axTac

varTacAction :: FunctionalTerm -> FunctionalTactic IO
varTacAction t = do
    liftIO $ Prelude.putStrLn "Enter the variable name in the context:"
    i <- liftIO Prelude.getLine
    varTac i

largeTypeTacAction :: FunctionalTactic IO
largeTypeTacAction = do
    seq <- getCurrentSequent
    if isJust $ goalTerm seq
    then piTac Nothing
    else (do
        liftIO . Prelude.putStrLn $ "Enter the Pi term that you would like to prove has type " ++ show (goalType seq)
        newGoalTerm <- liftIO Prelude.getLine
        piTac (Prelude.read newGoalTerm))

piTacAction :: FunctionalTactic IO
piTacAction = lambdaTac

tyAppTacAction :: FunctionalTactic IO
tyAppTacAction = do
    liftIO $ Prelude.putStrLn "Enter the variable name you would like to replace in the goal:"
    x <- liftIO Prelude.getLine
    liftIO $ Prelude.putStrLn "Enter the type of the variable as a term:"
    a <- Prelude.read <$> liftIO Prelude.getLine
    seq <- getCurrentSequent
    if isJust $ goalTerm seq
    then tyAppTac x a Nothing
    else (do
        liftIO . Prelude.putStrLn $ "Enter the term you would like to replace " ++ x ++ " with:"
        n <- Prelude.read <$> liftIO Prelude.getLine
        tyAppTac x a (Just n))

betaReduceTacAction :: FunctionalTerm -> FunctionalTactic IO
betaReduceTacAction k = do
    seq <- getCurrentSequent
    liftIO . Prelude.putStrLn $ "Enter a term that beta-reduces to " ++ show (goalType seq)
    a <- Prelude.read <$> liftIO Prelude.getLine
    liftIO . Prelude.putStrLn $ "Enter the level of universe " ++ show (goalType seq)
    j <- Prelude.read <$> liftIO Prelude.getLine
    cumulativityTac a j

actions :: [(String, FunctionalTactic IO)]
actions = []
-- actions = [("ax", axTacAction),
--     ("varT", varTacAction T),
--     ("varP", varTacAction P),
--     ("largeTypeP", largeTypeTacAction P),
--     ("largeTypeT", largeTypeTacAction T),
--     ("piP", piTacAction P),
--     ("piT", piTacAction T),
--     ("tyApp", tyAppTacAction),
--     ("betaP", betaReduceTacAction P),
--     ("betaT", betaReduceTacAction T)]

proveLoop :: ProofState IO -> IO (ProofState IO)
proveLoop st = do
    if Data.Map.member (curSubgoal st) (subgoals st)
    then (do
        Prelude.putStrLn "Current state:"
        Prelude.putStrLn $ "Current subgoal: " ++ curSubgoal st
        Prelude.putStrLn $ "Sequent: " ++ ftseqToSHelper (sequent (subgoals st! curSubgoal st))
        Prelude.putStrLn "Enter a tactic (exit to switch back for now): "
        (i :: String) <- Prelude.getLine
        if L.any (\a -> fst a == i) actions
        then do
            let nextTactic = snd . head $ L.filter (\a -> fst a == i) actions
            tacRes <- E.runExceptT (ST.runStateT nextTactic st)
            case tacRes of
                Right (res, newState) -> (do
                    Prelude.putStrLn res
                    proveLoop newState)
                Left err -> (do
                    Prelude.putStrLn err
                    proveLoop st)
        else return st)
    else return st

prove :: FunctionalContext -> FunctionalTerm -> S.Set String -> IO (ProofState IO)
prove assms g vars = do
    let seq = FunctionalTacticsSequent { functionalContext = assms, goalTerm = Nothing, goalType = g }
    proveLoop $ initializeState (initializeProof seq) vars

continueProof :: ProofState IO -> IO (ProofState IO)
continueProof = proveLoop

-- prove :: FunctionalContext -> FunctionalTerm -> S.Set String -> IO (Either String FunctionalProof)
-- prove assms g vars = do
--     let seq = FunctionalTacticsSequent { functionalContext = assms, goalTerm = Nothing, goalType = g }
--     finalState <- proveLoop $ initializeState (initializeProof seq) vars
--     let firstSubgoal = Data.Map.lookup "?a" $ subgoals finalState
--     case firstSubgoal of
--         Just sg -> E.runExceptT (fst <$> ST.runStateT (subgoalJustification sg) finalState)
--         Nothing -> return (Left "Could not find first subgoal!")

isComplete :: Monad m => ProofState m -> Bool
isComplete s = all used (Data.Map.elems $ subgoals s)

getProof :: Monad m => ProofState m -> m (Either String FunctionalProof)
getProof s = case Data.Map.lookup "?a" $ subgoals s of
    Just sg -> E.runExceptT (fst <$> ST.runStateT (subgoalJustification sg) s)
    Nothing -> return (Left "Could not find first subgoal!")

runProofState :: ST.StateT s (E.ExceptT String m) a -> s -> m (Either String (a, s))
runProofState a s = E.runExceptT (ST.runStateT a s)

applyFTacticGeneral :: Monad m => ProofState m -> FunctionalTactic m -> m (Either String (ProofState m))
applyFTacticGeneral s t = do
    res <- runProofState t s
    case res of
        Right (notif, newState) -> return . Right $ newState
        Left e -> return . Left $ e

applyFTactic :: ProofState Identity -> FunctionalTactic Identity -> Either String (ProofState Identity)
applyFTactic s t = runIdentity $ applyFTacticGeneral s t

applyFTacticM :: Either String (ProofState Identity) -> FunctionalTactic Identity -> Either String (ProofState Identity)
applyFTacticM s t = s >>= (\s -> runIdentity $ applyFTacticGeneral s t)

-- ============================================================
-- DSL for FunctionalTactics.hs
-- ============================================================

-- Start a theorem
_FTheorem :: Monad m => FunctionalContext -> FunctionalTerm -> S.Set String -> ProofState m
_FTheorem ctx g reserved =
    initializeState (initializeProof (FunctionalTacticsSequent
        { functionalContext = ctx
        , goalTerm = Nothing
        , goalType = g
        })) reserved

_FApply :: Either String (ProofState Identity) -> FunctionalTactic Identity -> Either String (ProofState Identity)
_FApply = applyFTacticM

-- Completion
_FDone :: ProofState Identity -> Bool
_FDone = isComplete

_FQED :: ProofState Identity -> Bool
_FQED = _FDone

-- Extract proof
_FGetProof :: ProofState Identity -> Either String FunctionalProof
_FGetProof st = runIdentity (getProof st)

-- Core rules
{-| Tactic: Apply the axiom tactic. Proving Prop:Type 0 -}
_FAx :: Monad m => FunctionalTactic m
_FAx = axTac

{-| Tactic: Apply the well-formed tactic. Attempt to complete a full proof that the types in the context are well formed. -}
-- _FWF :: Monad m => FunctionalTactic m
-- _FWF = wfTac

{-| Tactic: Provide the variable with the type in the context. -}
_FVar :: Monad m => String -> FunctionalTactic m
_FVar = varTac

{-| Tactic: Automatically find the variable with the type in the context. -}
_FVarA :: Monad m => FunctionalTactic m
_FVarA = varATac

{-| Tactic: For goals of the form (Pi x: A . B) : L. Supply the sort of A, and A if it is not known.  -}
_FPi :: Monad m => Maybe FunctionalTerm -> FunctionalTactic m
_FPi = piTac

{-| Tactic: For goals of the form (\x:A.N):(Pi x:A.B) -}
_FLambda :: Monad m => FunctionalTactic m
_FLambda = lambdaTac

{-| Tactic: x, the type of x, and the maybe term that x was replaced with. Do not supply optional term if the extract term is known. -}
_FApp :: Monad m => String -> FunctionalTerm -> Maybe FunctionalTerm -> FunctionalTactic m
_FApp = tyAppTac

{-| Tactic: For goals of the form Sigma x : A . B : Type j -}
_FSigma :: Monad m => Maybe FunctionalTerm -> FunctionalTactic m
_FSigma = sigmaTac

{-| Tactic: For goals of the form (M,N):(Sigma x:A.B) -}
_FPair :: Monad m => Maybe FunctionalTerm -> Maybe FunctionalTerm -> Integer -> FunctionalTactic m
_FPair = pairTac

{-| Tactic: For goals of the form fst M:A that refine to M:Sigma x:A.B -}
_FProj1 :: Monad m => String -> FunctionalTerm -> FunctionalTactic m
_FProj1 = proj1Tac

{-| Tactic: For goals of the form snd M:[fst M/x]B that refine to M:Sigma x:A.B -}
_FProj2 :: Monad m => String -> FunctionalTerm -> Maybe FunctionalTerm -> FunctionalTactic m
_FProj2 = proj2Tac

{-| Tactic: Attempt to refine a goal A' to the supplied A within a certain number of reduction steps. -}
_FCumulativity :: Monad m => FunctionalTerm -> Integer -> FunctionalTactic m
_FCumulativity = cumulativityTac

{-| Tactic: Simplify the goal term the provided number of times. -}
_FSimp :: Monad m => Integer -> FunctionalTactic m
_FSimp = simpTac

{-| Tactic: Prove the goal is inhabited with the supplied term. -}
_FExact :: Monad m => FunctionalTerm -> FunctionalTactic m
_FExact = exactTac

{-| Tactic: Attempt to prove the goal automatically if the term is known. -}
_FExactKnown :: Monad m => FunctionalTactic m
_FExactKnown = exactKnownTac

-- Hole / Fiat (alias for axiom/hole-style step)
-- _FHole :: Monad m => FunctionalTactic m
-- _FHole = do
--     seq <- getCurrentSequent
--     useCurrentSubgoal . buildJustification0 $ FHoleRule (functionalContext seq) (fromMaybe FHoleTerm (goalTerm seq)) (goalType seq)
--     return "Hole applied."

-- _FFiat :: Monad m => FunctionalTactic m
-- _FFiat = _FHole

-- Tacticals
{-| Tactic: Apply the first tactic and then the second to the resulting subgoals. -}
_FThen :: Monad m => FunctionalTactic m -> FunctionalTactic m -> FunctionalTactic m
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
_FAlt :: Monad m => FunctionalTactic m -> FunctionalTactic m -> FunctionalTactic m
_FAlt t1 t2 = t1 `mplus` t2

{-| Tactic: Skip the tactic application. Always succeeds. -}
_FSkip :: Monad m => FunctionalTactic m
_FSkip = do
    seq <- getCurrentSequent
    newGoal <- createNewSubgoal seq
    useCurrentSubgoal . buildJustification1 newGoal $ id
    return "Skip applied."

{-| Tactic: Repeat the application of a tactic until it fails. -}
_FRepeat :: Monad m => FunctionalTactic m -> FunctionalTactic m
_FRepeat t = t `_FThen` (_FRepeat t `_FAlt` return "Repeat applied")
