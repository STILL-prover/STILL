{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
module Tactics where

import Data.Map
import qualified Data.Set as S
import qualified Control.Monad.State.Lazy as ST
import qualified Control.Monad.Trans.Except as E
import qualified Data.List as L
import Control.Monad (mplus, when, unless)
import Text.Read (readMaybe)
import Data.Maybe (isJust, fromMaybe, isNothing, fromJust, listToMaybe)
import FunctionalSystem
import qualified FunctionalTactics as FT
import Util
import LinearLogic
import Debug.Trace
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Trans (MonadIO(liftIO))
import qualified Debug.Trace as DBG

data BranchType = Additive
    | Multiplicative -- Indicate the subgoal with the shared channel as root. The String allows unhiding a cut channel.
    | Cut
    | Trunk
    deriving (Eq, Show, Read)

data Subgoal m = Subgoal {
    sequent :: Sequent,
    prevGoal :: String,
    nextGoals :: [String],
    reservedVars :: S.Set String,
    subgoalJustification :: ProverStateT m Proof,
    expanded :: Maybe BranchType,
    inProgressFunctionalProof :: Maybe (FT.ProofState m, FunctionalProof -> Tactic m)
} deriving ()

isUsed :: Subgoal m -> Bool
isUsed = isJust . expanded

getVarsReservedInSubgoalBranches :: ProofState m -> String -> S.Set String
getVarsReservedInSubgoalBranches s sgName = case Data.Map.lookup sgName (subgoals s) of
    Just curSg -> S.unions (getVarsReservedInSubgoalBranches s <$> nextGoals curSg) `S.union` reservedVars curSg
    Nothing -> S.empty

getUnavailableVarsForSubgoal :: String -> ProofState m -> S.Set String
getUnavailableVarsForSubgoal sgName s = case Data.Map.lookup sgName (subgoals s) of
    Just curSg -> (if prevGoal curSg == ""
        then S.empty
        else (case Data.Map.lookup (prevGoal curSg) (subgoals s) of
            Just prevSg -> case expanded prevSg of--DBG.trace (show $ used prevSg) (used prevSg) of
                Just Multiplicative -> let
                        unavailableInBranches = S.unions (getVarsReservedInSubgoalBranches s <$> L.filter (/= sgName) (nextGoals prevSg))
                        unavailableForPrev = getUnavailableVarsForSubgoal (prevGoal curSg) s
                    in unavailableForPrev `S.union` unavailableInBranches-- `S.union` reservedVars prevSg
                Just Cut -> let
                        unavailableInBranches = S.unions (getVarsReservedInSubgoalBranches s <$> L.filter (/= sgName) (nextGoals prevSg))
                        unavailableForPrev = getUnavailableVarsForSubgoal (prevGoal curSg) s
                    in S.delete (channel (sequent prevSg)) $ unavailableForPrev `S.union` unavailableInBranches-- `S.union` reservedVars prevSg
                _ -> getUnavailableVarsForSubgoal (prevGoal curSg) s--reservedVars prevSg `S.union` getUnavailableVarsForSubgoal (prevGoal curSg) s
            _ -> S.empty))
    Nothing -> S.empty

data ProofState m = S {
    subgoals :: Map String (Subgoal m),
    uniqueNameVars :: Map String String,
    usedSubgoalNames :: S.Set String,
    outputs :: [String],
    theorems :: Map String Proof,
    curTheoremName :: String,
    curModuleName :: String,
    loadedModules :: Map String (Map String Proof),
    openGoalStack :: [String]
} deriving ()

curSubgoal :: ProofState m -> String
curSubgoal s = if L.null (openGoalStack s) then "" else head (openGoalStack s)

getStateReservedVars :: Monad m => ProofState m -> S.Set String
getStateReservedVars s = Data.Map.foldl' (\acc sg -> S.union acc (reservedVars sg)) S.empty (subgoals s)

type ProverStateT m a = ST.StateT (ProofState m) (E.ExceptT String m) a

type ProverStateIO a = ProverStateT IO a

type Justification m = ProverStateT m Proof

-- -- data TacticRes = TacSuccess {
-- --     justification :: Justification
-- -- } deriving (Show)

type Tactic m = ProverStateT m String

-- letters :: [String]
-- letters = (\c -> [c]) <$> ['a'..'z']

-- numbers :: [Integer]
-- numbers = [1..]

-- letterNumbers :: [String]
-- letterNumbers = [l ++ show n | n <- numbers, l <- letters]

-- allVars :: [String]
-- allVars = letters ++ letterNumbers

allSubgoalNames :: [String]
allSubgoalNames = ('?' :) <$> namesInOrder
-- >>>L.take 10 allSubgoalNames
-- ["?a","?b","?c","?d","?e","?f","?g","?h","?i","?j"]

getSubgoalNames :: Monad m => Subgoal m -> S.Set String
getSubgoalNames sg = let
    vars = getSequentNames . sequent $ sg
    fVars = maybe S.empty (FT.reservedVars . fst) (inProgressFunctionalProof sg)
    in S.union vars fVars

getProofStateNames :: Monad m => ProverStateT m (S.Set String)
getProofStateNames = do
    curSubgoals <- ST.gets subgoals
    uniqueNames <- S.fromList . L.concatMap (\(k,v) -> [k, v]) . Data.Map.toList <$> ST.gets uniqueNameVars
    let vars = S.unions (uniqueNames:(getSubgoalNames <$> Data.Map.elems curSubgoals))
    return vars

getFreshVar :: Monad m => ProverStateT m String
getFreshVar = do
    vars <- getProofStateNames
    let newVar = head $ Prelude.filter (\l -> not $ S.member l vars) namesInOrder
    ST.modify (\s -> s { uniqueNameVars = Data.Map.insert newVar newVar $ uniqueNameVars s })
    return newVar

getFreshVarNamed :: Monad m => String -> ProverStateT m String
getFreshVarNamed n = do
    vars <- getProofStateNames
    let newVar = head $ Prelude.filter (\l -> not $ S.member l vars) namesInOrder
    ST.modify (\s -> s { uniqueNameVars = Data.Map.insert newVar n $ uniqueNameVars s })
    return newVar

getFreshVarAttempt :: Monad m => String -> ProverStateT m String
getFreshVarAttempt z = do
    vars <- getProofStateNames
    let zs = z:[z ++ show i | i <- numbers]
        newVar = head $ Prelude.filter (\l -> not $ S.member l vars) zs
    ST.modify (\s -> s { uniqueNameVars = Data.Map.insert newVar newVar $ uniqueNameVars s })
    return newVar

getFreshSubgoalName :: Monad m => ProverStateT m String
getFreshSubgoalName = do
    curSubgoals <- ST.gets usedSubgoalNames
    let newSubgoalName = head $ Prelude.filter (\l -> not $ S.member l curSubgoals) allSubgoalNames
    ST.modify (\s -> s { usedSubgoalNames = S.insert newSubgoalName $ usedSubgoalNames s })
    return newSubgoalName

lookupVarName :: Monad m => String -> ProverStateT m String
lookupVarName x = do
    xNameMaybe <- Data.Map.lookup x <$> ST.gets uniqueNameVars
    liftMaybeWithError ("Cannot find name for " ++ x) xNameMaybe

initializeSequent :: Proposition -> Sequent
initializeSequent p = Sequent { tyVarContext = S.empty, fnContext = Data.Map.empty, unrestrictedContext = Data.Map.empty, linearContext = Data.Map.empty, recursiveBindings = Data.Map.empty, channel = "z", goalProposition = p }

initializeProof :: Monad m => Sequent -> Subgoal m
initializeProof seq = Subgoal { sequent = seq, prevGoal = "", nextGoals = [], expanded = Nothing, subgoalJustification = tacError "No justification.", inProgressFunctionalProof = Nothing, reservedVars = S.empty }

tacError :: Monad m => String -> ST.StateT (ProofState m) (E.ExceptT String m) a2
tacError = ST.lift . E.throwE

liftMaybeWithError :: Monad m => String -> Maybe a -> ProverStateT m a
liftMaybeWithError err res = case res of
    Nothing -> tacError err
    Just x -> return x

liftEither :: Monad m => Either String a -> ProverStateT m a
liftEither res = case res of
    Left err -> tacError err
    Right x -> return x

getGoal :: Monad m => String -> ProverStateT m (Subgoal m)
getGoal goalName = do
    curState <- ST.get
    case Data.Map.lookup goalName (subgoals curState) of
        Just goal -> return goal
        _ -> tacError "Invalid subgoal name."

-- -- getDisallowedVars :: String -> ProverStateT m (S.Set String)
-- -- getDisallowedVars goalName = do
-- --     curDisjointGoals <- disjointSubgoals <$> getGoal goalName
-- --     curSubgoals <- subgoals <$> ST.get
-- --     -- Get the subgoals and their reserved variables if the subgoal exists. Then union all reserved variables.
-- --     return $ L.foldl' S.union S.empty (maybe S.empty reservedVars . (`Data.Map.lookup` curSubgoals) <$> curDisjointGoals)

updateGoal :: Monad m => String -> Subgoal m -> ProverStateT m ()
updateGoal goalName newGoalState = do
    curState <- ST.get
    ST.put (curState { subgoals = Data.Map.insert goalName newGoalState (subgoals curState) })

removeVarsFromSequent :: Monad m => [String] -> Sequent -> ProverStateT m Sequent
removeVarsFromSequent varsToRem seq =
    if channel seq `L.elem` varsToRem
    then tacError $ "Cannot reserve the channel of the sequent: " ++ seqToS seq
    else return $ seq { linearContext = L.foldl (flip Data.Map.delete) (linearContext seq) (S.fromList varsToRem) }

removeVarsFromSubgoal :: Monad m => [String] -> (String, Subgoal m) -> ProverStateT m (String, Subgoal m)
removeVarsFromSubgoal varsToRem (x, sg) = if isUsed sg
    then return (x, sg)
    else (do
        newSeq <- removeVarsFromSequent varsToRem (sequent sg)
        return (x, sg { sequent = newSeq }))

reserveVars :: Monad m => [String] -> ProverStateT m ()
reserveVars varsToRes = do
    curSubgoalData <- getCurrentSubgoal
    curSubgoalName <- ST.gets curSubgoal
    unavailableVars <- ST.gets (getUnavailableVarsForSubgoal curSubgoalName)
    let newSgData = curSubgoalData { reservedVars = reservedVars curSubgoalData `S.union` S.fromList varsToRes}
    if L.any (`S.member` unavailableVars) varsToRes
    then tacError "Variables already reserved, and should not be available to use."
    else ST.modify (\s -> s { subgoals = Data.Map.insert curSubgoalName newSgData (subgoals s) })

buildJustification0 :: Monad m => Proof -> Justification m
buildJustification0 = return

buildJustification1 :: Monad m => String -> (Proof -> Proof) -> Justification m
buildJustification1 sg p = do
    curSubgoals <- ST.gets subgoals
    case Data.Map.lookup sg curSubgoals of
        (Just sg) -> do
            jst <- subgoalJustification sg
            return $ p jst
        _ -> tacError $ "Child subgoal lost " ++ sg

buildJustification2 :: Monad m => String -> String -> (Proof -> Proof -> Proof) -> Justification m
buildJustification2 sg1 sg2 p = do
    curSubgoals <- ST.gets subgoals
    case Data.Map.lookup sg1 curSubgoals of
        (Just sg) -> do
            jst <- subgoalJustification sg
            buildJustification1 sg2 (p jst)
        _ -> tacError $ "Child subgoal lost " ++ sg1

{-| 
    This should be the last call to in a tactic before returning the message. It
    pops the current open goal off the stack, and updates the goal with its
    justification. Call createNewSubgoal before this.
-}
useCurrentSubgoal :: Monad m => BranchType -> Justification m -> ProverStateT m ()
useCurrentSubgoal bt j = do
    curState <- ST.get
    let curSubgoals = subgoals curState
        curSubgoalMaybe = Data.Map.lookup (curSubgoal curState) curSubgoals
    curSubgoalObj <- liftMaybeWithError ("Cannot find current subgoal " ++ curSubgoal curState) curSubgoalMaybe
    ST.modify (\s -> s {
        subgoals = Data.Map.insert (curSubgoal curState) (curSubgoalObj { subgoalJustification = j, expanded = Just bt }) (subgoals s),
        openGoalStack = L.drop 1 (openGoalStack curState) }) -- subgoal is expanded and popped off.

getCurrentSubgoal :: Monad m => ProverStateT m (Subgoal m)
getCurrentSubgoal = do
    curSubgoalName <- ST.gets curSubgoal
    curSubgoalMaybe <- Data.Map.lookup curSubgoalName <$> ST.gets subgoals
    liftMaybeWithError ("Cannot find current subgoal " ++ curSubgoalName) curSubgoalMaybe

getCurrentSequent :: Monad m => ProverStateT m Sequent
getCurrentSequent = sequent <$> getCurrentSubgoal

{-|
    Create a new subgoal in the state pointing to the current subgoal as its
    previous. Puts the new goal just below the current open goal. Call
    useCurrentSubgoal after this.
-}
createNewSubgoal :: Monad m => Sequent -> ProverStateT m String
createNewSubgoal seq = do
    freshGoal <- getFreshSubgoalName
    curSubgoalName <- ST.gets curSubgoal
    curSubgoalData <- getCurrentSubgoal
    let newSubgoal = Subgoal { sequent = seq, prevGoal = curSubgoalName, nextGoals = [], subgoalJustification = tacError "No justification", expanded = Nothing, inProgressFunctionalProof = Nothing, reservedVars = S.empty }
        newCurSubgoalData = curSubgoalData { nextGoals = freshGoal:nextGoals curSubgoalData }
    ST.modify (\s -> s { subgoals = Data.Map.insert curSubgoalName newCurSubgoalData (Data.Map.insert freshGoal newSubgoal (subgoals s)), openGoalStack = (head (openGoalStack s)):(freshGoal:tail (openGoalStack s)) })
    return freshGoal

idTac :: Monad m => String -> Tactic m
idTac x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x (linearContext seq) of
        (Just p1) -> if p1 == goalProposition seq
            then do
                -- Get fresh vars needed
                -- Reserve vars
                --reserveVars [x, channel seq]
                reserveVars [x]
                -- Make new subgoals
                -- Make justification lookup unique var names
                x1Name <- lookupVarName x
                x2Name <- lookupVarName (channel seq)
                -- Mark subgoal as used and justify
                useCurrentSubgoal Trunk (buildJustification0 $ IdRule x1Name x2Name (tyVarContext seq) (fnContext seq) (unrestrictedContext seq) (recursiveBindings seq) p1)
                return "Id tactic applied."
            else tacError $ "The propositions " ++ x ++ " and " ++ channel seq ++ " are not the same."
        _ -> tacError $ "Could not find " ++ x ++ " in the linear context."

idATac :: Monad m => Tactic m
idATac = do
    seq <- getCurrentSequent
    case L.filter (\(_, p) -> p == goalProposition seq) . Data.Map.toList $ linearContext seq of
        ((x,p):rest) -> do
            --reserveVars [x, channel seq]
            reserveVars [x]
            xName <- lookupVarName x
            zName <- lookupVarName (channel seq)
            useCurrentSubgoal Trunk (buildJustification0 $ IdRule xName zName (tyVarContext seq) (fnContext seq) (unrestrictedContext seq) (recursiveBindings seq) p)
            return "IdA tactic applied."
        [] -> tacError $ "Could not find " ++ show (goalProposition seq) ++ " in the linear context."

functionalTermRightTac :: Monad m => FunctionalProof -> Tactic m
functionalTermRightTac fp = if verifyFunctionalProof fp
    then (do
        seq <- getCurrentSequent
        fpConcl <- liftEither $ functionalConcl fp
        case goalProposition seq of
            Lift t -> if t == goalType fpConcl then (do
                zName <- lookupVarName $ channel seq
                useCurrentSubgoal Trunk (buildJustification0 $ FunctionalTermRightRule zName fp (tyVarContext seq) (unrestrictedContext seq) (recursiveBindings seq))
                return "Functional term right side tactic applied")
                else tacError $ "Mismatched proof result and goal term:\nEXPECTED: " ++ show t ++ "\nGOT: " ++ show (goalType fpConcl)
            _ -> tacError "Cannot apply tactic to goal.")
    else tacError "Invalid proof."

functionalTermLeftTac :: Monad m => String -> Tactic m
functionalTermLeftTac x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x (linearContext seq) of
        (Just (Lift t)) -> do
            -- Get fresh vars needed
            -- Reserve vars
            reserveVars [x]
            x1Name <- lookupVarName x
            -- Make new subgoals
            freshGoal <- createNewSubgoal $ seq { fnContext = Data.Map.insert x1Name t $ fnContext seq, linearContext = Data.Map.delete x $ linearContext seq }
            -- Make justification lookup unique var names
            -- Mark subgoal as used and justify
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ FunctionalTermLeftRule x1Name
            return "Functional term left side tactic applied."
        Just _ -> tacError "Not a functional term."
        _ -> tacError $ "Could not find " ++ x ++ " in the linear context."

functionalTermLeftTacA :: Monad m => Tactic m
functionalTermLeftTacA = leftTacA functionalTermLeftTac (\case Lift _ -> True; _ -> False)

impliesRightTac :: Monad m => Tactic m
impliesRightTac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        Implication a b -> do
            x <- getFreshVar
            freshGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert x a $ linearContext seq, goalProposition = b }
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ ImpliesRightRule x
            return "Implies right side tactic applied"
        _ -> tacError "Not an implication"

impliesLeftTac :: Monad m => String -> Tactic m
impliesLeftTac x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x (linearContext seq) of
        Just (Implication a b) -> (do
            reserveVars [x]
            y <- getFreshVar
            xName <- lookupVarName x
            freshGoalY <- createNewSubgoal $ seq { linearContext = Data.Map.delete x $ linearContext seq, goalProposition = a, channel = y }
            freshGoalX <- createNewSubgoal $ seq { linearContext = Data.Map.insert x b $ linearContext seq }
            useCurrentSubgoal Multiplicative . buildJustification2 freshGoalY freshGoalX $ ImpliesLeftRule xName
            return "Implies left side tactic applied.")
        Just _ -> tacError "Cannot apply to non-implication proposition."
        Nothing -> tacError $ "Cannot find " ++ x ++ " in linear context."

leftTacA :: Monad m => (String -> Tactic m) -> (Proposition -> Bool) -> Tactic m
leftTacA tac test = do
    seq <- getCurrentSequent
    sgName <- ST.gets curSubgoal
    unavailableVars <- ST.gets (getUnavailableVarsForSubgoal sgName)
    let candidateProps = Data.Map.keys (Data.Map.filterWithKey (\k v -> not . S.member k $ unavailableVars) (Data.Map.filter test (linearContext seq)))
    if L.null candidateProps then tacError "No propositions in the linear context of the correct form!" else tac (head candidateProps)

impliesLeftTacA :: Monad m => Tactic m
impliesLeftTacA = leftTacA impliesLeftTac (\case Implication _ _ -> True; _ -> False)

unitRightTac :: Monad m => Tactic m
unitRightTac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        Unit -> (do
            --reserveVars [channel seq]
            channelName <- lookupVarName (channel seq)
            useCurrentSubgoal Trunk (return $ UnitRightRule channelName (tyVarContext seq) (fnContext seq) (unrestrictedContext seq) (recursiveBindings seq))
            return "Unit right side tactic applied.")
        _ -> tacError "Cannot apply to non-implication proposition."

unitLeftTac :: Monad m => String -> Tactic m
unitLeftTac x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x (linearContext seq) of
        Just Unit -> do
            -- Get fresh vars needed
            -- Reserve vars
            reserveVars [x]
            -- Make new subgoals
            freshGoal <- createNewSubgoal $ seq { linearContext = Data.Map.delete x $ linearContext seq }
            -- Make justification lookup unique var names
            xName <- lookupVarName x
            -- Mark subgoal as used and justify
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ UnitLeftRule xName
            return "Unit left side tactic applied."
        Just _ -> tacError "Not a Unit proposition."
        _ -> tacError $ "Could not find " ++ x ++ " in the linear context."

unitLeftTacA :: Monad m => Tactic m
unitLeftTacA = leftTacA unitLeftTac (\case Unit -> True; _ -> False)

replicationRightTac :: Monad m => Tactic m
replicationRightTac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        Replication a -> do
            -- Get fresh vars needed
            -- Reserve vars
            --reserveVars [channel seq]
            y <- getFreshVar
            -- Make new subgoals
            freshGoal <- createNewSubgoal $ seq { goalProposition = a, channel = y }
            -- Make justification lookup unique var names
            zName <- lookupVarName $ channel seq
            -- Mark subgoal as used and justify
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ ReplicationRightRule zName
            return "Unit left side tactic applied."
        _ -> tacError "Not a Replication proposition."

replicationLeftTac :: Monad m => String -> Tactic m
replicationLeftTac x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (Replication a) -> do
            -- Get fresh vars needed
            -- Reserve vars
            reserveVars [x]
            u <- getFreshVar
            -- Make new subgoals
            freshGoal <- createNewSubgoal $ seq { unrestrictedContext = Data.Map.insert u a $ unrestrictedContext seq, linearContext = Data.Map.delete x $ linearContext seq }
            -- Make justification lookup unique var names
            xName <- lookupVarName x
            -- Mark subgoal as used and justify
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ ReplicationLeftRule u xName
            return "Unit left side tactic applied."
        Just _ -> tacError "Not a Replication proposition."
        _ -> tacError $ "Cannot find " ++ x ++ " in linear context."

replicationLeftTacA :: Monad m => Tactic m
replicationLeftTacA = leftTacA replicationLeftTac (\case Replication _ -> True; _ -> False)

copyTac :: Monad m => String -> Maybe String -> Tactic m
copyTac u yMaybe = do
    seq <- getCurrentSequent
    case Data.Map.lookup u $ unrestrictedContext seq of
        Just a -> do
            -- Get fresh vars needed
            -- Reserve vars
            y <- maybe getFreshVar getFreshVarAttempt yMaybe
            -- Make new subgoals
            freshGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert y a $ linearContext seq }
            -- Make justification lookup unique var names
            uName <- lookupVarName u
            -- Mark subgoal as used and justify
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ CopyRule uName y
            return "Unit left side tactic applied."
        _ -> tacError $ "Cannot find " ++ u ++ " in unrestricted context."

withRightTac :: Monad m => Tactic m
withRightTac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        With p1 p2 -> do
            zName <- lookupVarName $ channel seq
            --reserveVars [channel seq]
            allUniqueNameVars <- ST.gets uniqueNameVars
            leftGoal <- createNewSubgoal $ seq { goalProposition = p1 }
            rightGoal <- createNewSubgoal $ seq { goalProposition = p2 }
            useCurrentSubgoal Additive $ buildJustification2 leftGoal rightGoal WithRightRule
            return "With right side tactic applied."
        _ -> tacError "Cannot apply tactic to non-with proposition."

withLeft1Tac :: Monad m => String -> Tactic m
withLeft1Tac x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (With p1 p2) -> do
            xName <- lookupVarName x
            reserveVars [x]
            newGoalName <- createNewSubgoal $ seq { linearContext = Data.Map.insert x p1 $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 newGoalName $ WithLeft1Rule xName p2
            return "With left side 1 tactic applied."
        _ -> tacError "Cannot apply tactic to non-with proposition."

withLeft1TacA :: Monad m => Tactic m
withLeft1TacA = leftTacA withLeft1Tac (\case With _ _ -> True; _ -> False)

withLeft2Tac :: Monad m => String -> Tactic m
withLeft2Tac x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (With p1 p2) -> do
            xName <- lookupVarName x
            reserveVars [x]
            newGoalName <- createNewSubgoal $ seq { linearContext = Data.Map.insert x p2 $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 newGoalName $ WithLeft2Rule xName p1
            return "With left side 2 tactic applied."
        _ -> tacError "Cannot apply to non-with proposition."

withLeft2TacA :: Monad m => Tactic m
withLeft2TacA = leftTacA withLeft2Tac (\case With _ _ -> True; _ -> False)

tensorRightTac :: Monad m => Tactic m
tensorRightTac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        Tensor a b -> (do
            --reserveVars [channel seq]
            y <- getFreshVar
            zName <- lookupVarName $ channel seq
            freshGoalY <- createNewSubgoal $ seq { goalProposition = a, channel = y }
            freshGoalZ <- createNewSubgoal $ seq { goalProposition = b }
            useCurrentSubgoal Multiplicative . buildJustification2 freshGoalY freshGoalZ $ TensorRightRule
            return "Tensor right side tactic applied.")
        _ -> tacError "Cannot apply to non-tensor proposition."

tensorLeftTac :: Monad m => String -> Tactic m
tensorLeftTac x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (Tensor a b) -> do
            reserveVars [x]
            xName <- lookupVarName x
            y <- getFreshVar
            freshGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert y a . Data.Map.insert x b . Data.Map.delete x $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ TensorLeftRule xName y
            return "Tensor left side tactic applied"
        Just _ -> tacError "Not a tensor"
        _ -> tacError $ "Could not find " ++ x ++ "in the linear context"

tensorLeftTacA :: Monad m => Tactic m
tensorLeftTacA = leftTacA tensorLeftTac (\case Tensor _ _ -> True; _ -> False)

plusRight1Tac :: Monad m => Tactic m
plusRight1Tac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        Plus a b -> (do
            --reserveVars [channel seq]
            zName <- lookupVarName $ channel seq
            freshGoalZ <- createNewSubgoal $ seq { goalProposition = a }
            useCurrentSubgoal Trunk . buildJustification1 freshGoalZ $ PlusRight1Rule b
            return "Plus right side 1 tactic applied.")
        _ -> tacError "Cannot apply to non-plus proposition."

plusRight2Tac :: Monad m => Tactic m
plusRight2Tac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        Plus a b -> (do
            --reserveVars [channel seq]
            zName <- lookupVarName $ channel seq
            freshGoalZ <- createNewSubgoal $ seq { goalProposition = b }
            useCurrentSubgoal Trunk . buildJustification1 freshGoalZ $ PlusRight2Rule a
            return "Plus right side 2 tactic applied.")
        _ -> tacError "Cannot apply to non-plus proposition."

plusLeftTac :: Monad m => String -> Tactic m
plusLeftTac x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (Plus p1 p2) -> do
            xName <- lookupVarName x
            --freshXRight <- getFreshVarNamed xName
            reserveVars [x]
            allUniqueNameVars <- ST.gets uniqueNameVars
            --let restLC = Data.Map.delete x $ linearContext seq
            -- copiedLinearContext <- Data.Map.fromList <$> mapM (\(k, v) -> case Data.Map.lookup k allUniqueNameVars of
            --     Just n -> (do
            --         newName <- getFreshVarNamed n
            --         return (newName, v))
            --     Nothing -> tacError $ "Could not find variable name for " ++ k) (Data.Map.toList restLC)
            zName <- lookupVarName $ channel seq
            --freshZRight <- getFreshVarNamed zName
            leftGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert x p1 (linearContext seq) }
            rightGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert x p2 (linearContext seq) }
            useCurrentSubgoal Additive $ buildJustification2 leftGoal rightGoal $ PlusLeftRule xName
            return "Plus left side tactic applied."
        Just _ -> tacError "Cannot apply to non-plus proposition"
        Nothing -> tacError $ "Could not find " ++ x ++ " in linear context."

plusLeftTacA :: Monad m => Tactic m
plusLeftTacA = leftTacA plusLeftTac (\case Plus _ _ -> True; _ -> False)

forallRightTac :: Monad m => Tactic m
forallRightTac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        Forall x t p -> do
            --reserveVars [channel seq]
            zName <- lookupVarName $ channel seq
            --freshZ <- getFreshVarNamed zName
            -- freshX <- getFreshVarAttempt x -- TODO do we need this actually?
            -- let newP = substVarProp p freshX x
            newGoal <- createNewSubgoal $ seq { fnContext = Data.Map.insert x t $ fnContext seq, goalProposition = p }
            useCurrentSubgoal Trunk . buildJustification1 newGoal $ ForallRightRule x
            return "Forall right side tactic applied."
        _ -> tacError "Cannot apply to non-forall proposition."

forallLeftTac :: Monad m => String -> FunctionalProof -> Tactic m
forallLeftTac x fp = if verifyFunctionalProof fp then (do
    seq <- getCurrentSequent
    fpConcl <- liftEither $ functionalConcl fp
    case Data.Map.lookup x $ linearContext seq of
        Just (Forall y t p) -> if t == goalType fpConcl then (do
            reserveVars [x]
            xName <- lookupVarName x
            freshGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert x (substVarTerm p (goalTerm fpConcl) y) $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ ForallLeftRule xName y fp
            return "Forall left side tactic applied.")
            else tacError $ "Mismatched proof result and goal term:\nEXPECTED: " ++ show t ++ "\nGOT: " ++ show (goalType fpConcl)
        Just _ -> tacError "Cannot apply to non-forall proposition."
        _ -> tacError $ "Could not find " ++ x ++ " in the linear context.")
    else tacError "Invalid proof."

existsRightTac :: Monad m => FunctionalProof -> Tactic m
existsRightTac fp = if verifyFunctionalProof fp then (do
    seq <- getCurrentSequent
    fpConcl <- liftEither $ functionalConcl fp
    case goalProposition seq of
        Exists x t p -> if t == goalType fpConcl then (do
            --reserveVars [channel seq]
            zName <- lookupVarName $ channel seq
            --newChannel <- getFreshVarNamed zName
            freshGoal <- createNewSubgoal $ seq { goalProposition = substVarTerm p (goalTerm fpConcl) x }
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ ExistsRightRule x fp
            return "Exists right side tactic applied.")
            else tacError $ "Mismatched proof result and goal term:\nEXPECTED: " ++ show t ++ "\nGOT: " ++ show (goalType fpConcl)
        _ -> tacError "Cannot apply to non-exists proposition.")
    else (case verifyFunctionalProofM fp of
        Right res -> tacError "Should not happen at all."
        Left e -> tacError $ "Invalid proof: " ++ e)

existsLeftTac :: Monad m => String -> Tactic m
existsLeftTac x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (Exists y t p) -> do
            reserveVars [x]
            xName <- lookupVarName x
            freshY <- getFreshVarAttempt y
            let newP = substVarProp p x freshY
            newGoal <- createNewSubgoal $ seq { fnContext = Data.Map.insert freshY t $ fnContext seq, linearContext = Data.Map.insert x newP $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 newGoal $ ExistsLeftRule xName freshY
            return "Exists left side tactic applied."
        Just _ -> tacError "Cannot apply to non-exists proposition."
        _ -> tacError "Variable doesn't exist"

existsLeftTacA :: Monad m => Tactic m
existsLeftTacA = leftTacA existsLeftTac (\case Exists {} -> True; _ -> False)

forallRight2Tac :: Monad m => Tactic m
forallRight2Tac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        Forall2 x p -> do
            --reserveVars [channel seq]
            zName <- lookupVarName $ channel seq
            newGoal <- createNewSubgoal $ seq { tyVarContext = S.insert x $ tyVarContext seq, goalProposition = p }
            useCurrentSubgoal Trunk . buildJustification1 newGoal $ ForallRight2Rule x
            return "Forall second order right side tactic applied."
        _ -> tacError "Cannot apply to non-forall second order proposition."

forallLeft2Tac :: Monad m => String -> Proposition -> Tactic m
forallLeft2Tac x b = do
    seq <- getCurrentSequent
    _ <- case wellFormedType (tyVarContext seq) b of Left e ->tacError (propToS b ++ " is not a well-formed type: " ++ e) ; Right () -> return ()
    case Data.Map.lookup x $ linearContext seq of
        Just (Forall2 y p) -> do
            reserveVars [x]
            xName <- lookupVarName x
            freshGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert x (substVarType p b y) $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ ForallLeft2Rule xName y b
            return "Forall second order left side tactic applied."
        Just _ -> tacError "Cannot apply to non-forall second order proposition."
        _ -> tacError $ "Could not find " ++ x ++ " in the linear context."

existsRight2Tac :: Monad m => Proposition -> Tactic m
existsRight2Tac b = do
    seq <- getCurrentSequent
    _ <- case wellFormedType (tyVarContext seq) b of Left e ->tacError (propToS b ++ " is not a well-formed type: " ++ e) ; Right () -> return ()
    case goalProposition seq of
        Exists2 y p -> do
            --reserveVars [(channel seq)]
            zName <- lookupVarName (channel seq)
            freshGoal <- createNewSubgoal $ seq { goalProposition = substVarType p b y }
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ ExistsRight2Rule y b
            return "Exists second order right side tactic applied."
        _ -> tacError "Cannot apply to non-forall second order proposition."

existsLeft2Tac :: Monad m => String -> Tactic m
existsLeft2Tac x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (Forall2 y p) -> do
            reserveVars [x]
            xName <- lookupVarName $ x
            newGoal <- createNewSubgoal $ seq { tyVarContext = S.insert x $ tyVarContext seq, linearContext = Data.Map.insert x p $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 newGoal $ ExistsLeft2Rule xName y
            return "Forall second order right side tactic applied."
        Just _ -> tacError "Cannot apply to non-forall second order proposition."
        _ -> tacError $ "Could not find " ++ x ++ " in the linear context."

existsLeft2TacA :: Monad m => Tactic m
existsLeft2TacA = leftTacA existsLeft2Tac (\case Exists2 {} -> True; _ -> False)

cutTac :: Monad m => Proposition -> Tactic m
cutTac p = do
    seq <- getCurrentSequent
    --reserveVars [channel seq]
    x <- getFreshVar
    zName <- lookupVarName $ channel seq
    freshGoalY <- createNewSubgoal $ seq { goalProposition = p, channel = x }
    freshGoalZ <- createNewSubgoal $ seq { linearContext = Data.Map.insert x p $ linearContext seq }
    useCurrentSubgoal Cut . buildJustification2 freshGoalY freshGoalZ $ CutRule
    return "Cut tactic applied."

cutReplicationTac :: Monad m => Proposition -> Tactic m
cutReplicationTac p = do
    seq <- getCurrentSequent
    --reserveVars [channel seq]
    x <- getFreshVar
    u <- getFreshVar
    zName <- lookupVarName $ channel seq
    freshGoalY <- createNewSubgoal $ seq { linearContext = Data.Map.empty, goalProposition = p, channel = x }
    freshGoalZ <- createNewSubgoal $ seq { unrestrictedContext = Data.Map.insert u p $ unrestrictedContext seq }
    useCurrentSubgoal Multiplicative . buildJustification2 freshGoalY freshGoalZ $ CutRule
    return "Cut replication tactic applied."

nuRightTac :: Monad m => String -> [String] -> [String] -> Tactic m
nuRightTac x ys zs = do
    seq <- getCurrentSequent
    case goalProposition seq of
        TyNu y a -> (do
            let yzs = zip ys zs
                newTyVarCtx = L.foldl (\acc (y, z) -> substVarTyVarContext acc y z) (tyVarContext seq) yzs
                newFnCtx = L.foldl (\acc (y, z) -> substVarFunctionalContext acc y z) (fnContext seq) yzs
                newUC = L.foldl (\acc (y, z) -> substVarContext acc y z) (unrestrictedContext seq) yzs
                newLC = L.foldl (\acc (y, z) -> substVarContext acc y z) (linearContext seq) yzs
                newChan = L.foldl (\acc (y, z) -> if acc == z then y else acc) (channel seq) yzs
                bindingSeq = BindingSequent { bindingTyVarContext = newTyVarCtx, bindingFnContext = newFnCtx, bindingUC = newUC, bindingLC = newLC, bindingChan = newChan, bindingTyVar = y }
            freshGoalName <- createNewSubgoal $ seq { recursiveBindings = Data.Map.insert x (ys, bindingSeq) $ recursiveBindings seq, goalProposition = a }
            useCurrentSubgoal Trunk . buildJustification1 freshGoalName $ TyNuRightRule x zs
            return "Nu right tactic applied.")
        _ -> tacError "Cannot apply to non-Nu proposition."

nuLeftTac :: Monad m => String -> Tactic m
nuLeftTac c = do
    seq <- getCurrentSequent
    case Data.Map.lookup c (linearContext seq) of
        Just (TyNu x a) -> (do
            reserveVars [c]
            freshGoalName <- createNewSubgoal $ seq { linearContext = Data.Map.insert c (unfoldRec a x a) $ linearContext seq}
            useCurrentSubgoal Trunk . buildJustification1 freshGoalName $ TyNuLeftRule c x
            return "Nu left tactic applied.")
        Just _ -> tacError "Cannot apply to non-Nu proposition."
        Nothing -> tacError $ "Cannot find " ++ c ++ " in linear context."

nuLeftTacA :: Monad m => Tactic m
nuLeftTacA = leftTacA nuLeftTac (\case TyNu {} -> True; _ -> False)

tyVarTac :: Monad m => String -> [String] -> Tactic m
tyVarTac x zs = do
    seq <- getCurrentSequent
    curSgName <- ST.gets curSubgoal
    case Data.Map.lookup x (recursiveBindings seq) of
        Just (ys, xSeq) -> (do
            when (L.length zs /= L.length ys) (tacError "Invalid number of arguments")
            unavailVars <- getUnavailableVarsForSubgoal curSgName <$> ST.get
            let yzs = zip ys zs
                boundSeqRenamedTyVarContext = L.foldl (\acc (y, z) -> substVarTyVarContext acc z y) (bindingTyVarContext xSeq) yzs
                boundSeqRenamedFnContext = L.foldl (\acc (y, z) -> substVarFunctionalContext acc z y) (bindingFnContext xSeq) yzs
                boundSeqRenamedUCContext = L.foldl (\acc (y, z) -> substVarContext acc z y) (bindingUC xSeq) yzs
                boundSeqRenamedLCContext = L.foldl (\acc (y, z) -> substVarContext acc z y) (bindingLC xSeq) yzs
                boundSeqRenamedChannel = L.foldl (\curVar (y, z) -> if curVar == y then z else curVar) (bindingChan xSeq) yzs
            when (boundSeqRenamedTyVarContext /= tyVarContext seq) $ tacError "Invalid tyvar contexts."
            when (boundSeqRenamedFnContext /= fnContext seq) $ tacError "Invalid functional contexts."
            when (boundSeqRenamedUCContext /= unrestrictedContext seq) $ tacError "Invalid unrestricted contexts."
            when (boundSeqRenamedLCContext /= S.foldl (flip Data.Map.delete) (linearContext seq) unavailVars) $ tacError ("Invalid linear contexts:\n" ++ show boundSeqRenamedLCContext ++ "\n\n" ++ show (S.foldl (flip Data.Map.delete) (linearContext seq) unavailVars))
            when (boundSeqRenamedChannel /= channel seq) $ tacError "Invalid channel."
            useCurrentSubgoal Trunk . buildJustification0 $ TyVarRule (recursiveBindings seq) x zs
            return "Type variable tactic applied.")
        Nothing -> tacError $ "Cannot find " ++ x ++ " in recursive bindings."

replWeakenTac :: Monad m => String -> Tactic m
replWeakenTac u = do
    seq <- getCurrentSequent
    _ <- (if Data.Map.member u (unrestrictedContext seq) then return () else tacError $ u ++ " is not a member of the unrestricted context.")
    newSgName <- createNewSubgoal $ seq { unrestrictedContext = Data.Map.delete u (unrestrictedContext seq) }
    useCurrentSubgoal Trunk . buildJustification1 newSgName $ ReplWeakening u (unrestrictedContext seq Data.Map.! u)
    return "Replication weakening tactic applied."

fnWeakenTac :: Monad m => String -> Tactic m
fnWeakenTac t = do
    seq <- getCurrentSequent
    _ <- (if Data.Map.member t (fnContext seq) then return () else tacError $ t ++ " is not a member of the functional context.")
    newSgName <- createNewSubgoal $ seq { fnContext = Data.Map.delete t (fnContext seq) }
    useCurrentSubgoal Trunk . buildJustification1 newSgName $ FnWeakening t (fnContext seq Data.Map.! t)
    return "Functional weakening tactic applied."

useProofTac :: Monad m => String -> Tactic m
useProofTac tName = do
    seq <- getCurrentSequent
    ts <- ST.gets theorems
    case concl <$> Data.Map.lookup tName ts of
        Nothing -> tacError "Could not find the provided theorem."
        Just (Left e) -> tacError $ "Error in conclusion: " ++ e
        Just (Right conclusion) -> (do
            if conclusion == seq
            then useCurrentSubgoal Trunk . buildJustification0 $ ts Data.Map.! tName
            else tacError ("Conclusion of the theorem does not match the current goal:\nExpected: " ++ seqToS seq ++ "\nFound: " ++ seqToS conclusion)
            return $ "Applied theorem " ++ tName)

useModuleProofTac :: Monad m => String -> String -> Tactic m
useModuleProofTac mName tName = do
    seq <- getCurrentSequent
    ms <- ST.gets loadedModules
    let t = Data.Map.lookup mName ms >>= Data.Map.lookup tName
    case concl <$> t of
        Nothing -> tacError "Could not find the provided theorem."
        Just (Left e) -> tacError $ "Error in conclusion: " ++ e
        Just (Right conclusion) -> (do
            if conclusion == seq
            then useCurrentSubgoal Trunk . buildJustification0 $ (ms Data.Map.! mName) Data.Map.! tName
            else tacError ("Conclusion of the theorem does not match the current goal:\nExpected: " ++ seqToS seq ++ "\nFound: " ++ seqToS conclusion)
            return $ "Applied theorem " ++ mName ++ "." ++ tName)

cutLinearTheoremTac :: Monad m => String -> Tactic m
cutLinearTheoremTac theoremName = do
    seq <- getCurrentSequent
    ms <- ST.gets loadedModules
    ts <- ST.gets theorems
    let mName = L.takeWhile (/= '.') theoremName
        tName = L.drop 1 . L.dropWhile (/= '.') $ theoremName
        maybeTheorem = if '.' `L.elem` theoremName then (Data.Map.lookup mName ms >>= Data.Map.lookup tName) else (Data.Map.lookup theoremName ts)
    theorem <- case maybeTheorem of Nothing -> tacError "Could not find the theorem."; Just t -> return t
    conclusion <- case concl theorem of Left e -> tacError ("Could not get conclusion of theorem: " ++ e); Right c -> return c
    -- unless (Data.Map.null $ linearContext conclusion) $ tacError "Only theorems with empty linear contexts are supported right now."
    -- unless (Data.Map.null $ unrestrictedContext conclusion) $ tacError "Only theorems with empty unrestricted contexts are supported right now."
    -- unless (Data.Map.null $ fnContext conclusion) $ tacError "Only theorems with empty functional contexts are supported right now."
    -- unless (S.null $ tyVarContext conclusion) $ tacError "Only theorems with empty type variable contexts are supported right now."
    -- unless (Data.Map.null $ recursiveBindings conclusion) $ tacError "Only theorems with empty recursive binding information are supported right now."
    newChan <- getFreshVar
    let newRenamedProof = renameVarInProof theorem newChan (channel conclusion)
        weakenedUnrestrictedProof = L.foldl' (\proof (k, prop) -> ReplWeakening k prop proof) newRenamedProof (Data.Map.toList (unrestrictedContext seq)) -- Add everything needed for the unrestricted context.
        weakenedFnProof = L.foldl' (\proof (k, term) -> FnWeakening k term proof) weakenedUnrestrictedProof (Data.Map.toList (fnContext seq)) -- Add everything needed for the functional context.
        weakenedTyVarProof = L.foldl' (\proof (k) -> TyVarWeakening k proof) weakenedFnProof (S.toList (tyVarContext seq)) -- Add everything needed for the type variable context.
        weakenedRecBindProof = L.foldl' (\proof (k, b) -> RecBindingWeakening k b proof) weakenedTyVarProof (Data.Map.toList (recursiveBindings seq)) -- Add everything needed for the recursive binding context.
    newConclusion <- case concl weakenedRecBindProof of Left e -> tacError ("Could not get conclusion of the renamed variable theorem: " ++ e); Right c -> return c
    freshGoal <- createNewSubgoal (seq { linearContext = Data.Map.insert newChan (goalProposition newConclusion) (linearContext seq) })
    useCurrentSubgoal Multiplicative . buildJustification1 freshGoal $ CutRule weakenedRecBindProof
    return $ "Linear theorem cut tactic applied: " ++ propToS (goalProposition conclusion)

weakenTac :: Monad m => String -> Tactic m
weakenTac t = altTactical (replWeakenTac t) (fnWeakenTac t)

exactTac :: Monad m => Process -> Tactic m
exactTac p = return ""

holeTac :: Monad m => Tactic m
holeTac = do
    seq <- getCurrentSequent
    useCurrentSubgoal Trunk . buildJustification0 $ HoleRule (tyVarContext seq) (fnContext seq) (unrestrictedContext seq) (linearContext seq) (recursiveBindings seq) (channel seq) (goalProposition seq)
    return "Hole applied."

thenTactical :: Monad m => Tactic m -> Tactic m -> Tactic m
thenTactical t1 t2 = do
    currentSubgoals <- ST.gets openGoalStack
    res1 <- t1
    newSubgoals <- ST.gets openGoalStack
    let toApplySubgoals = L.filter (`notElem` currentSubgoals) newSubgoals
    t2Res <- mapM (\sgn -> (do
            curSgs <- ST.gets openGoalStack
            let i = L.elemIndex sgn curSgs
            ST.modify (\s -> _Prefer s (fromMaybe (-1 :: Int) i))
            t2)) toApplySubgoals
    return (res1 ++ "\n" ++ L.intercalate "\n" t2Res)

skipTactical :: Monad m => Tactic m
skipTactical = do
    seq <- getCurrentSequent
    newGoal <- createNewSubgoal seq
    useCurrentSubgoal Trunk . buildJustification1 newGoal $ id
    return "Skip applied."

altTactical :: Monad m => Tactic m -> Tactic m -> Tactic m
altTactical t1 t2 = t1 `mplus` t2

repeatTactical :: Monad m => Tactic m -> Tactic m
repeatTactical t = t `thenTactical` (repeatTactical t `altTactical` return "Repeat applied")

initCleanState :: String -> ProofState m
initCleanState mName = S { subgoals = Data.Map.empty, uniqueNameVars = Data.Map.empty, usedSubgoalNames = S.empty, outputs = ["Ready to begin!"], curTheoremName = "", curModuleName = mName, theorems = Data.Map.empty, loadedModules = Data.Map.empty, openGoalStack = [] }

{-| Assumes the initial  subgoal has no assumptions in -}
-- initializeState :: String -> Subgoal m -> ProofState m
-- initializeState name goal =
--     let
--         channelVar = (channel . sequent $ goal)
--         linearVars = Data.Map.keys . linearContext . sequent $ goal
--         unrestrictedVars = Data.Map.keys . unrestrictedContext . sequent $ goal
--         fnVars = Data.Map.keys . fnContext . sequent $ goal
--         allVars = channelVar : (linearVars ++ unrestrictedVars ++ fnVars)
--     in
--         S { subgoals = singleton "?a" goal, curSubgoal = "?a", uniqueNameVars = Data.Map.fromList $ (\x -> (x, x)) <$> allVars, usedSubgoalNames = S.singleton "?a", outputs = [], curTheoremName = name, theorems = Data.Map.empty, loadedModules = Data.Map.empty }

runProofState :: ST.StateT s (E.ExceptT String m) a -> s -> m (Either String (a, s))
runProofState a s = E.runExceptT (ST.runStateT a s)

applyTacticGeneral :: Monad m => ProofState m -> Tactic m -> m (Either String (ProofState m))
applyTacticGeneral s t = do
    res <- runProofState t s
    case res of
        Right (notif, newState) -> return . Right $ newState { outputs = notif:outputs newState}
        Left e -> return . Left $ e

-- clear :: Monad m => String -> Proposition -> ProofState m
-- clear name = initializeState name . initializeProof . initializeSequent

theorem :: Monad m => ProofState m -> String -> Proposition -> ProofState m
theorem s n p =
    let
        goal = initializeProof . initializeSequent $ p
        channelVar = (channel . sequent $ goal)
        linearVars = Data.Map.keys . linearContext . sequent $ goal
        unrestrictedVars = Data.Map.keys . unrestrictedContext . sequent $ goal
        fnVars = Data.Map.keys . fnContext . sequent $ goal
        allVars = channelVar : (linearVars ++ unrestrictedVars ++ fnVars)
    in
        s { subgoals = singleton "?a" goal, uniqueNameVars = Data.Map.fromList $ (\x -> (x, x)) <$> allVars, usedSubgoalNames = S.singleton "?a", outputs = "New theorem started":outputs s, curTheoremName = n, openGoalStack = ["?a"] }

applyTactic :: ProofState Identity -> Tactic Identity -> Either String (ProofState Identity)
applyTactic s t = runIdentity $ applyTacticGeneral s t

applyTacticM :: Either String (ProofState Identity) -> Tactic Identity -> Either String (ProofState Identity)
applyTacticM s t = s >>= (\s -> runIdentity $ applyTacticGeneral s t)

verifyGeneral :: Monad m => ProofState m -> m (Either String (Proof, ProofState m))
verifyGeneral s = do
    v <- runProofState (subgoalJustification ( subgoals s ! "?a")) s
    case v of
        Right (p, s) -> return (case verifyProofM p of Right True -> Right (p, s); Right False -> Left "Could not verify the proof." ; Left e ->  Left e)
        Left e -> return (Left e)

extractFromJustification :: Monad m => ProofState m -> m (Either String (Process, Sequent))
extractFromJustification s = do
    v <- runProofState (subgoalJustification ( subgoals s ! "?a")) s
    case v of
        Right (p, s) -> do
            let process1 = extractProcess p
            return process1
        Left err -> return (Left err)

done :: ProofState Identity -> ProofState Identity
done res = case runIdentity (verifyGeneral res) of
    Right (p, s) -> s { theorems = Data.Map.insert (curTheoremName s) p (theorems s),  outputs = ("Theorem complete: " ++ curTheoremName s):outputs res}
    Left err -> res { outputs = ("Could not verify proof: " ++ err):outputs res }

-- DSL

_Init :: String -> ProofState Identity
_Init = initCleanState

_BeginModule :: Monad m => ProofState m -> String -> ProofState m
_BeginModule s m = s { subgoals = Data.Map.empty, uniqueNameVars = Data.Map.empty, usedSubgoalNames = S.empty, outputs = ["Module started: " ++ m], curTheoremName = "", curModuleName = m, theorems = Data.Map.empty, openGoalStack = [] }

-- _Clear :: String -> Proposition -> ProofState Identity
-- _Clear = clear

_Theorem :: ProofState Identity -> String -> Proposition -> ProofState Identity
_Theorem = theorem

_Done :: ProofState Identity -> ProofState Identity
_Done = done

_QED :: ProofState Identity -> ProofState Identity
_QED = _Done

_Extract :: ProofState Identity -> String -> ProofState Identity
_Extract s tName =
    let
        extractor p = case extractProcess p of
            Left e -> s { outputs = e:outputs s }
            Right (prc, seq) -> s { outputs = pToS prc:outputs s }
    in
        case Data.Map.lookup tName (theorems s) of
            Nothing -> case Data.Map.lookup (L.takeWhile (/= '.') tName) (loadedModules s) of
                Nothing -> s { outputs = "Could not find the supplied theorem.":outputs s }
                Just m -> maybe
                  s {outputs = "Could not find the supplied theorem." : outputs s}
                  extractor (Data.Map.lookup (L.tail $ L.dropWhile (/= '.') tName) m)
            Just p -> extractor p

_PushMessage :: ProofState Identity -> String -> ProofState Identity
_PushMessage s m = s { outputs = m:outputs s }

_Apply :: ProofState Identity -> Tactic Identity -> ProofState Identity
_Apply s t = case applyTacticM (Right s) t of
    Right newS -> newS
    Left err -> s { outputs = ("ERROR: " ++ err):outputs s}

{-| Tactic: Apply a tactic from the functional system to a functional subgoal. -}
_FTac :: FT.FunctionalTactic Identity -> Tactic Identity
_FTac t = do
    s <- ST.get
    case Data.Map.lookup (curSubgoal s) (subgoals s) of
        Just sg -> case inProgressFunctionalProof sg of
            Just (fs, p) -> case FT._FApply (Right fs) t of
                Right newFs -> if FT._FDone newFs
                    then case FT._FGetProof newFs of
                        Right fp -> case applyTactic s (p fp) of
                            Right newS -> ST.put newS >> return "Functional proof complete and tactic applied."
                            Left err -> tacError $ "ERROR applying tactic after functional proof: " ++ err
                        Left e -> tacError $ "Proof completed, but justification has errors: " ++ e
                    else ST.put (s { subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (newFs, p) }) (subgoals s) }) >> return "Functional tactic applied."
                Left e -> tacError e
            Nothing -> tacError "No in progress functional proof to apply to in current subgoal."
        Nothing -> tacError $ "Could not find current subgoal name: " ++ curSubgoal s ++ " in subgoals."

_FApply :: ProofState Identity -> FT.FunctionalTactic Identity -> ProofState Identity
_FApply s t = case Data.Map.lookup (curSubgoal s) (subgoals s) of
    Just sg -> case inProgressFunctionalProof sg of
        Just (fs, p) -> case FT._FApply (Right fs) t of
            Right newFs -> if FT._FDone newFs
                then case FT._FGetProof newFs of
                    Right fp -> case applyTactic s (p fp) of
                        Right newS -> newS
                        Left err -> s { outputs = ("ERROR applying tactic after functional proof: " ++ err):outputs s }
                    Left e -> s { outputs = ("Proof completed, but justification has errors: " ++ e):outputs s }
                else s { subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (newFs, p) }) (subgoals s), outputs = "Functional tactic applied.":outputs s }
            Left e -> s { outputs = e:outputs s }
        Nothing -> s { outputs = "No in progress functional proof to apply to in current subgoal.":outputs s }
    Nothing -> s { outputs = ("Could not find current subgoal name: " ++ curSubgoal s ++ " in subgoals."):outputs s }

-- Identity
{-| Tactic: Apply the Id tactic linking an explicitly provided resource with an offered resource. -}
_Id :: Monad m => String -> Tactic m
_Id = idTac

-- Document tactics exactly like this!
{-| Tactic: Apply the Id tactic linking a provided resource with an offered resource. -}
_IdA :: Monad m => Tactic m
_IdA = idATac

-- Functional terms
-- _FTermR :: Monad m => FunctionalProof -> Tactic m
-- _FTermR = functionalTermRightTac
{-| Tactic: Refine a functional term session type to a term in the functional system. -}
_FTermR :: Monad m => Tactic m
_FTermR = do
    curState <- ST.get
    sg <- getCurrentSubgoal
    seq <- getCurrentSequent
    names <- getProofStateNames
    let fullTac p = do
            --ST.modify (\s1 -> s1 { curSubgoal = curSubgoal curState })
            functionalTermRightTac p
    case goalProposition seq of
        Lift t -> (do
                ST.modify (\s -> s { subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (FT._FTheorem  (fnContext seq) t names, fullTac )}) (subgoals s) })
                return "Functional proof in progress.")
        _ -> tacError $ "Cannot apply tactic to non Lift proposition: " ++ show (goalProposition seq)

{-| Tactic: Refine a functional term session type in the assumptions to an assumption in the functional system. -}
_FTermL :: Monad m => String -> Tactic m
_FTermL = functionalTermLeftTac

{-| Tactic: Automatically apply _FTermL to the first functional term in the linear context. -}
_FTermLA :: Monad m => Tactic m
_FTermLA = functionalTermLeftTacA

{-| Tactic: Refine an implication. Assume the antecedent and prove the consequent. -}
_ImpliesR :: Monad m => Tactic m
_ImpliesR = impliesRightTac

{-| Tactic: Refine an implication assumption. Create a goal to prove the antecedent, and another goal where the consequent is an assumption. -}
_ImpliesL :: Monad m => String -> Tactic m
_ImpliesL = impliesLeftTac

{-| Tactic: Automatically apply _ImpliesLA to the first implication proposition in the linear context. -}
_ImpliesLA :: Monad m => Tactic m
_ImpliesLA = impliesLeftTacA

{-| Tactic: Refine a unit proposition. Completes this branch of the proof. -}
_UnitR :: Monad m => Tactic m
_UnitR = unitRightTac

{-| Tactic: Refine a unit assumption. Discards the assumption from the linear context. -}
_UnitL :: Monad m => String -> Tactic m
_UnitL = unitLeftTac

{-| Tactic: Automatically apply _UnitL to the first implication proposition in the linear context. -}
_UnitLA :: Monad m => Tactic m
_UnitLA = unitLeftTacA

{-| Tactic: Refine a replicating proposition. Create a goal to prove the inner proposition. -}
_BangR :: Monad m => Tactic m
_BangR = replicationRightTac

{-| Tactic: Refine a replicating assumption. Moves the inner proposition to the unrestricted context. -}
_BangL :: Monad m => String -> Tactic m
_BangL = replicationLeftTac

{-| Tactic: Automatically apply _BangL to the first implication proposition in the linear context. -}
_BangLA :: Monad m => Tactic m
_BangLA = replicationLeftTacA

{-| Tactic: Creates a copy of an assumption in the unrestricted context in the linear context. -}
_Copy :: Monad m => String -> Maybe String -> Tactic m
_Copy = copyTac

{-| Tactic: Refine a With proposition. Creates two goals. One to prove the left side, and the other to prove the right side. -}
_WithR :: Monad m => Tactic m
_WithR = withRightTac

{-| Tactic: Refine a With assumption. Selects the left side as the assumption. -}
_WithL1 :: Monad m => String -> Tactic m
_WithL1 = withLeft1Tac

{-| Tactic: Automatically apply _WithL1 to the first implication proposition in the linear context. -}
_WithL1A :: Monad m => Tactic m
_WithL1A = withLeft1TacA

{-| Tactic: Refine a With assumption. Selects the right side as the assumption. -}
_WithL2 :: Monad m => String -> Tactic m
_WithL2 = withLeft2Tac

{-| Tactic: Automatically apply _WithL2 to the first implication proposition in the linear context. -}
_WithL2A :: Monad m => Tactic m
_WithL2A = withLeft2TacA

{-| Tactic: Refine a Tensor proposition. Creates two goals. One to prove the left side, and the other to prove the right side. -}
_TensorR :: Monad m => Tactic m
_TensorR = tensorRightTac

{-| Tactic: Refine a Tensor assumption. Both sides become one assumption each. -}
_TensorL :: Monad m => String -> Tactic m
_TensorL = tensorLeftTac

{-| Tactic: Automatically apply _TensorL to the first implication proposition in the linear context. -}
_TensorLA :: Monad m => Tactic m
_TensorLA = tensorLeftTacA

{-| Tactic: Refine a Plus proposition. Selects the left side as the goal. -}
_PlusR1 :: Monad m => Tactic m
_PlusR1 = plusRight1Tac

{-| Tactic: Refine a Plus proposition. Selects the right side as the goal. -}
_PlusR2 :: Monad m => Tactic m
_PlusR2 = plusRight2Tac

{-| Tactic: Refine a Plus assumption. Two subgoals are created. One to complete the proof with the left side of the assumption, and one for the right side. -}
_PlusL :: Monad m => String -> Tactic m
_PlusL = plusLeftTac

{-| Tactic: Automatically apply _PlusL to the first implication proposition in the linear context. -}
_PlusLA :: Monad m => Tactic m
_PlusLA = plusLeftTacA

{-| Tactic: Refine a forall quantification proposition. Adds the term to the functional context. -}
_ForallR :: Monad m => Tactic m
_ForallR = forallRightTac

{-| Tactic: Refine a forall quantification assumption. Creates a subgoal to validate the type of the term, and another to continue the proof once validated. -}
_ForallL :: Monad m => String -> Tactic m
_ForallL x = do
    curState <- ST.get
    sg <- getCurrentSubgoal
    seq <- getCurrentSequent
    names <- getProofStateNames
    let fullTac p = do
            --ST.modify (\s1 -> s1 { curSubgoal = curSubgoal curState })
            forallLeftTac x p
    case Data.Map.lookup x (linearContext seq) of
        Just (Forall x t p) -> (do
                ST.modify (\s -> s { subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (FT._FTheorem  (fnContext seq) t names, fullTac )}) (subgoals s) })
                return "Functional proof in progress.")
        _ -> tacError $ "Cannot apply tactic to non Forall proposition: " ++ show (goalProposition seq)

_ForallLA :: Monad m => Tactic m
_ForallLA = leftTacA _ForallL (\case Forall x t p -> True; _ -> False)

{-| Tactic: Refine an existential quantification proposition. Creates a subgoal to validate the type of the term, and another to continue the proof once validated. -}
_ExistsR :: Monad m => Tactic m
_ExistsR = do
    curState <- ST.get
    sg <- getCurrentSubgoal
    seq <- getCurrentSequent
    names <- getProofStateNames
    let fullTac p = do
            --ST.modify (\s1 -> s1 { curSubgoal = curSubgoal curState })
            existsRightTac p
    case goalProposition seq of
        Exists x t a -> (do
                ST.modify (\s -> s { subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (FT._FTheorem  (fnContext seq) t names, fullTac )}) (subgoals s) })
                return "Functional proof in progress.")
        _ -> tacError $ "Cannot apply tactic to non Exists proposition: " ++ show (goalProposition seq)

{-| Tactic: Refine an existential quantification assumption. Adds the term to the functional context. -}
_ExistsL :: Monad m => String -> Tactic m
_ExistsL = existsLeftTac

{-| Tactic: Automatically apply _ExistsL to the first implication proposition in the linear context. -}
_ExistsLA :: Monad m => Tactic m
_ExistsLA = existsLeftTacA

{-| Tactic: Refine a second order universal quantified proposition. Adds the variable to the type variable context. -}
_Forall2R :: Monad m => Tactic m
_Forall2R = forallRight2Tac

{-| Tactic: Refine a second order universal quantified assumption. Provide a well-formed type to bind to the abstraction. -}
_Forall2L :: Monad m => String -> Proposition -> Tactic m
_Forall2L = forallLeft2Tac

{-| Tactic: Refine a second order existential quantified proposition. Provide a well-formed type to bind to the abstraction. -}
_Exists2R :: Monad m => Proposition -> Tactic m
_Exists2R = existsRight2Tac

{-| Tactic: Refine a second order existential quantified assumption. Adds the variable to the type variable context. -}
_Exists2L :: Monad m => String -> Tactic m
_Exists2L = existsLeft2Tac

{-| Tactic: Automatically apply _Exists2L to the first implication proposition in the linear context. -}
_Exists2LA :: Monad m => Tactic m
_Exists2LA = existsLeft2TacA

{-| Tactic: Cut a theorem into the proof. A goal to prove the theorem is created, and another goal to use it as an assumption is created. -}
_Cut :: Monad m => Proposition -> Tactic m
_Cut = cutTac

{-| Tactic: Cut a replicating theorem into the proof. A goal to prove the theorem is created, and another goal to use it as an unrestricted assumption is created. -}
_CutRepl :: Monad m => Proposition -> Tactic m
_CutRepl = cutReplicationTac

_CutTheorem :: Monad m => String -> Tactic m
_CutTheorem = cutLinearTheoremTac

_CutReplTheorem :: Monad m => String -> Tactic m
_CutReplTheorem = (\s -> return "Not implemented!")

{-| Tactic: Refine a corecursive proposition. Provide the binding name, parameter names, and initial arguments. -}
_NuR :: Monad m => String -> [String] -> [String] -> Tactic m
_NuR = nuRightTac

{-| Tactic: Refine a corecursive assumption. Unfolds the type one level. -}
_NuL :: Monad m => String -> Tactic m
_NuL = nuLeftTac

{-| Tactic: Automatically apply _NuL to the first implication proposition in the linear context. -}
_NuLA :: Monad m => Tactic m
_NuLA = nuLeftTacA

{-| Tactic: Refine a type variable assumption. Provide the binding name from a previous _NuR application and the new arguments. -}
_TyVar :: Monad m => String -> [String] -> Tactic m
_TyVar = tyVarTac

{-| Tactic: Apply the weaken structural rule to the matching variable in the unrestricted or functional context. Will not allow the other contexts to be modified. -}
_Weaken :: Monad m => String -> Tactic m
_Weaken = weakenTac

-- Hole
_Hole :: Monad m => Tactic m
_Hole = holeTac

_Fiat :: Monad m => Tactic m
_Fiat = _Hole

-- Tacticals
{-| Tactic: Apply one tactic, then the second to the resulting subgoals of the first tactic. -}
_Then :: Monad m => Tactic m -> Tactic m -> Tactic m
_Then = thenTactical

{-| Tactic: Apply one tactic, then the second if the first one fails. -}
_Alt :: Monad m => Tactic m -> Tactic m -> Tactic m
_Alt = altTactical

{-| Tactic: Do nothing and succeed. Useful with _Alt. -}
_Skip :: Monad m => Tactic m
_Skip = skipTactical

{-| Tactic: Apply the tactic until it no longer succeeds. -}
_Repeat :: Monad m => Tactic m -> Tactic m
_Repeat = repeatTactical

{-| Tactic: Apply all available introduction rules. -}
_Intros :: Monad m => Tactic m
_Intros = _Repeat (_ImpliesR `_Alt` _ForallR `_Alt` _Forall2R)

-- _Switch :: Monad m => String -> Tactic m
-- _Switch newSg = do
--     validSwitch <- Data.Map.member newSg <$> ST.gets subgoals
--     if validSwitch
--     then (do
--         --ST.modify (\s -> s{curSubgoal = newSg})
--         return $ "Switched subgoal to " ++ newSg)
--     else (do
--         curState <- ST.get
--         let sgName = L.takeWhile (/= '.') newSg
--             fgName = L.tail . L.dropWhile (/= '.') $ newSg
--         newSgData <- case Data.Map.lookup sgName (subgoals curState) of
--             Nothing -> tacError "No valid switch."
--             Just res -> return res
--         (fs, tac) <- case inProgressFunctionalProof newSgData of
--             Nothing -> tacError "No valid switch."
--             Just res -> return res
--         _ <- (if Data.Map.member fgName (FT.subgoals fs) then return () else tacError "No valid switch.")
--         ST.modify (\s -> s { curSubgoal = sgName, subgoals = Data.Map.insert sgName (newSgData { inProgressFunctionalProof = Just (fs { FT.curSubgoal = fgName }, tac) }) (subgoals s) })
--         return $ "Switched subgoal to " ++ newSg)

_Defer :: Monad m => ProofState m -> ProofState m
_Defer curS =
    let
        filteredStack = L.filter (\name -> maybe False (not . isUsed) (Data.Map.lookup name (subgoals curS))) (openGoalStack curS)
        newStack = if L.null filteredStack then filteredStack else tail filteredStack ++ [head filteredStack]
    in
        curS { openGoalStack = newStack }

_Prefer :: Monad m => ProofState m -> Int ->  ProofState m
_Prefer curS i =
    let
        curSgs = openGoalStack curS
        (hs, ts) = L.splitAt i curSgs
    in
        if i >= L.length curSgs
        then curS
        else curS { openGoalStack = head ts : (hs ++ tail ts) }

_PrintTheorems :: Monad m => ProofState m -> ProofState m
_PrintTheorems s = let
    --printTs curMessage prefix ts = Data.Map.foldrWithKey (\k v acc -> case concl v of Right seq -> k ++ ": " ++ seqToS seq ++ "\n" ++ acc; Left e -> acc) curMessage ts
    localTs = L.intercalate "\n" $ L.filter (/= "") $ (\(n, p) -> case concl p of Right seq -> n ++ ": " ++ seqToS seq; Left e -> "") <$> Data.Map.toList (theorems s)
    modulePrint = L.intercalate "\n" $ L.filter (/= "") $ (\(mName, moduleTheorems) -> L.intercalate "\n" $ L.filter (/= "") $ (\(n, p) -> case concl p of Right seq -> mName ++ "." ++ n ++ ": " ++ seqToS seq; Left e -> "") <$> Data.Map.toList moduleTheorems) <$> Data.Map.toList (loadedModules s)
    --localTs = printTs "" "" (theorems s)
    --fullMessage = Data.Map.foldrWithKey (\k v acc -> acc ++ )
    in s { outputs = (L.intercalate "\n" [modulePrint, localTs]):outputs s }

_LoadModule :: Monad m => ProofState m -> ProofState m -> ProofState m
_LoadModule curState moduleData = curState {
        loadedModules = Data.Map.insert (curModuleName moduleData) (theorems moduleData) (loadedModules curState),
        outputs = ("Loaded module: " ++ curModuleName moduleData):outputs curState
    }

_SaveModule :: Monad m => ProofState m -> ProofState m
_SaveModule curState = curState {
    theorems = Data.Map.empty,
    curModuleName = "",
    loadedModules = Data.Map.insert (curModuleName curState) (theorems curState) (loadedModules curState),
    outputs = ("Saved theorems as module: " ++ curModuleName curState):outputs curState
}

_TestDisallowedVars :: Monad m => Tactic m
_TestDisallowedVars = do
    s <- ST.get
    return $ show (getUnavailableVarsForSubgoal (curSubgoal s) s)

_TestBranchReserved :: Monad m => Tactic m
_TestBranchReserved = do
    s <- ST.get
    return $ show (getVarsReservedInSubgoalBranches  s (curSubgoal s))

_TestPrevGoal :: Monad m => Tactic m
_TestPrevGoal = do
    sg <- getCurrentSubgoal
    return $ prevGoal sg

