{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
module SessionTypes.Tactics where

import Data.Map
import qualified Data.Set as S
import qualified Control.Monad.State.Lazy as ST
import qualified Control.Monad.Trans.Except as E
import qualified Data.List as L
import Control.Monad (mplus, when, unless)
import Text.Read (readMaybe)
import Data.Maybe (isJust, fromMaybe, isNothing, fromJust, listToMaybe)
import ECC.Kernel (FunctionalSequent(functionalContext,goalType,goalTerm)
    , FunctionalContext
    , FunctionalTerm(..)
    , FunctionalProof(..)
    , ftToS
    , ctxToList
    , functionalNames
    , getFunctionalContextNames
    , emptyContext
    , ctxLookup
    , ctxEitherLookup
    , ctxMember
    , ctxKeys
    , ctxDelete
    , extractProofFromTermUnderCtx
    , safeInsert
    , functionalFreeVariables
    , alphaConvert
    , functionalSubst
    , cumulativiyRelation
    , allConversionSteps
    , verifyFunctionalProofM
    , abstTermFunctional
    , functionalRename
    , getFunctionalProofNames
    , substVarFunctional
    , foldFunctionalProof
    , getFunctionalContextFreeNames
    , renameVarInFnCtx)
import qualified ECC.Tactics as FT
import Utils.Misc
import SessionTypes.Kernel
import Debug.Trace
import Control.Monad.Identity (Identity (runIdentity))
import qualified Debug.Trace as DBG
import GHC.Conc (par, pseq)

data BranchType = Additive
    | Multiplicative -- Indicate the subgoal with the shared channel as root. The String allows unhiding a cut channel.
    | Cut
    | Trunk
    deriving (Eq, Show, Read)

data Subgoal = Subgoal {
    sequent :: Sequent,
    prevGoal :: String,
    nextGoals :: [String],
    reservedVars :: S.Set String,
    subgoalJustification :: ProverState Proof,
    expanded :: Maybe BranchType,
    inProgressFunctionalProof :: Maybe (FT.ProofState, FunctionalProof -> Tactic)
} deriving ()

isUsed :: Subgoal -> Bool
isUsed = isJust . expanded

getVarsReservedInSubgoalBranches :: ProofState -> String -> S.Set String
getVarsReservedInSubgoalBranches s sgName = case Data.Map.lookup sgName (subgoals s) of
    Just curSg -> S.unions (getVarsReservedInSubgoalBranches s <$> nextGoals curSg) `S.union` reservedVars curSg
    Nothing -> S.empty

getUnavailableVarsForSubgoal :: String -> ProofState -> S.Set String
getUnavailableVarsForSubgoal sgName s = case Data.Map.lookup sgName (subgoals s) of
    Just curSg -> (if prevGoal curSg == ""
        then S.empty
        else (case Data.Map.lookup (prevGoal curSg) (subgoals s) of
            Just prevSg -> case expanded prevSg of--DBG.trace (show $ used prevSg) (used prevSg) of
                Just Multiplicative -> let
                        unavailableInBranches = S.unions (getVarsReservedInSubgoalBranches s <$> L.filter (/= sgName) (nextGoals prevSg))
                        unavailableForPrev = getUnavailableVarsForSubgoal (prevGoal curSg) s
                    in unavailableForPrev `par` (unavailableInBranches `pseq` (unavailableForPrev `S.union` unavailableInBranches))
                Just Cut -> let
                        unavailableInBranches = S.unions (getVarsReservedInSubgoalBranches s <$> L.filter (/= sgName) (nextGoals prevSg))
                        unavailableForPrev = getUnavailableVarsForSubgoal (prevGoal curSg) s
                    in unavailableForPrev `par` (unavailableInBranches `pseq` S.delete (channel (sequent prevSg)) (unavailableForPrev `S.union` unavailableInBranches))
                _ -> getUnavailableVarsForSubgoal (prevGoal curSg) s
            _ -> S.empty))
    Nothing -> S.empty

data Theorem = Theorem {
    proofObject :: Proof,
    numberOfSubgoals :: Integer
}

data ProofState = S {
    subgoals :: Map String Subgoal,
    outputs :: [String],
    theorems :: Map String Theorem,
    curTheoremName :: String,
    curModuleName :: String,
    loadedModules :: Map String (Map String Theorem),
    openGoalStack :: [String],
    cachedProofStateNames :: S.Set String,
    newSubgoalNameList :: [String],
    cachedVarNames :: [String],
    stypeDecls :: [(String, Proposition)],
    fnAssumptions :: FunctionalContext,
    procAssumptions :: [(String, Proposition)],
    stypeAssumptions :: [String],
    errors :: [String]
} deriving ()

substTyDecls :: [(String, Proposition)] -> Proposition -> Proposition
substTyDecls [] p = p
substTyDecls ((n,ty):rest) p = substTyDecls rest (substVarType p ty n)

substTyDeclsM :: Proposition -> ProverState Proposition
substTyDeclsM p = (`substTyDecls` p) <$> ST.gets stypeDecls

curSubgoal :: ProofState -> String
curSubgoal s = if L.null (openGoalStack s) then "" else L.takeWhile (/= '.') $ head (openGoalStack s)

usedSubgoalNames :: ProofState -> S.Set String
usedSubgoalNames s = S.fromList $ Data.Map.keys $ subgoals s

getStateReservedVars :: ProofState -> S.Set String
getStateReservedVars s = Data.Map.foldl' (\acc sg -> S.union acc (reservedVars sg)) S.empty (subgoals s)

type ProverStateT m a = ST.StateT ProofState (E.ExceptT String m) a

type ProverState a = ProverStateT Identity a

type Justification = ProverState Proof

-- -- data TacticRes = TacSuccess {
-- --     justification :: Justification
-- -- } deriving (Show)

type Tactic = ProverState String

-- letters :: [String]
-- letters = (\c -> [c]) <$> ['a'..'z']

-- numbers :: [Integer]
-- numbers = [1..]

-- letterNumbers :: [String]
-- letterNumbers = [l ++ show n | n <- numbers, l <- letters]

-- allVars :: [String]
-- allVars = letters ++ letterNumbers

-- allSubgoalNames :: [String]
-- allSubgoalNames = ('?' :) . (\a -> [a]) <$> ['a'..'z']

allSubgoalNames :: [String]
allSubgoalNames = ('?' :) <$> namesInOrder

-- >>>L.take 10 allSubgoalNames
-- ["?a","?b","?c","?d","?e","?f","?g","?h","?i","?j"]

getSubgoalNames :: Subgoal -> S.Set String
getSubgoalNames sg = let
    vars = getSequentNames . sequent $ sg
    fVars = maybe S.empty (FT.reservedVars . fst) (inProgressFunctionalProof sg)
    in S.union vars fVars

getProofStateNames :: ProverState (S.Set String)
getProofStateNames = do
    cachedNames <- ST.gets cachedProofStateNames
    if S.null cachedNames
    then (do
        curSubgoals <- ST.gets subgoals
        let vars = S.unions (getSubgoalNames <$> Data.Map.elems curSubgoals)
        ST.modify (\s -> s { cachedProofStateNames = vars })
        return vars)
    else return cachedNames

getFreshVar :: ProverState String
getFreshVar = do
    vars <- getProofStateNames
    vNames <- ST.gets cachedVarNames
    let newVNames = Prelude.filter (\l -> not $ S.member l vars) vNames
        newVar = head $ Prelude.filter (\l -> not $ S.member l vars) vNames
    ST.modify (\s -> s { cachedProofStateNames = S.insert newVar (cachedProofStateNames s), cachedVarNames = newVNames })
    return newVar

getFreshVarAttempt :: String -> ProverState String
getFreshVarAttempt z = do
    seq <- getCurrentSequent
    let vars = getSequentFreeNames seq
    let zs = z:[z ++ show i | i <- numbers]
        newVar = head $ Prelude.filter (\l -> not $ S.member l vars) zs
    ST.modify (\s -> s { cachedProofStateNames = S.insert newVar (cachedProofStateNames s) })
    return newVar

getFreshSubgoalName :: ProverState String
getFreshSubgoalName = do
    newNames <- ST.gets newSubgoalNameList
    ST.modify (\s -> s { newSubgoalNameList = tail (newSubgoalNameList s)})
    return (head newNames)

invalidateNameCache :: ProverState ()
invalidateNameCache = ST.modify (\s -> s { cachedProofStateNames = S.empty })

lookupVarName :: String -> ProverState String
lookupVarName x = return x

initializeSequent :: [String] -> FunctionalContext -> [Proposition] -> Proposition -> Sequent
initializeSequent assumedSessionTypes assumedTerms consumedProps p = let
    termNames = getFunctionalContextNames assumedTerms
    currentAllNames = S.insert "z" $ S.fromList assumedSessionTypes `S.union` termNames `S.union` S.unions (propNames <$> (p:consumedProps))
    resourceNames = L.filter (\n -> not $ n `S.member` currentAllNames) namesInOrder
    linearProps = zip resourceNames consumedProps
    in Sequent { tyVarContext = S.fromList assumedSessionTypes, fnContext = assumedTerms, unrestrictedContext = Data.Map.empty, linearContext = Data.Map.fromList linearProps, recursiveBindings = Data.Map.empty, channel = "z", goalProposition = p }

initializeProof :: Sequent -> Subgoal
initializeProof seq = Subgoal { sequent = seq, prevGoal = "", nextGoals = [], expanded = Nothing, subgoalJustification = tacError "No justification.", inProgressFunctionalProof = Nothing, reservedVars = S.empty }

tacError :: String -> ST.StateT ProofState (E.ExceptT String Identity) a2
tacError = ST.lift . E.throwE

liftMaybeWithError :: String -> Maybe a -> ProverState a
liftMaybeWithError err res = case res of
    Nothing -> tacError err
    Just x -> return x

liftEither :: Either String a -> ProverState a
liftEither res = case res of
    Left err -> tacError err
    Right x -> return x

getGoal :: String -> ProverState (Subgoal)
getGoal goalName = do
    curState <- ST.get
    case Data.Map.lookup goalName (subgoals curState) of
        Just goal -> return goal
        _ -> tacError "Invalid subgoal name."

-- -- getDisallowedVars :: String -> ProverState (S.Set String)
-- -- getDisallowedVars goalName = do
-- --     curDisjointGoals <- disjointSubgoals <$> getGoal goalName
-- --     curSubgoals <- subgoals <$> ST.get
-- --     -- Get the subgoals and their reserved variables if the subgoal exists. Then union all reserved variables.
-- --     return $ L.foldl' S.union S.empty (maybe S.empty reservedVars . (`Data.Map.lookup` curSubgoals) <$> curDisjointGoals)

updateGoal :: String -> Subgoal -> ProverState ()
updateGoal goalName newGoalState = do
    curState <- ST.get
    ST.put (curState { subgoals = Data.Map.insert goalName newGoalState (subgoals curState) })

removeVarsFromSequent :: [String] -> Sequent -> ProverState Sequent
removeVarsFromSequent varsToRem seq =
    if channel seq `L.elem` varsToRem
    then tacError $ "Cannot reserve the channel of the sequent: " ++ seqToS seq
    else return $ seq { linearContext = L.foldl (flip Data.Map.delete) (linearContext seq) (S.fromList varsToRem) }

removeVarsFromSubgoal :: [String] -> (String, Subgoal) -> ProverState (String, Subgoal)
removeVarsFromSubgoal varsToRem (x, sg) = if isUsed sg
    then return (x, sg)
    else (do
        newSeq <- removeVarsFromSequent varsToRem (sequent sg)
        return (x, sg { sequent = newSeq }))

reserveVars :: [String] -> ProverState ()
reserveVars = reserveVarsKnownUnavailable S.empty

reserveVarsKnownUnavailable :: S.Set String -> [String] -> ProverState ()
reserveVarsKnownUnavailable unavailableVarsArg varsToRes = do
    curSubgoalName <- ST.gets curSubgoal
    curSubgoalData <- getCurrentSubgoal
    unavailableVars <- if unavailableVarsArg == S.empty then ST.gets (getUnavailableVarsForSubgoal curSubgoalName) else return unavailableVarsArg
    let newSgData = curSubgoalData { reservedVars = reservedVars curSubgoalData `S.union` S.fromList varsToRes}
    if L.any (`S.member` unavailableVars) varsToRes
    then tacError "Variables already reserved, and should not be available to use."
    else ST.modify (\s -> s { subgoals = Data.Map.insert curSubgoalName newSgData (subgoals s) })

buildJustification0 :: Proof -> Justification
buildJustification0 = return

buildJustification1 :: String -> (Proof -> Proof) -> Justification
buildJustification1 sg p = do
    curSubgoals <- ST.gets subgoals
    case Data.Map.lookup sg curSubgoals of
        (Just sg) -> do
            jst <- subgoalJustification sg
            return $ p jst
        _ -> tacError $ "Child subgoal lost " ++ sg

buildJustification2 :: String -> String -> (Proof -> Proof -> Proof) -> Justification
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
useCurrentSubgoal :: BranchType -> Justification -> ProverState ()
useCurrentSubgoal bt j = do
    curState <- ST.get
    let curSubgoals = subgoals curState
        curSubgoalMaybe = Data.Map.lookup (curSubgoal curState) curSubgoals
    curSubgoalObj <- liftMaybeWithError ("Cannot find current subgoal " ++ curSubgoal curState) curSubgoalMaybe
    ST.modify (\s -> s {
        subgoals = Data.Map.insert (curSubgoal curState) (curSubgoalObj { subgoalJustification = j, expanded = Just bt }) (subgoals s),
        openGoalStack = L.drop 1 (openGoalStack curState) }) -- subgoal is expanded and popped off.

getCurrentSubgoal :: ProverState (Subgoal)
getCurrentSubgoal = do
    curSubgoalName <- ST.gets curSubgoal
    curSubgoalMaybe <- Data.Map.lookup curSubgoalName <$> ST.gets subgoals
    liftMaybeWithError ("Cannot find current subgoal " ++ curSubgoalName) curSubgoalMaybe

getCurrentSequent :: ProverState Sequent
getCurrentSequent = sequent <$> getCurrentSubgoal

{-|
    Create a new subgoal in the state pointing to the current subgoal as its
    previous. Puts the new goal just below the current open goal. Call
    useCurrentSubgoal after this.
-}
createNewSubgoal :: Sequent -> ProverState String
createNewSubgoal seq = do
    freshGoal <- getFreshSubgoalName
    curSubgoalName <- ST.gets curSubgoal
    curSubgoalData <- getCurrentSubgoal
    let newSubgoal = Subgoal { sequent = seq, prevGoal = curSubgoalName, nextGoals = [], subgoalJustification = tacError "No justification", expanded = Nothing, inProgressFunctionalProof = Nothing, reservedVars = S.empty }
        newCurSubgoalData = curSubgoalData { nextGoals = freshGoal:nextGoals curSubgoalData }
    ST.modify (\s -> s { subgoals = Data.Map.insert curSubgoalName newCurSubgoalData (Data.Map.insert freshGoal newSubgoal (subgoals s)), openGoalStack = (head (openGoalStack s)):(freshGoal:tail (openGoalStack s)) })
    return freshGoal

idTac :: String -> Tactic
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

idATac :: Tactic
idATac = do
    seq <- getCurrentSequent
    curSg <- ST.gets curSubgoal
    unavailableVars <- getUnavailableVarsForSubgoal curSg <$> ST.get
    case L.filter (\(k, p) -> not (S.member k unavailableVars) && p == goalProposition seq) . Data.Map.toList $ linearContext seq of
        ((x,p):rest) -> do
            reserveVarsKnownUnavailable unavailableVars [x]
            xName <- lookupVarName x
            zName <- lookupVarName (channel seq)
            useCurrentSubgoal Trunk (buildJustification0 $ IdRule xName zName (tyVarContext seq) (fnContext seq) (unrestrictedContext seq) (recursiveBindings seq) p)
            return "IdA tactic applied."
        [] -> tacError $ "Could not find " ++ show (goalProposition seq) ++ " in the linear context."

functionalTermRightTac :: FunctionalProof -> Tactic
functionalTermRightTac fp = do
    seq <- getCurrentSequent
    fpConcl <- liftEither $ verifyFunctionalProofM fp
    case goalProposition seq of
        Lift t -> if t == goalType fpConcl then (do
            zName <- lookupVarName $ channel seq
            useCurrentSubgoal Trunk (buildJustification0 $ FunctionalTermRightRule zName fp (tyVarContext seq) (unrestrictedContext seq) (recursiveBindings seq))
            return "Functional term right side tactic applied")
            else tacError $ "Mismatched proof result and goal term:\nEXPECTED: " ++ show t ++ "\nGOT: " ++ show (goalType fpConcl)
        _ -> tacError "Cannot apply tactic to goal."

functionalTermLeftTac :: S.Set String -> String -> Tactic
functionalTermLeftTac unavailableVars x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x (linearContext seq) of
        (Just (Lift t)) -> do
            -- Get fresh vars needed
            -- Reserve vars
            reserveVarsKnownUnavailable unavailableVars [x]
            x1Name <- lookupVarName x
            newFnCtx <- liftEither $ safeInsert x1Name t $ fnContext seq
            -- Make new subgoals
            freshGoal <- createNewSubgoal $ seq { fnContext = newFnCtx, linearContext = Data.Map.delete x $ linearContext seq }
            -- Make justification lookup unique var names
            -- Mark subgoal as used and justify
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ FunctionalTermLeftRule x1Name
            return "Functional term left side tactic applied."
        Just _ -> tacError "Not a functional term."
        _ -> tacError $ "Could not find " ++ x ++ " in the linear context."

functionalTermLeftTacA :: Tactic
functionalTermLeftTacA = leftTacA functionalTermLeftTac (\case Lift _ -> True; _ -> False)

impliesRightTac :: Tactic
impliesRightTac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        Implication a b -> do
            x <- getFreshVar
            freshGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert x a $ linearContext seq, goalProposition = b }
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ ImpliesRightRule x
            return "Implies right side tactic applied"
        _ -> tacError "Not an implication"

impliesLeftTac :: S.Set String -> String -> Tactic
impliesLeftTac unavailableVars x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x (linearContext seq) of
        Just (Implication a b) -> (do
            reserveVarsKnownUnavailable unavailableVars [x]
            y <- getFreshVar
            xName <- lookupVarName x
            freshGoalY <- createNewSubgoal $ seq { linearContext = Data.Map.delete x $ linearContext seq, goalProposition = a, channel = y }
            freshGoalX <- createNewSubgoal $ seq { linearContext = Data.Map.insert x b $ linearContext seq }
            useCurrentSubgoal Multiplicative . buildJustification2 freshGoalY freshGoalX $ ImpliesLeftRule xName
            return "Implies left side tactic applied.")
        Just _ -> tacError "Cannot apply to non-implication proposition."
        Nothing -> tacError $ "Cannot find " ++ x ++ " in linear context."

leftTacA :: (S.Set String -> String -> Tactic) -> (Proposition -> Bool) -> Tactic
leftTacA tac test = do
    seq <- getCurrentSequent
    sgName <- ST.gets curSubgoal
    unavailableVars <- ST.gets (getUnavailableVarsForSubgoal sgName)
    let candidateProps = Data.Map.keys (Data.Map.filterWithKey (\k v -> not . S.member k $ unavailableVars) (Data.Map.filter test (linearContext seq)))
    if L.null candidateProps then tacError "No propositions in the linear context of the correct form!" else tac unavailableVars (head candidateProps)

impliesLeftTacA :: Tactic
impliesLeftTacA = leftTacA impliesLeftTac (\case Implication _ _ -> True; _ -> False)

unitRightTac :: Tactic
unitRightTac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        Unit -> (do
            --reserveVars [channel seq]
            channelName <- lookupVarName (channel seq)
            useCurrentSubgoal Trunk (return $ UnitRightRule channelName (tyVarContext seq) (fnContext seq) (unrestrictedContext seq) (recursiveBindings seq))
            return "Unit right side tactic applied.")
        _ -> tacError "Cannot apply to non-implication proposition."

unitLeftTac :: S.Set String -> String -> Tactic
unitLeftTac unavailableVars x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x (linearContext seq) of
        Just Unit -> do
            -- Get fresh vars needed
            -- Reserve vars
            reserveVarsKnownUnavailable unavailableVars [x]
            -- Make new subgoals
            freshGoal <- createNewSubgoal $ seq { linearContext = Data.Map.delete x $ linearContext seq }
            -- Make justification lookup unique var names
            xName <- lookupVarName x
            -- Mark subgoal as used and justify
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ UnitLeftRule xName
            return "Unit left side tactic applied."
        Just _ -> tacError "Not a Unit proposition."
        _ -> tacError $ "Could not find " ++ x ++ " in the linear context."

unitLeftTacA :: Tactic
unitLeftTacA = leftTacA unitLeftTac (\case Unit -> True; _ -> False)

replicationRightTac :: Tactic
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
            return "Replication right side tactic applied."
        _ -> tacError "Not a Replication proposition."

replicationLeftTac :: S.Set String -> String -> Tactic
replicationLeftTac unavailableVars x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (Replication a) -> do
            -- Get fresh vars needed
            -- Reserve vars
            reserveVarsKnownUnavailable unavailableVars [x]
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

replicationLeftTacA :: Tactic
replicationLeftTacA = leftTacA replicationLeftTac (\case Replication _ -> True; _ -> False)

copyTac :: String -> Maybe String -> Tactic
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

withRightTac :: Tactic
withRightTac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        With p1 p2 -> do
            zName <- lookupVarName $ channel seq
            --reserveVars [channel seq]
            leftGoal <- createNewSubgoal $ seq { goalProposition = p1 }
            rightGoal <- createNewSubgoal $ seq { goalProposition = p2 }
            useCurrentSubgoal Additive $ buildJustification2 leftGoal rightGoal WithRightRule
            return "With right side tactic applied."
        _ -> tacError "Cannot apply tactic to non-with proposition."

withLeft1Tac :: S.Set String -> String -> Tactic
withLeft1Tac unavailableVars x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (With p1 p2) -> do
            xName <- lookupVarName x
            reserveVarsKnownUnavailable unavailableVars [x]
            newGoalName <- createNewSubgoal $ seq { linearContext = Data.Map.insert x p1 $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 newGoalName $ WithLeft1Rule xName p2
            return "With left side 1 tactic applied."
        _ -> tacError "Cannot apply tactic to non-with proposition."

withLeft1TacA :: Tactic
withLeft1TacA = leftTacA withLeft1Tac (\case With _ _ -> True; _ -> False)

withLeft2Tac :: S.Set String -> String -> Tactic
withLeft2Tac unavailableVars x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (With p1 p2) -> do
            xName <- lookupVarName x
            reserveVarsKnownUnavailable unavailableVars [x]
            newGoalName <- createNewSubgoal $ seq { linearContext = Data.Map.insert x p2 $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 newGoalName $ WithLeft2Rule xName p1
            return "With left side 2 tactic applied."
        _ -> tacError "Cannot apply to non-with proposition."

withLeft2TacA :: Tactic
withLeft2TacA = leftTacA withLeft2Tac (\case With _ _ -> True; _ -> False)

tensorRightTac :: Tactic
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

tensorLeftTac :: S.Set String -> String -> Tactic
tensorLeftTac unavailableVars x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (Tensor a b) -> do
            reserveVarsKnownUnavailable unavailableVars [x]
            xName <- lookupVarName x
            y <- getFreshVar
            freshGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert y a . Data.Map.insert x b . Data.Map.delete x $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ TensorLeftRule xName y
            return "Tensor left side tactic applied"
        Just _ -> tacError "Not a tensor"
        _ -> tacError $ "Could not find " ++ x ++ "in the linear context"

tensorLeftTacA :: Tactic
tensorLeftTacA = leftTacA tensorLeftTac (\case Tensor _ _ -> True; _ -> False)

plusRight1Tac :: Tactic
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

plusRight2Tac :: Tactic
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

plusLeftTac :: S.Set String -> String -> Tactic
plusLeftTac unavailableVars x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (Plus p1 p2) -> do
            xName <- lookupVarName x
            reserveVarsKnownUnavailable unavailableVars [x]
            zName <- lookupVarName $ channel seq
            leftGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert x p1 (linearContext seq) }
            rightGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert x p2 (linearContext seq) }
            useCurrentSubgoal Additive $ buildJustification2 leftGoal rightGoal $ PlusLeftRule xName
            return "Plus left side tactic applied."
        Just _ -> tacError "Cannot apply to non-plus proposition"
        Nothing -> tacError $ "Could not find " ++ x ++ " in linear context."

plusLeftTacA :: Tactic
plusLeftTacA = leftTacA plusLeftTac (\case Plus _ _ -> True; _ -> False)

forallRightTac :: Tactic
forallRightTac = do
    seq <- getCurrentSequent
    case goalProposition seq of
        Forall x t p -> do
            zName <- lookupVarName $ channel seq
            newFnCtx <- liftEither $ safeInsert x t $ fnContext seq
            newGoal <- createNewSubgoal $ seq { fnContext = newFnCtx, goalProposition = p }
            useCurrentSubgoal Trunk . buildJustification1 newGoal $ ForallRightRule x
            return "Forall right side tactic applied."
        _ -> tacError "Cannot apply to non-forall proposition."

forallLeftTac :: String -> FunctionalProof -> Tactic
forallLeftTac x fp = do
    seq <- getCurrentSequent
    fpConcl <- liftEither $ verifyFunctionalProofM fp
    case Data.Map.lookup x $ linearContext seq of
        Just (Forall y t p) -> if t == goalType fpConcl then (do
            reserveVars [x]
            xName <- lookupVarName x
            freshGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert x (substVarTerm p (goalTerm fpConcl) y) $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ ForallLeftRule xName y fp
            return "Forall left side tactic applied.")
            else tacError $ "Mismatched proof result and goal term:\nEXPECTED: " ++ show t ++ "\nGOT: " ++ show (goalType fpConcl)
        Just _ -> tacError "Cannot apply to non-forall proposition."
        _ -> tacError $ "Could not find " ++ x ++ " in the linear context."

existsRightTac :: FunctionalProof -> Tactic
existsRightTac fp = do
    seq <- getCurrentSequent
    fpConcl <- liftEither $ verifyFunctionalProofM fp
    case goalProposition seq of
        Exists x t p -> if t == goalType fpConcl then (do
            zName <- lookupVarName $ channel seq
            freshGoal <- createNewSubgoal $ seq { goalProposition = substVarTerm p (goalTerm fpConcl) x }
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ ExistsRightRule x fp
            return "Exists right side tactic applied.")
            else tacError $ "Mismatched proof result and goal term:\nEXPECTED: " ++ show t ++ "\nGOT: " ++ show (goalType fpConcl)
        _ -> tacError "Cannot apply to non-exists proposition."

existsLeftTac :: S.Set String -> String -> Tactic
existsLeftTac unavailableVars x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (Exists y t p) -> do
            reserveVarsKnownUnavailable unavailableVars [x]
            xName <- lookupVarName x
            freshY <- getFreshVarAttempt y
            let newP = substVarProp p freshY y
            newFnCtx <- liftEither $ safeInsert freshY t $ fnContext seq
            newGoal <- createNewSubgoal $ seq { fnContext = newFnCtx, linearContext = Data.Map.insert x newP $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 newGoal $ ExistsLeftRule xName freshY
            return "Exists left side tactic applied."
        Just _ -> tacError "Cannot apply to non-exists proposition."
        _ -> tacError "Variable doesn't exist"

existsLeftTacA :: Tactic
existsLeftTacA = leftTacA existsLeftTac (\case Exists {} -> True; _ -> False)

forallRight2Tac :: Tactic
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

forallLeft2Tac :: String -> Proposition -> Tactic
forallLeft2Tac x bWithDecls = do
    seq <- getCurrentSequent
    b <- substTyDeclsM bWithDecls
    _ <- case wellFormedType ((tyVarContext seq) `S.union` (S.fromList ((\v -> bindingTyVar v) . snd . snd <$> Data.Map.toList (recursiveBindings seq)))) b of Left e ->tacError (propToS b ++ " is not a well-formed type: " ++ e) ; Right () -> return ()
    case Data.Map.lookup x $ linearContext seq of
        Just (Forall2 y p) -> do
            reserveVars [x]
            xName <- lookupVarName x
            invalidateNameCache
            freshGoal <- createNewSubgoal $ seq { linearContext = Data.Map.insert x (substVarType p b y) $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ ForallLeft2Rule xName y b
            return "Forall second order left side tactic applied."
        Just _ -> tacError "Cannot apply to non-forall second order proposition."
        _ -> tacError $ "Could not find " ++ x ++ " in the linear context."

existsRight2Tac :: Proposition -> Tactic
existsRight2Tac bWithDecls = do
    seq <- getCurrentSequent
    b <- substTyDeclsM bWithDecls
    _ <- case wellFormedType (((tyVarContext seq) `S.union` (S.fromList ((\v -> bindingTyVar v) . snd . snd <$> Data.Map.toList (recursiveBindings seq))))) b of Left e ->tacError (propToS b ++ " is not a well-formed type: " ++ e) ; Right () -> return ()
    case goalProposition seq of
        Exists2 y p -> do
            --reserveVars [(channel seq)]
            zName <- lookupVarName (channel seq)
            invalidateNameCache
            freshGoal <- createNewSubgoal $ seq { goalProposition = substVarType p b y }
            useCurrentSubgoal Trunk . buildJustification1 freshGoal $ ExistsRight2Rule y b
            return "Exists second order right side tactic applied."
        _ -> tacError "Cannot apply to non-forall second order proposition."

existsLeft2Tac :: S.Set String -> String -> Tactic
existsLeft2Tac unavailableVars x = do
    seq <- getCurrentSequent
    case Data.Map.lookup x $ linearContext seq of
        Just (Forall2 y p) -> do
            reserveVarsKnownUnavailable unavailableVars [x]
            xName <- lookupVarName $ x
            newGoal <- createNewSubgoal $ seq { tyVarContext = S.insert x $ tyVarContext seq, linearContext = Data.Map.insert x p $ linearContext seq }
            useCurrentSubgoal Trunk . buildJustification1 newGoal $ ExistsLeft2Rule xName y
            return "Forall second order right side tactic applied."
        Just _ -> tacError "Cannot apply to non-forall second order proposition."
        _ -> tacError $ "Could not find " ++ x ++ " in the linear context."

existsLeft2TacA :: Tactic
existsLeft2TacA = leftTacA existsLeft2Tac (\case Exists2 {} -> True; _ -> False)

cutTac :: Proposition -> Tactic
cutTac pWithDecls = do
    seq <- getCurrentSequent
    p <- substTyDeclsM pWithDecls
    x <- getFreshVar
    zName <- lookupVarName $ channel seq
    invalidateNameCache
    freshGoalY <- createNewSubgoal $ seq { goalProposition = p, channel = x }
    freshGoalZ <- createNewSubgoal $ seq { linearContext = Data.Map.insert x p $ linearContext seq }
    useCurrentSubgoal Cut . buildJustification2 freshGoalY freshGoalZ $ CutRule
    return "Cut tactic applied."

cutReplicationTac :: Proposition -> Tactic
cutReplicationTac pWithDecls = do
    seq <- getCurrentSequent
    p <- substTyDeclsM pWithDecls
    x <- getFreshVar
    u <- getFreshVar
    zName <- lookupVarName $ channel seq
    invalidateNameCache
    freshGoalY <- createNewSubgoal $ seq { linearContext = Data.Map.empty, goalProposition = p, channel = x }
    freshGoalZ <- createNewSubgoal $ seq { unrestrictedContext = Data.Map.insert u p $ unrestrictedContext seq }
    useCurrentSubgoal Multiplicative . buildJustification2 freshGoalY freshGoalZ $ CutRule
    return "Cut replication tactic applied."

nuRightTac :: String -> [String] -> [String] -> Tactic
nuRightTac x ys zs = do
    seq <- getCurrentSequent
    case goalProposition seq of
        TyNu y a -> (do
            let yzs = zip ys zs
                newTyVarCtx = L.foldl (\acc (y, z) -> substVarTyVarContext acc y z) (tyVarContext seq) yzs
                newFnCtx = L.foldl (\acc (y, z) -> renameVarInFnCtx S.empty acc y z) (fnContext seq) yzs
                newUC = L.foldl (\acc (y, z) -> substVarContext acc y z) (unrestrictedContext seq) yzs
                newLC = L.foldl (\acc (y, z) -> substVarContext acc y z) (linearContext seq) yzs
                newChan = L.foldl (\acc (y, z) -> if acc == z then y else acc) (channel seq) yzs
                bindingSeq = BindingSequent { bindingTyVarContext = newTyVarCtx, bindingFnContext = newFnCtx, bindingUC = newUC, bindingLC = newLC, bindingChan = newChan, bindingTyVar = y }
            freshGoalName <- createNewSubgoal $ seq { recursiveBindings = Data.Map.insert x (ys, bindingSeq) $ recursiveBindings seq, goalProposition = a }
            useCurrentSubgoal Trunk . buildJustification1 freshGoalName $ TyNuRightRule x zs
            return "Nu right tactic applied.")
        _ -> tacError "Cannot apply to non-Nu proposition."

nuLeftTac :: S.Set String -> String -> Tactic
nuLeftTac unavailableVars c = do
    seq <- getCurrentSequent
    case Data.Map.lookup c (linearContext seq) of
        Just (TyNu x a) -> (do
            reserveVarsKnownUnavailable unavailableVars [c]
            freshGoalName <- createNewSubgoal $ seq { linearContext = Data.Map.insert c (unfoldRec a x a) $ linearContext seq}
            useCurrentSubgoal Trunk . buildJustification1 freshGoalName $ TyNuLeftRule c x
            return "Nu left tactic applied.")
        Just _ -> tacError "Cannot apply to non-Nu proposition."
        Nothing -> tacError $ "Cannot find " ++ c ++ " in linear context."

nuLeftTacA :: Tactic
nuLeftTacA = leftTacA nuLeftTac (\case TyNu {} -> True; _ -> False)

tyVarTac :: String -> [String] -> Tactic
tyVarTac x zs = do
    seq <- getCurrentSequent
    curSgName <- ST.gets curSubgoal
    case Data.Map.lookup x (recursiveBindings seq) of
        Just (ys, xSeq) -> (do
            when (L.length zs /= L.length ys) (tacError "Invalid number of arguments")
            unavailVars <- getUnavailableVarsForSubgoal curSgName <$> ST.get
            let yzs = zip ys zs
                boundSeqRenamedTyVarContext = L.foldl (\acc (y, z) -> substVarTyVarContext acc z y) (bindingTyVarContext xSeq) yzs
                boundSeqRenamedFnContext = L.foldl (\acc (y, z) -> renameVarInFnCtx S.empty acc z y) (bindingFnContext xSeq) yzs
                boundSeqRenamedUCContext = L.foldl (\acc (y, z) -> substVarContext acc z y) (bindingUC xSeq) yzs
                boundSeqRenamedLCContext = L.foldl (\acc (y, z) -> substVarContext acc z y) (bindingLC xSeq) yzs
                boundSeqRenamedChannel = L.foldl (\curVar (y, z) -> if curVar == y then z else curVar) (bindingChan xSeq) yzs
            when (boundSeqRenamedTyVarContext /= tyVarContext seq) $ tacError "Invalid tyvar contexts."
            when (boundSeqRenamedFnContext /= fnContext seq) $ tacError $ "Invalid functional contexts: " ++ show (ctxToList boundSeqRenamedFnContext) ++ " and " ++ show (ctxToList (fnContext seq))
            when (boundSeqRenamedUCContext /= unrestrictedContext seq) $ tacError "Invalid unrestricted contexts."
            when (boundSeqRenamedLCContext /= S.foldl (flip Data.Map.delete) (linearContext seq) unavailVars) $ tacError ("Invalid linear contexts:\n" ++ show boundSeqRenamedLCContext ++ "\n\n" ++ show (S.foldl (flip Data.Map.delete) (linearContext seq) unavailVars))
            when (boundSeqRenamedChannel /= channel seq) $ tacError "Invalid channel."
            useCurrentSubgoal Trunk . buildJustification0 $ TyVarRule (recursiveBindings seq) x zs
            return "Type variable tactic applied.")
        Nothing -> tacError $ "Cannot find " ++ x ++ " in recursive bindings."

replWeakenTac :: String -> Tactic
replWeakenTac u = do
    seq <- getCurrentSequent
    _ <- (if Data.Map.member u (unrestrictedContext seq) then return () else tacError $ u ++ " is not a member of the unrestricted context.")
    newSgName <- createNewSubgoal $ seq { unrestrictedContext = Data.Map.delete u (unrestrictedContext seq) }
    useCurrentSubgoal Trunk . buildJustification1 newSgName $ ReplWeakening u (unrestrictedContext seq Data.Map.! u)
    return "Replication weakening tactic applied."

fnWeakenTac :: String -> Tactic
fnWeakenTac t = do
    seq <- getCurrentSequent
    _ <- (if ctxMember t (fnContext seq) then return () else tacError $ t ++ " is not a member of the functional context.")
    tTy <- liftEither $ ctxEitherLookup t $ fnContext seq
    newFnCtx <- liftEither $ ctxDelete t $ fnContext seq
    newSgName <- createNewSubgoal $ seq { fnContext = newFnCtx }
    useCurrentSubgoal Trunk . buildJustification1 newSgName $ FnWeakening t tTy
    return "Functional weakening tactic applied."

useProofTac :: String -> Tactic
useProofTac tName = do
    seq <- getCurrentSequent
    ts <- Data.Map.map proofObject <$> ST.gets theorems
    case verifyProofM <$> Data.Map.lookup tName ts of
        Nothing -> tacError "Could not find the provided theorem."
        Just (Left e) -> tacError $ "Error in conclusion: " ++ e
        Just (Right (_, conclusion)) -> (do
            if conclusion == seq
            then useCurrentSubgoal Trunk . buildJustification0 $ ts Data.Map.! tName
            else tacError ("Conclusion of the theorem does not match the current goal:\nExpected: " ++ seqToS seq ++ "\nFound: " ++ seqToS conclusion)
            return $ "Applied theorem " ++ tName)

useModuleProofTac :: String -> String -> Tactic
useModuleProofTac mName tName = do
    seq <- getCurrentSequent
    ms <- ST.gets loadedModules
    let t = proofObject <$> (Data.Map.lookup mName ms >>= Data.Map.lookup tName)
    case verifyProofM <$> t of
        Nothing -> tacError "Could not find the provided theorem."
        Just (Left e) -> tacError $ "Error in conclusion: " ++ e
        Just (Right (_, conclusion)) -> (do
            if conclusion == seq
            then useCurrentSubgoal Trunk . buildJustification0 $ proofObject ((ms Data.Map.! mName) Data.Map.! tName)
            else tacError ("Conclusion of the theorem does not match the current goal:\nExpected: " ++ seqToS seq ++ "\nFound: " ++ seqToS conclusion)
            return $ "Applied theorem " ++ mName ++ "." ++ tName)

{-|
    Returns the renaming required for assumptions. The empty string is the
    renaming if searching fails.
-}
getAssumptionRenamingForTheorem :: Sequent -> Sequent -> [(String, String)]
getAssumptionRenamingForTheorem theoremSeq curSeq = Data.Map.foldlWithKey' (\acc k v -> (k, getMatch acc v):acc) [] $ linearContext theoremSeq
        where
            availAssumptions = linearContext curSeq
            getMatches acc prop = Data.Map.toList (Data.Map.filterWithKey (\k v -> v == prop && (k `L.notElem` (fst <$> acc))) availAssumptions)
            getMatch acc prop = if L.null (getMatches acc prop) then "" else fst . L.head $ getMatches acc prop

applyAssumptionRenamingForTheorem :: [(String, String)] -> Proof -> Proof
applyAssumptionRenamingForTheorem renaming p = L.foldl' (\newP (prev, next) -> renameVarInProof newP next prev) p renaming

cutLinearTheoremTac :: String -> Tactic
cutLinearTheoremTac theoremName = do
    seq <- getCurrentSequent
    ms <- ST.gets loadedModules
    ts <- ST.gets theorems
    let mName = L.takeWhile (/= '.') theoremName
        tName = L.drop 1 . L.dropWhile (/= '.') $ theoremName
        maybeTheorem = if '.' `L.elem` theoremName then (proofObject <$> (Data.Map.lookup mName ms >>= Data.Map.lookup tName)) else (Data.Map.lookup theoremName (proofObject <$> ts))
    theorem <- case maybeTheorem of Nothing -> tacError "Could not find the theorem."; Just t -> return t
    conclusion <- case verifyProofM theorem of Left e -> tacError ("Could not get conclusion of theorem: " ++ e); Right (_, c) -> return c
    curNames <- getProofStateNames
    let otherNames = getProofNames theorem
        allNames = S.union otherNames curNames
        freshName = getFreshName allNames
    newChan <- getFreshVarAttempt freshName
    let channelRenamedProof = renameVarInProof theorem newChan (channel conclusion)
    (_, channelRenamedProofSeq) <- liftEither $ verifyProofM channelRenamedProof
    let assumptionNamingRequirements = getAssumptionRenamingForTheorem channelRenamedProofSeq seq
        newRenamedProof = applyAssumptionRenamingForTheorem assumptionNamingRequirements  channelRenamedProof
        weakenedUnrestrictedProof = L.foldl' (\proof (k, prop) -> ReplWeakening k prop proof) newRenamedProof (Data.Map.toList (unrestrictedContext seq)) -- Add everything needed for the unrestricted context.
        weakenedFnProof = L.foldl' (\proof (k, term) -> FnWeakening k term proof) weakenedUnrestrictedProof (reverse (ctxToList (fnContext seq))) -- Add everything needed for the functional context.
        weakenedTyVarProof = L.foldl' (\proof (k) -> TyVarWeakening k proof) weakenedFnProof (S.toList (tyVarContext seq)) -- Add everything needed for the type variable context.
        weakenedRecBindProof = L.foldl' (\proof (k, b) -> RecBindingWeakening k b proof) weakenedTyVarProof (Data.Map.toList (recursiveBindings seq)) -- Add everything needed for the recursive binding context.
    when (L.any (\(prev, next) -> next == "") assumptionNamingRequirements) (tacError "Could not find the necessary assumptions to use for the theorem!")
    newConclusion <- case verifyProofM weakenedRecBindProof of Left e -> tacError ("Could not get conclusion of the renamed variable theorem: " ++ e); Right (_, c) -> return c
    reserveVars (snd <$> assumptionNamingRequirements)
    let deletedReservedFromLinear = L.foldl' (flip Data.Map.delete) (linearContext seq) (snd <$> assumptionNamingRequirements)
    freshGoal <- createNewSubgoal (seq { linearContext = Data.Map.insert newChan (goalProposition newConclusion) deletedReservedFromLinear })
    useCurrentSubgoal Multiplicative . buildJustification1 freshGoal $ CutRule weakenedRecBindProof
    invalidateNameCache
    return $ "Linear theorem cut tactic applied: " ++ propToS (goalProposition conclusion)

cutProcessAssumptionTac :: String -> Tactic
cutProcessAssumptionTac n = do
    seq <- getCurrentSequent
    processAssumptions <- ST.gets procAssumptions
    assumption <- case L.dropWhile (\pa -> fst pa /= n) processAssumptions of [] -> tacError "Could not find the assumed process"; (h:_) -> return h
    curNames <- getProofStateNames
    when (n `S.member` curNames) $ tacError ("Name clash for " ++ n)
    let otherNames = propNames (snd assumption)
        allNames = S.union otherNames curNames
        freshName = getFreshName allNames
    newChan <- getFreshVarAttempt freshName
    freshGoal <- createNewSubgoal (seq { linearContext = Data.Map.insert newChan (snd assumption) (linearContext seq) })
    useCurrentSubgoal Multiplicative . buildJustification1 freshGoal $ ProcessFiatRule n newChan (snd assumption)
    invalidateNameCache
    return "Assumed process cut in."

weakenTac :: String -> Tactic
weakenTac t = altTactical (replWeakenTac t) (fnWeakenTac t)

byProcessTac :: Process -> Tactic
byProcessTac p = do
    seq <- getCurrentSequent
    curSg <- ST.gets curSubgoal
    curS <- ST.get
    let
        unavailableVars = getUnavailableVarsForSubgoal curSg curS
        typeCheckSeq = seq { linearContext = S.foldl (flip Data.Map.delete) (linearContext seq) unavailableVars}
    procProof <- case typeCheckProcessUnderSequent seq p of Right res -> return res; Left e -> tacError e
    newSeq <- case verifyProofM procProof of Right (_, newSeq) -> return newSeq; Left e -> tacError ("Error verifying proof of type derivation: " ++ e)
    unless (newSeq == seq) $ tacError ("Sequents are not the same in subgoal and derivation: " ++ seqToS seq ++ "\n\n" ++ seqToS newSeq) -- TODO allow subset of linear context.
    useCurrentSubgoal Trunk . buildJustification0 $ procProof
    return "Process is the correct type."


holeTac :: Tactic
holeTac = do
    seq <- getCurrentSequent
    useCurrentSubgoal Trunk . buildJustification0 $ HoleRule (tyVarContext seq) (fnContext seq) (unrestrictedContext seq) (linearContext seq) (recursiveBindings seq) (channel seq) (goalProposition seq)
    return "Hole applied."

thenTactical :: Tactic -> Tactic -> Tactic
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

skipTactical :: Tactic
skipTactical = do
    seq <- getCurrentSequent
    newGoal <- createNewSubgoal seq
    useCurrentSubgoal Trunk . buildJustification1 newGoal $ id
    return "Skip applied."

altTactical :: Tactic -> Tactic -> Tactic
altTactical t1 t2 = t1 `mplus` t2

repeatTactical :: Tactic -> Tactic
repeatTactical t = t `thenTactical` (repeatTactical t `altTactical` return "Repeat applied")

initCleanState :: String -> ProofState
initCleanState mName =
    let
        channelVar = []
        linearVars = []
        unrestrictedVars = []
        fnVars = []
        allVars = []
    in
        S { subgoals = Data.Map.empty
        , outputs = ["Ready to begin!"]
        , curTheoremName = ""
        , curModuleName = mName
        , theorems = Data.Map.empty
        , loadedModules = Data.Map.empty
        , openGoalStack = []
        , cachedProofStateNames = S.empty
        , newSubgoalNameList = tail allSubgoalNames
        , cachedVarNames = namesInOrder
        , stypeDecls = []
        , fnAssumptions = emptyContext
        , procAssumptions = []
        , errors = []
        , stypeAssumptions = [] }

runProofState :: ProverState a -> ProofState -> (Either String (a, ProofState))
runProofState a s = runIdentity $ E.runExceptT $ ST.runStateT a s

applyTactic :: ProofState -> Tactic -> ProofState
applyTactic s t = case runProofState t s of
    Right (notif, newState) -> newState { outputs = notif:outputs newState}
    Left e -> s { errors = e:errors s }

theorem :: ProofState -> [Proposition] -> String -> Proposition -> ProofState
theorem s ts n p =
    let
        typeSynonyms = stypeDecls s
        sessionsToConsume = substTyDecls typeSynonyms <$> ts
        goalProp = (substTyDecls typeSynonyms p)
        goal = initializeProof (initializeSequent (stypeAssumptions s) (fnAssumptions s) sessionsToConsume goalProp)
        wellFormedGoal = wellFormedTypeWithFreeVars goalProp
    in
        case wellFormedGoal of
            Left e -> s { errors = ("Proposition is not well-formed! " ++ e):errors s }
            Right () -> declCheck n s (s {
                subgoals = singleton "?a" goal
                , outputs = "New theorem started":outputs s
                , curTheoremName = n
                , openGoalStack = ["?a"]
                , cachedProofStateNames = S.empty
                , newSubgoalNameList = tail allSubgoalNames
                , cachedVarNames = namesInOrder })

runAndVerifyJustification :: ProofState -> Either String (Proof, ProofState)
runAndVerifyJustification s = case runProofState (subgoalJustification ( subgoals s ! "?a")) s of
    Right (p, s) -> case verifyProofM p of Right _ -> Right (p, s); Left e ->  Left e
    Left e -> Left e

extractFromJustification :: ProofState -> Either String (Process, Sequent)
extractFromJustification s = case runProofState (subgoalJustification ( subgoals s ! "?a")) s of
    Right (p, s) -> verifyProofM p
    Left err -> Left err

done :: ProofState -> ProofState
done res = case runAndVerifyJustification res of
    Right (p, s) -> s { theorems = Data.Map.insert (curTheoremName s) (Theorem p (fromIntegral . L.length . Data.Map.keys $ subgoals s)) (theorems s),  outputs = ("Theorem complete: " ++ curTheoremName s):outputs res}
    Left err -> res { outputs = ("Could not verify proof: " ++ err):outputs res, errors = ("Could not verify proof: " ++ err):errors res }

-- DSL

_Init :: String -> ProofState
_Init = initCleanState

_Theorem :: ProofState -> [Proposition] -> String -> Proposition -> ProofState
_Theorem = theorem

_Done :: ProofState -> ProofState
_Done = done

_QED :: ProofState -> ProofState
_QED = _Done

_Extract :: ProofState -> String -> ProofState
_Extract s tName =
    let
        extractor p = case verifyProofM p of
            Left e -> s { outputs = e:outputs s }
            Right (prc, seq) -> s { outputs = pToS prc:outputs s }
    in
        case Data.Map.lookup tName (theorems s) of
            Nothing -> case Data.Map.lookup (L.takeWhile (/= '.') tName) (loadedModules s) of
                Nothing -> s { outputs = "Could not find the supplied theorem.":outputs s }
                Just m -> maybe
                  s {outputs = "Could not find the supplied theorem." : outputs s}
                  extractor (proofObject <$> (Data.Map.lookup (L.tail $ L.dropWhile (/= '.') tName) m))
            Just p -> extractor (proofObject p)

getProofStateDeclNames :: ProofState -> [String]
getProofStateDeclNames s = [curTheoremName s, curModuleName s] ++ Data.Map.keys (loadedModules s) ++ concatMap Data.Map.keys (loadedModules s) ++ Data.Map.keys (theorems s) ++ (fst <$> stypeDecls s) ++ (fst <$> ctxToList (fnAssumptions s)) ++ (fst <$> procAssumptions s) ++ stypeAssumptions s

declCheck n s res = if n `L.elem` getProofStateDeclNames s then s { errors = "Name already declared!":errors s } else res

_STypeDecl :: String -> Proposition -> ProofState -> ProofState
_STypeDecl n ty s = declCheck n s (s { stypeDecls = (n, ty):stypeDecls s })

_FAssumption :: String -> FunctionalTerm -> ProofState -> ProofState
_FAssumption n ty s = case safeInsert n ty (fnAssumptions s) of
    Right newAssms -> declCheck n s (s { fnAssumptions = newAssms })
    Left e -> s { errors = e:errors s }

_PAssumption :: String -> Proposition -> ProofState -> ProofState
_PAssumption n ty s = declCheck n s (s { procAssumptions = (n, substTyDecls (stypeDecls s) ty):procAssumptions s })

_STypeAssumption :: String -> ProofState -> ProofState
_STypeAssumption n s = declCheck n s (s { stypeAssumptions = n:stypeAssumptions s })

_PushMessage :: ProofState -> String -> ProofState
_PushMessage s m = s { outputs = m:outputs s }

_Apply :: ProofState -> Tactic -> ProofState
_Apply s t = applyTactic s t

{-| Tactic: Apply a tactic from the functional system to a functional subgoal. -}
_FTac :: FT.FunctionalTactic -> Tactic
_FTac t = do
    invalidateNameCache
    s <- ST.get
    case Data.Map.lookup (curSubgoal s) (subgoals s) of
        Just sg -> case inProgressFunctionalProof sg of
            Just (fs, p) -> case FT._FApply (Right fs) t of
                Right newFs ->
                    let
                        prevGoals = FT.subgoals fs
                        newGoals = FT.subgoals newFs
                        newGoalNames = (\n -> curSubgoal s ++ "." ++ n) <$> Data.Map.keys (Data.Map.difference newGoals prevGoals)
                        newGoalStack = (if Data.Map.null (Data.Map.filter (not . FT.used) newGoals) then [curSubgoal s] else newGoalNames) ++ tail (openGoalStack s)
                    in
                        if FT._FDone newFs
                        then case FT._FGetProof newFs of
                            Right fp -> ST.put (applyTactic (s { openGoalStack = newGoalStack }) (p fp)) >> return "Functional proof complete and tactic applied."
                            Left e -> tacError $ "Proof completed, but justification has errors: " ++ e
                        else ST.put (s { openGoalStack = newGoalStack, subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (newFs, p) }) (subgoals s) }) >> return "Functional tactic applied."
                Left e -> tacError e
            Nothing -> tacError "No in progress functional proof to apply to in current subgoal."
        Nothing -> tacError $ "Could not find current subgoal name: " ++ curSubgoal s ++ " in subgoals."

_FApply :: ProofState -> FT.FunctionalTactic -> ProofState
_FApply s t = case Data.Map.lookup (curSubgoal s) (subgoals s) of
    Just sg -> case inProgressFunctionalProof sg of
        Just (fs, p) -> case FT._FApply (Right fs) t of
            Right newFs -> if FT._FDone newFs
                then case FT._FGetProof newFs of
                    Right fp -> applyTactic s (p fp)
                    Left e -> s { outputs = ("Proof completed, but justification has errors: " ++ e):outputs s, errors = ("Proof completed, but justification has errors: " ++ e):errors s }
                else s { subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (newFs, p) }) (subgoals s), outputs = "Functional tactic applied.":outputs s }
            Left e -> s { outputs = e:outputs s, errors = e:errors s }
        Nothing -> s { outputs = "No in progress functional proof to apply to in current subgoal.":outputs s, errors = "No in progress functional proof to apply to in current subgoal.":errors s }
    Nothing -> s { outputs = ("Could not find current subgoal name: " ++ curSubgoal s ++ " in subgoals."):outputs s, errors = ("Could not find current subgoal name: " ++ curSubgoal s ++ " in subgoals."):errors s }

-- Identity
{-| Tactic: Apply the Id tactic linking an explicitly provided resource with an offered resource. -}
_Id :: String -> Tactic
_Id = idTac

-- Document tactics exactly like this!
{-| Tactic: Apply the Id tactic linking a provided resource with an offered resource. -}
_IdA :: Tactic
_IdA = idATac

-- Functional terms
{-| Tactic: Refine a functional term session type to a term in the functional system. -}
_FTermR :: Tactic
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
                newGoalsStack <- case openGoalStack curState of
                    h:rest -> return ((h ++ ".?a"):rest)
                    [] -> tacError "Cannot find the current subgoal!"
                ST.modify (\s -> s { openGoalStack = newGoalsStack, subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (FT._FTheorem  (fnContext seq) t names, fullTac )}) (subgoals s) })
                return "Functional proof in progress.")
        _ -> tacError $ "Cannot apply tactic to non Lift proposition: " ++ show (goalProposition seq)

{-| Tactic: Refine a functional term session type in the assumptions to an assumption in the functional system. -}
_FTermL :: String -> Tactic
_FTermL = functionalTermLeftTac S.empty

{-| Tactic: Automatically apply _FTermL to the first functional term in the linear context. -}
_FTermLA :: Tactic
_FTermLA = functionalTermLeftTacA

{-| Tactic: Refine an implication. Assume the antecedent and prove the consequent. -}
_ImpliesR :: Tactic
_ImpliesR = impliesRightTac

{-| Tactic: Refine an implication assumption. Create a goal to prove the antecedent, and another goal where the consequent is an assumption. -}
_ImpliesL :: String -> Tactic
_ImpliesL = impliesLeftTac S.empty

{-| Tactic: Automatically apply _ImpliesLA to the first implication proposition in the linear context. -}
_ImpliesLA :: Tactic
_ImpliesLA = impliesLeftTacA

{-| Tactic: Refine a unit proposition. Completes this branch of the proof. -}
_UnitR :: Tactic
_UnitR = unitRightTac

{-| Tactic: Refine a unit assumption. Discards the assumption from the linear context. -}
_UnitL :: String -> Tactic
_UnitL = unitLeftTac S.empty

{-| Tactic: Automatically apply _UnitL to the first implication proposition in the linear context. -}
_UnitLA :: Tactic
_UnitLA = unitLeftTacA

{-| Tactic: Refine a replicating proposition. Create a goal to prove the inner proposition. -}
_BangR :: Tactic
_BangR = replicationRightTac

{-| Tactic: Refine a replicating assumption. Moves the inner proposition to the unrestricted context. -}
_BangL :: String -> Tactic
_BangL = replicationLeftTac S.empty

{-| Tactic: Automatically apply _BangL to the first implication proposition in the linear context. -}
_BangLA :: Tactic
_BangLA = replicationLeftTacA

{-| Tactic: Creates a copy of an assumption in the unrestricted context in the linear context. -}
_Copy :: String -> Maybe String -> Tactic
_Copy = copyTac

{-| Tactic: Refine a With proposition. Creates two goals. One to prove the left side, and the other to prove the right side. -}
_WithR :: Tactic
_WithR = withRightTac

{-| Tactic: Refine a With assumption. Selects the left side as the assumption. -}
_WithL1 :: String -> Tactic
_WithL1 = withLeft1Tac S.empty

{-| Tactic: Automatically apply _WithL1 to the first implication proposition in the linear context. -}
_WithL1A :: Tactic
_WithL1A = withLeft1TacA

{-| Tactic: Refine a With assumption. Selects the right side as the assumption. -}
_WithL2 :: String -> Tactic
_WithL2 = withLeft2Tac S.empty

{-| Tactic: Automatically apply _WithL2 to the first implication proposition in the linear context. -}
_WithL2A :: Tactic
_WithL2A = withLeft2TacA

{-| Tactic: Refine a Tensor proposition. Creates two goals. One to prove the left side, and the other to prove the right side. -}
_TensorR :: Tactic
_TensorR = tensorRightTac

{-| Tactic: Refine a Tensor assumption. Both sides become one assumption each. -}
_TensorL :: String -> Tactic
_TensorL = tensorLeftTac S.empty

{-| Tactic: Automatically apply _TensorL to the first implication proposition in the linear context. -}
_TensorLA :: Tactic
_TensorLA = tensorLeftTacA

{-| Tactic: Refine a Plus proposition. Selects the left side as the goal. -}
_PlusR1 :: Tactic
_PlusR1 = plusRight1Tac

{-| Tactic: Refine a Plus proposition. Selects the right side as the goal. -}
_PlusR2 :: Tactic
_PlusR2 = plusRight2Tac

{-| Tactic: Refine a Plus assumption. Two subgoals are created. One to complete the proof with the left side of the assumption, and one for the right side. -}
_PlusL :: String -> Tactic
_PlusL = plusLeftTac S.empty

{-| Tactic: Automatically apply _PlusL to the first implication proposition in the linear context. -}
_PlusLA :: Tactic
_PlusLA = plusLeftTacA

{-| Tactic: Refine a forall quantification proposition. Adds the term to the functional context. -}
_ForallR :: Tactic
_ForallR = forallRightTac

{-| Tactic: Refine a forall quantification assumption. Creates a subgoal to validate the type of the term, and another to continue the proof once validated. -}
_ForallL :: String -> Tactic
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
                newGoalsStack <- case openGoalStack curState of
                    h:rest -> return ((h ++ ".?a"):rest)
                    [] -> tacError "Cannot find the current subgoal!"
                ST.modify (\s -> s { openGoalStack = newGoalsStack, subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (FT._FTheorem  (fnContext seq) t names, fullTac )}) (subgoals s) })
                return "Functional proof in progress.")
        _ -> tacError $ "Cannot apply tactic to non Forall proposition: " ++ show (goalProposition seq)

_ForallLA :: Tactic
_ForallLA = leftTacA (\_ s -> _ForallL s) (\case Forall x t p -> True; _ -> False)

{-| Tactic: Refine an existential quantification proposition. Creates a subgoal to validate the type of the term, and another to continue the proof once validated. -}
_ExistsR :: Tactic
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
                newGoalsStack <- case openGoalStack curState of
                    h:rest -> return ((h ++ ".?a"):rest)
                    [] -> tacError "Cannot find the current subgoal!"
                ST.modify (\s -> s { openGoalStack = newGoalsStack, subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (FT._FTheorem  (fnContext seq) t names, fullTac )}) (subgoals s) })
                return "Functional proof in progress.")
        _ -> tacError $ "Cannot apply tactic to non Exists proposition: " ++ show (goalProposition seq)

{-| Tactic: Refine an existential quantification assumption. Adds the term to the functional context. -}
_ExistsL :: String -> Tactic
_ExistsL = existsLeftTac S.empty

{-| Tactic: Automatically apply _ExistsL to the first implication proposition in the linear context. -}
_ExistsLA :: Tactic
_ExistsLA = existsLeftTacA

{-| Tactic: Refine a second order universal quantified proposition. Adds the variable to the type variable context. -}
_Forall2R :: Tactic
_Forall2R = forallRight2Tac

{-| Tactic: Refine a second order universal quantified assumption. Provide a well-formed type to bind to the abstraction. -}
_Forall2L :: String -> Proposition -> Tactic
_Forall2L = forallLeft2Tac

{-| Tactic: Refine a second order existential quantified proposition. Provide a well-formed type to bind to the abstraction. -}
_Exists2R :: Proposition -> Tactic
_Exists2R = existsRight2Tac

{-| Tactic: Refine a second order existential quantified assumption. Adds the variable to the type variable context. -}
_Exists2L :: String -> Tactic
_Exists2L = existsLeft2Tac S.empty

{-| Tactic: Automatically apply _Exists2L to the first implication proposition in the linear context. -}
_Exists2LA :: Tactic
_Exists2LA = existsLeft2TacA

{-| Tactic: Cut a theorem into the proof. A goal to prove the theorem is created, and another goal to use it as an assumption is created. -}
_Cut :: Proposition -> Tactic
_Cut = cutTac

{-| Tactic: Cut a replicating theorem into the proof. A goal to prove the theorem is created, and another goal to use it as an unrestricted assumption is created. -}
_CutRepl :: Proposition -> Tactic
_CutRepl = cutReplicationTac

_CutTheorem :: String -> Tactic
_CutTheorem = cutLinearTheoremTac

_CutReplTheorem :: String -> Tactic
_CutReplTheorem = (\s -> tacError "Not implemented!")

{-| Tactic: Refine a corecursive proposition. Provide the binding name, parameter names, and initial arguments. -}
_NuR :: String -> [String] -> [String] -> Tactic
_NuR = nuRightTac

{-| Tactic: Refine a corecursive assumption. Unfolds the type one level. -}
_NuL :: String -> Tactic
_NuL = nuLeftTac S.empty

{-| Tactic: Automatically apply _NuL to the first implication proposition in the linear context. -}
_NuLA :: Tactic
_NuLA = nuLeftTacA

{-| Tactic: Refine a type variable assumption. Provide the binding name from a previous _NuR application and the new arguments. -}
_TyVar :: String -> [String] -> Tactic
_TyVar = tyVarTac

{-| Tactic: Apply the weaken structural rule to the matching variable in the unrestricted or functional context. Will not allow the other contexts to be modified. -}
_Weaken :: String -> Tactic
_Weaken = weakenTac

-- Hole
_Hole :: Tactic
_Hole = holeTac

_Fiat :: Tactic
_Fiat = _Hole

-- Tacticals
{-| Tactic: Apply one tactic, then the second to the resulting subgoals of the first tactic. -}
_Then :: Tactic -> Tactic -> Tactic
_Then = thenTactical

{-| Tactic: Apply one tactic, then the second if the first one fails. -}
_Alt :: Tactic -> Tactic -> Tactic
_Alt = altTactical

{-| Tactic: Do nothing and succeed. Useful with _Alt. -}
_Skip :: Tactic
_Skip = skipTactical

{-| Tactic: Apply the tactic until it no longer succeeds. -}
_Repeat :: Tactic -> Tactic
_Repeat = repeatTactical

{-| Tactic: Apply all available introduction rules. -}
_Intros :: Tactic
_Intros = _Repeat (_ImpliesR `_Alt` _ForallR `_Alt` _Forall2R)

_Defer :: ProofState -> ProofState
_Defer curS =
    let
        filteredStack = L.filter (\name -> maybe False (not . isUsed) (Data.Map.lookup (L.takeWhile (/= '.') name) (subgoals curS))) (openGoalStack curS)
        newStack = if L.null filteredStack then filteredStack else tail filteredStack ++ [head filteredStack]
        (sessionGoal, fnGoal) = case newStack of
            goal:rest | '.' `L.elem` goal -> (L.takeWhile (/= '.') goal, L.drop 1 . L.dropWhile (/= '.') $ goal)
            (goal:rest) -> (goal, "")
            _ -> ("", "")
        newFnProofAction = if L.null fnGoal then return else (\fp -> return ((fst fp) { FT.curSubgoal = fnGoal }, snd fp)) :: (FT.ProofState, FunctionalProof -> Tactic) -> Maybe (FT.ProofState, FunctionalProof -> Tactic)
        newSubgoal = Data.Map.lookup sessionGoal (subgoals curS) >>= (\sg -> return $ sg { inProgressFunctionalProof = inProgressFunctionalProof sg >>= newFnProofAction })
        newSubgoals = case newSubgoal of
            Nothing -> subgoals curS
            Just sg -> Data.Map.insert sessionGoal sg (subgoals curS)
    in
        curS { openGoalStack = newStack, subgoals = newSubgoals }

_Prefer :: ProofState -> Int ->  ProofState
_Prefer curS i =
    let
        curSgs = openGoalStack curS
        (hs, ts) = L.splitAt i curSgs
    in
        if i >= L.length curSgs
        then curS
        else curS { openGoalStack = head ts : (hs ++ tail ts) }

_PrintTheorems :: ProofState -> ProofState
_PrintTheorems s = let
    localTs = L.intercalate "\n" $ L.filter (/= "") $ (\(n, p) -> case verifyProofM p of Right (_, seq) -> n ++ ": " ++ seqToS seq; Left e -> "") <$> Data.Map.toList (proofObject <$> theorems s)
    modulePrint = L.intercalate "\n" $ L.filter (/= "") $ (\(mName, moduleTheorems) -> L.intercalate "\n" $ L.filter (/= "") $ (\(n, p) -> case verifyProofM p of Right (_, seq) -> mName ++ "." ++ n ++ ": " ++ seqToS seq; Left e -> "") <$> Data.Map.toList (proofObject <$> moduleTheorems)) <$> Data.Map.toList (loadedModules s)
    in s { outputs = (L.intercalate "\n" [modulePrint, localTs]):outputs s }

_TestDisallowedVars :: Tactic
_TestDisallowedVars = do
    s <- ST.get
    return $ show (getUnavailableVarsForSubgoal (curSubgoal s) s)

_TestBranchReserved :: Tactic
_TestBranchReserved = do
    s <- ST.get
    return $ show (getVarsReservedInSubgoalBranches  s (curSubgoal s))

_TestPrevGoal :: Tactic
_TestPrevGoal = do
    sg <- getCurrentSubgoal
    return $ prevGoal sg

