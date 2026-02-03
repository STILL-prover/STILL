module TacticsIO where

import Data.Map
import qualified Data.Set as S
import qualified Data.List as L
import Tactics
import LinearLogic
import Control.Monad.Trans (MonadIO(liftIO))
import qualified Control.Monad.State.Lazy as ST
import qualified FunctionalTactics as FT

idTacAction :: Tactic IO
idTacAction = do
    liftIO $ Prelude.putStrLn "Please enter the variable for the prop."
    i <- liftIO Prelude.getLine
    idTac i

functionalTermRightAction :: Tactic IO
functionalTermRightAction = do
    curState <- ST.get
    sg <- getCurrentSubgoal
    seq <- getCurrentSequent
    let fullTac p = do
            --ST.modify (\s1 -> s1 { curSubgoal = curSubgoal curState })
            functionalTermRightTac p
    case goalProposition seq of
        Lift t -> (do
            fState <- case inProgressFunctionalProof sg of
                Just s -> liftIO $ FT.continueProof (fst s)
                Nothing -> liftIO $ FT.prove (fnContext seq) t (getSequentNames seq `S.union` S.fromList (Data.Map.keys (uniqueNameVars curState)))
            if FT.isComplete fState then (do
                res <- liftIO $ FT.getProof fState
                case res of
                    Right fp -> functionalTermRightTac fp
                    Left e -> tacError e)
            else (do
                ST.modify (\s -> s { subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (fState, fullTac ) }) (subgoals s) })
                return "Functional proof in progress."))
        _ -> tacError $ "Cannot apply tactic to non Lift proposition: " ++ show (goalProposition seq)

functionalTermLeftAction :: Tactic IO
functionalTermLeftAction = do
    liftIO $ Prelude.putStrLn "Please enter the variable for the functional term in the linear context."
    i <- liftIO Prelude.getLine
    functionalTermLeftTac i

impliesRightAction :: Tactic IO
impliesRightAction = impliesRightTac

impliesLeftAction :: Tactic IO
impliesLeftAction = do
    liftIO $ Prelude.putStrLn "Please enter the variable for the prop."
    i <- liftIO Prelude.getLine
    impliesLeftTac i

unitRightAction :: Tactic IO
unitRightAction = unitRightTac

unitLeftAction :: Tactic IO
unitLeftAction = do
    liftIO $ Prelude.putStrLn "Please enter the variable for the prop."
    i <- liftIO Prelude.getLine
    unitLeftTac i

replicationRightAction :: Tactic IO
replicationRightAction = replicationRightTac

replicationLeftAction :: Tactic IO
replicationLeftAction = do
    liftIO $ Prelude.putStrLn "Please enter the variable for the replication proposition."
    i <- liftIO Prelude.getLine
    replicationLeftTac i

copyAction :: Tactic IO
copyAction = do
    liftIO $ Prelude.putStrLn "Please enter the variable for the proposition in the unrestricted context."
    i <- liftIO Prelude.getLine
    copyTac i Nothing

withRightAction :: Tactic IO
withRightAction = withRightTac

withLeft1Action :: Tactic IO
withLeft1Action = do
    liftIO $ Prelude.putStrLn "Please enter the variable for the with proposition."
    i <- liftIO Prelude.getLine
    withLeft1Tac i

withLeft2Action :: Tactic IO
withLeft2Action = do
    liftIO $ Prelude.putStrLn "Please enter the variable for the with proposition."
    i <- liftIO Prelude.getLine
    withLeft2Tac i

tensorRightAction :: Tactic IO
tensorRightAction = tensorRightTac

tensorLeftAction :: Tactic IO
tensorLeftAction = do
    liftIO $ Prelude.putStrLn "Please enter the variable for the tensor proposition."
    i <- liftIO Prelude.getLine
    tensorLeftTac i

plusRight1Action :: Tactic IO
plusRight1Action = plusRight1Tac


plusRight2Action :: Tactic IO
plusRight2Action = plusRight2Tac

plusLeftAction :: Tactic IO
plusLeftAction = do
    liftIO $ Prelude.putStrLn "Please enter the variable for the plus proposition."
    i <- liftIO Prelude.getLine
    plusLeftTac i

forallRightAction :: Tactic IO
forallRightAction = forallRightTac

forallLeftAction :: Tactic IO
forallLeftAction = do
    liftIO $ Prelude.putStrLn "Please enter the variable for the forall proposition."
    i <- liftIO Prelude.getLine
    curState <- ST.get
    sg <- getCurrentSubgoal
    seq <- getCurrentSequent
    let fullTac p = do
            --ST.modify (\s1 -> s1 { curSubgoal = curSubgoal curState })
            forallLeftTac i p
    case Data.Map.lookup i $ linearContext seq of
        Just (Forall x t a) -> (do
            fState <- case inProgressFunctionalProof sg of
                Just s -> liftIO $ FT.continueProof (fst s)
                Nothing -> liftIO $ FT.prove (fnContext seq) t (getSequentNames seq `S.union` S.fromList (Data.Map.keys (uniqueNameVars curState)))
            if FT.isComplete fState then (do
                res <- liftIO $ FT.getProof fState
                case res of
                    Right fp -> forallLeftTac i fp
                    Left e -> tacError e)
            else (do
                ST.modify (\s -> s { subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (fState, fullTac) }) (subgoals s) })
                return "Functional proof in progress."))
        Just p -> tacError $ "Cannot apply tactic to non Forall proposition: " ++ show (goalProposition seq)
        _ -> tacError $ "Cannot find " ++ i ++ " in linear context."

existsRightAction :: Tactic IO
existsRightAction = do
    curState <- ST.get
    sg <- getCurrentSubgoal
    seq <- getCurrentSequent
    let fullTac p = do
            --ST.modify (\s1 -> s1 { curSubgoal = curSubgoal curState })
            existsRightTac p
    case goalProposition seq of
        (Exists x t a) -> (do
            fState <- case inProgressFunctionalProof sg of
                Just s -> liftIO $ FT.continueProof (fst s)
                Nothing -> liftIO $ FT.prove (fnContext seq) t (getSequentNames seq `S.union` S.fromList (Data.Map.keys (uniqueNameVars curState)))
            if FT.isComplete fState then (do
                res <- liftIO $ FT.getProof fState
                case res of
                    Right fp -> existsRightTac fp
                    Left e -> tacError e)
            else (do
                ST.modify (\s -> s { subgoals = Data.Map.insert (curSubgoal s) (sg { inProgressFunctionalProof = Just (fState, fullTac) }) (subgoals s) })
                return "Functional proof in progress."))
        _ -> tacError $ "Cannot apply tactic to non Forall proposition: " ++ show (goalProposition seq)

existsLeftAction :: Tactic IO
existsLeftAction = do
    liftIO $ Prelude.putStrLn "Please enter the variable for the exists proposition."
    i <- liftIO Prelude.getLine
    existsLeftTac i

availableSubgoalsAction :: Tactic IO
availableSubgoalsAction = do
    curSubgoals <- Data.Map.keys <$> ST.gets subgoals
    return $ L.drop 1 $ L.foldl' (\acc k -> acc ++ " " ++ k) "" curSubgoals

switchSubgoalAction :: Tactic IO
switchSubgoalAction = do
    nextSubgoal <- liftIO Prelude.getLine
    --ST.modify (\s -> s { curSubgoal = nextSubgoal })
    return $ "Switched to " ++ nextSubgoal

thenTacticalAction :: Tactic IO
thenTacticalAction = do
    liftIO $ Prelude.putStrLn "Enter a tactic:"
    tac1Name <- liftIO Prelude.getLine
    liftIO $ Prelude.putStrLn "Enter a tactic:"
    tac2Name <- liftIO Prelude.getLine
    let tac1Action = snd . head $ L.filter (\a -> fst a == tac1Name) actions
        tac2Action = snd . head $ L.filter (\a -> fst a == tac2Name) actions
    thenTactical tac1Action tac2Action

actions :: [(String, Tactic IO)]
actions = [("id", idTacAction),
    ("impR", impliesRightAction),
    ("impL", impliesLeftAction),
    ("functionalR", functionalTermRightAction),
    ("functionalL", functionalTermLeftAction),
    ("unitR", unitRightAction),
    ("unitL", unitLeftAction),
    ("replR", replicationRightAction),
    ("replL", replicationLeftAction),
    ("copy", copyAction),
    ("withR", withRightAction),
    ("withL1", withLeft1Action),
    ("withL2", withLeft2Action),
    ("tensorR", tensorRightAction),
    ("tensorL", tensorLeftAction),
    ("plusR1", plusRight1Action),
    ("plusR2", plusRight2Action),
    ("plusL", plusLeftAction),
    ("forallR", forallRightAction),
    ("forallL", forallLeftAction),
    ("existsR", existsRightAction),
    ("existsL", existsLeftAction),
    ("subgoals", availableSubgoalsAction),
    ("switch", switchSubgoalAction),
    ("then", thenTacticalAction)]