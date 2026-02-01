module Main where

import Data.Map
import qualified Data.Set as S
import qualified Control.Monad.State.Lazy as ST
import qualified Data.List as L
import Control.Monad (when)
import Text.Read (readMaybe)
import Data.Maybe (isJust, fromMaybe)
import FunctionalSystem
import Util
import LinearLogic
import Tactics
import TacticsIO
import FunctionalTactics (_FAx, _FWF, _FVar, _FVarA, _FPi, _FLambda, _FApp, _FSigma, _FPair, _FProj1, _FProj2, _FCumulativity, _FSimp, _FExact, _FExactKnown, _FThen, _FRepeat, _FAlt, _FSkip)
import qualified FunctionalTactics as FT
import qualified AC
import GhciUtil
import Control.Monad.Identity (Identity (runIdentity))
import PropParser

viewJustificationsLoop :: ProofState IO -> IO ()
viewJustificationsLoop s = do
    Prelude.putStrLn ("Enter subgoal to see justification (exit to quit): " ++ L.drop 1 (L.foldl' (\acc n -> acc ++ " " ++ n) "" $ Data.Map.keys (subgoals s)))
    a <- Prelude.getLine
    if a == "exit"
    then return ()
    else case Data.Map.lookup a $ subgoals s of
        Just sg -> (do
            res <- runProofState (subgoalJustification sg) s
            case res of
                Right (p, newState) -> (do
                    Prelude.print p
                    if verifyProof p then Prelude.putStrLn "Valid proof" >>= (\() -> Prelude.putStrLn (case extractProcess p of Right (p, seq) -> pToS p ++ "\n" ++ seqToS seq ; Left e -> "Error: " ++ e)) else Prelude.putStrLn "Not a valid proof"
                    viewJustificationsLoop s)
                Left err -> Prelude.putStrLn err >>= (\a -> viewJustificationsLoop s))
        Nothing -> Prelude.putStrLn ("Could not find the subgoal " ++ a) >>= (\a -> viewJustificationsLoop s)

mainLoop :: ProofState IO -> IO ()
mainLoop s = do
    if Data.Map.member (curSubgoal s) (subgoals s)
    then (do
        Prelude.putStrLn "Current state:"
        Prelude.putStrLn $ "Current subgoal: " ++ curSubgoal s
        Prelude.putStrLn $ "Sequent: " ++ seqToS (sequent (subgoals s! curSubgoal s))
        Prelude.putStrLn "Enter a tactic: "
        (i :: String) <- Prelude.getLine
        when (L.any (\a -> fst a == i) actions) $ do
            let nextTactic = snd . head $ L.filter (\a -> fst a == i) actions
            tacRes <- runProofState nextTactic s
            case tacRes of
                Right (res, newState) -> (do
                    Prelude.putStrLn res
                    mainLoop newState)
                Left err -> (do
                    Prelude.putStrLn err
                    mainLoop s))
    else (do
        case Data.Map.lookup "?a" $ subgoals s of
            Just sg -> (do
                res <- runProofState (subgoalJustification sg) s
                case res of
                    Right (p, newState) -> (do
                        Prelude.print p
                        if verifyProof p then Prelude.putStrLn "Proof has been verified" >>= (\a -> Prelude.putStrLn (case extractProcess p of Right (p, seq) -> pToS p ++ "\n" ++ seqToS seq ; Left e -> "Error: " ++ e)) else Prelude.putStrLn "Not a valid proof"
                        viewJustificationsLoop s)
                    Left err -> Prelude.putStrLn err >>= (\a -> viewJustificationsLoop s))
            Nothing -> Prelude.putStrLn "There is an issue finding the initial subgoal" >>= (\() -> viewJustificationsLoop s))

-- mainInit :: IO ()
-- mainInit = do
--     Prelude.putStrLn "Please enter the proposition in the sequent you would like to prove. Empty to begin proving. e.g. Par (Par (Dual \"A\") (Dual \"B\")) (Times (Var \"B\") (Var \"A\"))"
--     initialSeq <- Prelude.getLine
--     mainLoop $ initializeState "test" (initializeProof (Sequent { fnContext = Data.Map.empty, unrestrictedContext = Data.Map.empty, linearContext = Data.Map.empty, recursiveBindings = Data.Map.empty, channel = "z", goalProposition = Prelude.read initialSeq }))

main = putStrLn "Command line interface is not complete should run the prover using GHCi" --mainInit


