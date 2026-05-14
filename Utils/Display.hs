module Utils.Display where

import SessionTypes.Tactics
import qualified Data.List as L
import qualified ECC.Kernel as FS
import qualified ECC.Tactics as FT
import qualified Data.Map
import qualified Data.Map as M
import Data.Maybe (isNothing, isJust, fromJust)
import SessionTypes.Kernel (Process (..), Proposition (..), Sequent (tyVarContext, fnContext, unrestrictedContext, linearContext, channel, goalProposition), pToS, propToS, seqToS)
import qualified Data.Set as S
import qualified Data.String
import ECC.Kernel (ftToS, ctxToList)
import ECC.Tactics (ftseqToSHelper)

ftseqToS :: FT.FunctionalTacticsSequent -> String
ftseqToS = ftseqToSHelper

fsgToS :: FT.Subgoal -> String
fsgToS sg = ftseqToS (FT.sequent sg)

sgToS :: Subgoal -> String
sgToS sg = seqToS (sequent sg)

sgsToS :: [Subgoal] -> String
sgsToS (sg:sgs) = sgToS sg ++ "\n" ++ sgsToS sgs
sgsToS [] = ""

ansiRed :: String -> String
ansiRed s = "\ESC[31m" ++ s ++ "\ESC[0m"

showFiltered :: (S.Set String, S.Set String) -> Bool -> Subgoal -> String
showFiltered (hiddenVars, blackVars) isMultCtx sg =
    let
        seq' = sequent sg
        formatBlock [] = ""
        formatBlock items = "\n    " ++ L.intercalate ",\n    " items
        tyVars = S.toList (tyVarContext seq')
        fns    = [k ++ ":" ++ ftToS v | (k, v) <- ctxToList (fnContext seq')]
        unres  = [k ++ ":" ++ propToS v | (k, v) <- Data.Map.toList (unrestrictedContext seq')]
        lin    = [ let entry = k ++ ":" ++ propToS v
                   in if k `S.member` blackVars
                      then entry
                      else if isMultCtx then ansiRed entry else entry
                 | (k, v) <- L.filter (\(k, v) -> not (k `S.member` hiddenVars)) (Data.Map.toList (linearContext seq')) ]
        goal   = channel seq' ++ ":" ++ propToS (goalProposition seq')
    in
        "\n  Ω: " ++ (if L.null tyVars then "" else formatBlock tyVars) ++ ";" ++
        "\n  Ψ:  " ++ (if L.null fns then "" else formatBlock fns) ++ ";" ++
        "\n  Γ:  " ++ (if L.null unres then "" else formatBlock unres) ++ ";" ++
        "\n  Δ: " ++ (if L.null lin then "" else formatBlock lin) ++
        "\n  |- " ++ goal

renderState :: ProofState -> String
renderState s =
    let
        sgNameSep = ">> "
        ctxInfo     sgn = getContextInfo sgn s
        subgoalPrinter n sg = case inProgressFunctionalProof sg of
            Just (fs, p) | Data.Map.member (L.drop 1 (L.dropWhile (/= '.') n)) (FT.subgoals fs) -> (if [n] == L.take 1 (openGoalStack s) then "*" else " ") ++ n ++ sgNameSep ++ fsgToS (FT.subgoals fs Data.Map.! L.drop 1 (L.dropWhile (/= '.') n))
            Nothing -> let (unavail, committed, multCtx) = ctxInfo n
                       in (if n == curSubgoal s then "*" else " ") ++ n ++ sgNameSep ++ showFiltered (unavail, committed) multCtx sg
            _ -> n
        messagePrinter = (if L.null $ outputs s then "" else head $ outputs s) ++ (if L.null (errors s) then "" else "\n" ++ unlines (reverse (errors s)))
        orderedSubgoals = (\(sgn, sg) -> (sgn, fromJust sg)) <$> L.filter (\(sgn, sg) -> isJust sg) ((\sgn -> (sgn, Data.Map.lookup  (L.takeWhile (/= '.') sgn) (subgoals s))) <$> openGoalStack s)
        cachedNames = show $ cachedProofStateNames s
        freeNames = show $ getProofStateFreeNames s
    in
        messagePrinter ++ L.foldl' (\acc kvp -> acc ++ "\n" ++ uncurry subgoalPrinter kvp) "" orderedSubgoals

renderGoals :: ProofState -> String
renderGoals s =
    let
        sgNameSep = ">> "
        ctxInfo     sgn = getContextInfo sgn s
        subgoalPrinter n sg = case inProgressFunctionalProof sg of
            Just (fs, p) | Data.Map.member (L.drop 1 (L.dropWhile (/= '.') n)) (FT.subgoals fs) -> (if [n] == L.take 1 (openGoalStack s) then "*" else " ") ++ n ++ sgNameSep ++ fsgToS (FT.subgoals fs Data.Map.! L.drop 1 (L.dropWhile (/= '.') n))
            Nothing -> let (unavail, committed, multCtx) = ctxInfo n
                       in (if n == curSubgoal s then "*" else " ") ++ n ++ sgNameSep ++ showFiltered (unavail, committed) multCtx sg
            _ -> n
        orderedSubgoals = (\(sgn, sg) -> (sgn, fromJust sg)) <$> L.filter (\(sgn, sg) -> isJust sg) ((\sgn -> (sgn, Data.Map.lookup (L.takeWhile (/= '.') sgn) (subgoals s))) <$> openGoalStack s)
    in
        if null orderedSubgoals
          then "(no open goals)"
          else L.intercalate "\n" (uncurry subgoalPrinter <$> orderedSubgoals)

mainPrinter (Right s) =
        let
            sgNameSep = ">> "
            ctxInfo     sgn = getContextInfo sgn s
            subgoalPrinter n sg = case inProgressFunctionalProof sg of
                Just (fs, p) | Data.Map.member (L.drop 1 (L.dropWhile (/= '.') n)) (FT.subgoals fs) -> (if [n] == L.take 1 (openGoalStack s) then "*" else " ") ++ n ++ sgNameSep ++ fsgToS (FT.subgoals fs Data.Map.! L.drop 1 (L.dropWhile (/= '.') n))
                Nothing -> let (unavail, committed, multCtx) = ctxInfo n
                           in (if n == curSubgoal s then "*" else " ") ++ n ++ sgNameSep ++ showFiltered (unavail, committed) multCtx sg
                _ -> n
            messagePrinter = (if L.null $ outputs s then "" else head $ outputs s) ++ (if L.null (errors s) then "" else "\n" ++ unlines (reverse (errors s)))
            orderedSubgoals = L.reverse $ (\(sgn, sg) -> (sgn, fromJust sg)) <$> L.filter (\(sgn, sg) -> isJust sg) ((\sgn -> (sgn, Data.Map.lookup  (L.takeWhile (/= '.') sgn) (subgoals s))) <$> openGoalStack s)
        in
            putStrLn $ renderState s
mainPrinter (Left e) = putStrLn $ "Error occured: " ++ e

getGoodLines :: [(String, String, String)] -> [String] -> [(String, String, String)]
getGoodLines acc (h1:h2:h3:rest) = if L.take 10 h1 == "{-| Tactic" then getGoodLines ((h1,h2,h3):acc) rest else getGoodLines acc (h2:h3:rest)
getGoodLines acc rest = reverse acc

prettyPrintGoodLine :: (String, String, String) -> String
prettyPrintGoodLine (a,b,c) = (L.takeWhile (\n -> n /= ' ' && n /= '=' ) b) ++ L.takeWhile (\d -> d /= '-') (L.drop 10 a)

getTactics :: IO ()
getTactics = do
    fileLines <- getGoodLines [] . lines <$> readFile "SessionTypes/Tactics.hs"
    putStrLn $ L.intercalate "\n" (prettyPrintGoodLine <$> fileLines)

getFTactics :: IO ()
getFTactics = do
    fileLines <- getGoodLines [] . lines <$> readFile "ECC/Tactics.hs"
    putStrLn $ L.intercalate "\n" (prettyPrintGoodLine <$> fileLines)

printCommands :: String
printCommands = do
    L.intercalate "\n" ["module MODULE_NAME [imports [IMPORT_MODULE_NAME ...]] begin :: starts a module.",
        "theorem THEOREM_NAME: \"PROPOSITION\" :: Initializes a theorem.",
        "apply TACTIC_EXPRESSION :: Applies the supplied tactic to the current subgoal.",
        "defer :: Moves the current subgoal to the end of the list of open subgoals.",
        "done :: Validates the current proof, and loads it as a theorem if validation succeeds.",
        "help :: Display this text."]

removeNewlines :: String -> String
removeNewlines args = L.unwords (L.lines args)
