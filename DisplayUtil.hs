{-# LANGUAGE UndecidableInstances #-}
module DisplayUtil where

import SessionTypes.Tactics
import qualified Data.List as L
import qualified ECC.Kernel as FS
import qualified ECC.Tactics as FT
import qualified Data.Map
import qualified Data.Map as M
import Data.Maybe (isNothing, isJust, fromJust)
import SessionTypes.Kernel (Process (..), Proposition (..), Sequent (fnContext, unrestrictedContext, linearContext, channel, goalProposition), pToS, propToS, seqToS)
import qualified Data.Set as S
import qualified Data.String
import ECC.Kernel (ftToS)
import ECC.Tactics (ftseqToSHelper)

fcToS :: FS.FunctionalContext -> String
fcToS = M.foldlWithKey (\acc k t -> acc ++ k ++ ":" ++ ftToS t) ""

ftseqToS :: FT.FunctionalTacticsSequent -> String
ftseqToS = ftseqToSHelper

fsgToS :: FT.Subgoal m -> String
fsgToS sg = ftseqToS (FT.sequent sg)

sgToS :: Subgoal m -> String
sgToS sg = seqToS (sequent sg)

sgsToS :: [Subgoal m] -> String
sgsToS (sg:sgs) = sgToS sg ++ "\n" ++ sgsToS sgs
sgsToS [] = ""

showFiltered :: S.Set String -> Subgoal m -> String
showFiltered reservedVars sg =
    let
        actualSequent = (sequent sg) {
            fnContext = fnContext . sequent $ sg,
            unrestrictedContext = unrestrictedContext . sequent $ sg,
            linearContext = Data.Map.filterWithKey (\k v -> not (k `S.member` reservedVars)) (linearContext . sequent $ sg)
        }
    in seqToS actualSequent

class GhciPrint a where
  ghciPrint :: a -> IO ()

-- Default: anything with Show uses normal print
instance {-# OVERLAPPABLE #-} Show a => GhciPrint a where
  ghciPrint = print

ghciPrintFn :: GhciPrint a => a -> IO ()
ghciPrintFn = ghciPrint

ghciNoPrintFn :: a -> IO ()
ghciNoPrintFn a = return ()

mainPrinter (Right s) =
        let
            sgNameSep = ">> "
            curSgName = curSubgoal s
            curReservedVars sgn = getUnavailableVarsForSubgoal sgn s
            subgoalPrinter n sg = case inProgressFunctionalProof sg of
                Nothing -> (if n == curSubgoal s then "*" else " ") ++ n ++ sgNameSep ++ showFiltered (curReservedVars n) sg
                Just (fs, p) -> L.foldl' (\acc kvp -> acc ++ "\n" ++ (if n == curSubgoal s && fst kvp == FT.curSubgoal fs then "*" else " ") ++ n ++ "." ++ fst kvp ++ sgNameSep ++ fsgToS (snd kvp)) ""  (Data.Map.toList (Data.Map.filter (not . FT.used) (FT.subgoals fs)))
            messagePrinter = if L.null $ outputs s then "" else head $ outputs s
            orderedSubgoals = L.reverse $ (\(sgn, sg) -> (sgn, fromJust sg)) <$> L.filter (\(sgn, sg) -> isJust sg) ((\sgn -> (sgn, Data.Map.lookup  sgn (subgoals s))) <$> openGoalStack s)
        in
            putStrLn $ messagePrinter ++ L.foldl' (\acc kvp -> acc ++ "\n" ++ uncurry subgoalPrinter kvp) "" orderedSubgoals
mainPrinter (Left e) = putStrLn $ "Error occured: " ++ e

instance {-# OVERLAPPING #-} GhciPrint (Either String (ProofState m)) where
    ghciPrint = mainPrinter

instance {-# OVERLAPPING #-} GhciPrint (Either String Process) where
    ghciPrint (Right p) = putStrLn . pToS $ p
    ghciPrint (Left e) = putStrLn $ "Error occured: " ++ e

instance {-# OVERLAPPING #-} GhciPrint (ProofState m) where
    ghciPrint s = mainPrinter (Right s)

getGoodLines :: [(String, String, String)] -> [String] -> [(String, String, String)]
getGoodLines acc (h1:h2:h3:rest) = if L.take 10 h1 == "{-| Tactic" then getGoodLines ((h1,h2,h3):acc) rest else getGoodLines acc (h2:h3:rest)
getGoodLines acc rest = reverse acc

prettyPrintGoodLine :: (String, String, String) -> String
prettyPrintGoodLine (a,b,c) = (L.takeWhile (\n -> n /= ' ' && n /= '=' ) b) ++ L.takeWhile (\d -> d /= '-') (L.drop 10 a)

getTactics :: IO ()
getTactics = do
    fileLines <- getGoodLines [] . lines <$> readFile "Tactics.hs"
    putStrLn $ L.intercalate "\n" (prettyPrintGoodLine <$> fileLines)

getFTactics :: IO ()
getFTactics = do
    fileLines <- getGoodLines [] . lines <$> readFile "FunctionalTactics.hs"
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
