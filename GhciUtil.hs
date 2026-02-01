{-# LANGUAGE UndecidableInstances #-}
module GhciUtil where

import Tactics
import qualified Data.List as L
import qualified FunctionalSystem as FS
import qualified FunctionalTactics as FT
import qualified Data.Map
import qualified Data.Map as M
import Data.Maybe (isNothing)
import LinearLogic (Process (..), Proposition (..), Sequent (fnContext, unrestrictedContext, linearContext, channel, goalProposition), pToS, propToS, seqToS)
import qualified Data.Set as S
import qualified Data.String
import FunctionalSystem (ftToS)
import FunctionalTactics (ftseqToSHelper)

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
            curReservedVars = getUnavailableVarsForSubgoal curSgName s
            subgoalPrinter n sg = case inProgressFunctionalProof sg of
                Nothing -> (if n == curSubgoal s then "*" else " ") ++ n ++ sgNameSep ++ showFiltered curReservedVars sg
                Just (fs, p) -> L.foldl' (\acc kvp -> acc ++ "\n" ++ (if n == curSubgoal s && fst kvp == FT.curSubgoal fs then "*" else " ") ++ n ++ "." ++ fst kvp ++ sgNameSep ++ fsgToS (snd kvp)) ""  (Data.Map.toList (Data.Map.filter (not . FT.used) (FT.subgoals fs)))
            messagePrinter = if L.null $ outputs s then "" else head $ outputs s
        in
            putStrLn $ messagePrinter ++ L.foldl' (\acc kvp -> acc ++ "\n" ++ uncurry subgoalPrinter kvp) "" (Data.Map.toList (Data.Map.filter (isNothing . used) (subgoals s)))
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

printCommands :: IO ()
printCommands = do
    putStrLn $ L.intercalate "\n" ["init <module_name> :: Initializes a module with a fresh prover state. Wrap module name in quotes.",
        "theorem <theorem_name> <proposition> :: Initializes a theorem in the module. The theorem name must be wrapped in quotes and be one word, no spaces.",
        "apply <tactic> :: Applies the supplied tactic to the current subgoal. Must be a result with the Tactic m type",
        "switch <subgoal_name> :: Switches to the supplied subgoal name. Must wrap name in quotes.",
        "done :: Validates the current proof, and loads it as a theorem if validation succeeds.",
        "extract <theorem_name> :: Extracts the process term corresponding to the proof of the theorem. The theorem name must be wrapped in quotes.",
        "load_module <file_name> :: Loads the file with prover commands as a separate state, then loads that state into the current one as a module.",
        "help_tactics :: Display all tactics and a small description for each one.",
        "help_functional_tactics :: Display all functional tactics and a small description for each one.",
        "help_commands :: Display this text."]

removeNewlines :: String -> String
removeNewlines args = L.unwords (L.lines args)


