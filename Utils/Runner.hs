-- | Batch execution of proof scripts: the logic behind @still FILE ...@ and
-- @still benchmark FILE ...@. Kept free of printing and process exit so that
-- it can be tested directly; "Main" does the I/O.
module Utils.Runner
  ( ScriptResult (..)
  , runScriptFile
  , unfinishedProofErrors
  , DiagnosticInfo (..)
  , benchmarkFile
  , renderResultsTable
  ) where

import Control.Exception (evaluate)
import Data.List (foldl', intercalate, transpose)
import qualified Data.Map as Map
import Data.Time.Clock (UTCTime, diffUTCTime, getCurrentTime)
import Numeric (showFFloat)
import SessionTypes.Kernel (proofSize)
import SessionTypes.Tactics (ProofState (..), Theorem (numberOfSubgoals, proofObject))
import System.Directory (doesFileExist)
import Utils.Server (readFileSafe, runProofScript)

-- | Outcome of running one proof script.
data ScriptResult = ScriptResult
  { scriptOk       :: Bool      -- ^ True iff the script ran without any problem
  , scriptOutput   :: String    -- ^ The prover's normal output, oldest first
  , scriptProblems :: [String]  -- ^ Everything that makes the run a failure
  }
  deriving (Eq, Show)

-- | Run a script file. The result is a failure when the file is missing or
-- unparseable, when any command reports an error, or when the script ends
-- with a theorem still open.
runScriptFile :: FilePath -> IO ScriptResult
runScriptFile fname = do
  result <- loadAndRun fname
  return $ case result of
    Left e   -> ScriptResult False "" [e]
    Right fs -> let problems = scriptStateProblems fs
                in ScriptResult (null problems) (unlines (reverse (outputs fs))) problems

loadAndRun :: FilePath -> IO (Either String ProofState)
loadAndRun fname = do
  exists <- doesFileExist fname
  if not exists
    then return (Left ("file not found: " ++ fname))
    else readFileSafe fname >>= runProofScript fname

scriptStateProblems :: ProofState -> [String]
scriptStateProblems fs = reverse (errors fs) ++ unfinishedProofErrors fs

-- | A script that ends while a theorem is still open (no @done@) has not
-- proved that theorem, even if no tactic reported an error.
unfinishedProofErrors :: ProofState -> [String]
unfinishedProofErrors fs =
  [ "Proof of theorem '" ++ curTheoremName fs ++ "' is incomplete (missing 'done')."
  | not (null (curTheoremName fs)) ]

-- ==========================================
-- Benchmarking
-- ==========================================

data DiagnosticInfo = DiagnosticInfo
  { moduleName       :: String
  , executionTime    :: Double
  , maxExecutionTime :: Double
  , minExecutionTime :: Double
  , didError         :: Bool
  , numTheorems      :: String
  , maxSubgoals      :: String
  , maxProofNodes    :: String
  , totalSubgoals    :: String
  , totalProofNodes  :: String
  }
  deriving (Eq, Show)

-- | Run a script @n@ times (at least once) for timing. Returns the averaged
-- diagnostics together with the problems reported by the first run.
benchmarkFile :: Int -> FilePath -> IO (DiagnosticInfo, [String])
benchmarkFile n fname = do
  runs <- mapM (const (timedRun fname)) [1 .. max 1 n]
  let (infos, problems) = unzip runs
  return (averageDiagnostic infos, head problems)

-- | Time one evaluation of a script. Reading the file is excluded from the
-- measurement, and the resulting proof state is forced before the clock is
-- read again: the prover is lazy, so without this the timer would stop before
-- any proof search had actually happened.
timedRun :: FilePath -> IO (DiagnosticInfo, [String])
timedRun fname = do
  exists <- doesFileExist fname
  if not exists
    then return (errorDiagnostic fname 0, ["file not found: " ++ fname])
    else do
      content <- readFileSafe fname
      _       <- evaluate (length content)
      start   <- getCurrentTime
      result  <- runProofScript fname content
      _       <- evaluate (forceResult result)
      end     <- getCurrentTime
      let exTime = realToFrac (diffUTCTime end start)
      return $ case result of
        Left e   -> (errorDiagnostic fname exTime, [e])
        Right fs -> (getDiagnostics start end fs, scriptStateProblems fs)

-- | Force everything a script run produces: its messages, its errors, and the
-- proof object and subgoal count of every theorem.
forceResult :: Either String ProofState -> Int
forceResult (Left e)   = length e
forceResult (Right fs) =
  length (concat (outputs fs))
    + length (concat (errors fs))
    + length (curTheoremName fs)
    + sum [ fromIntegral (proofSize (proofObject t)) + fromIntegral (numberOfSubgoals t)
          | t <- Map.elems (theorems fs) ]

errorDiagnostic :: FilePath -> Double -> DiagnosticInfo
errorDiagnostic fname exTime = DiagnosticInfo
  { moduleName = fname, executionTime = exTime, maxExecutionTime = exTime, minExecutionTime = exTime
  , didError = True, numTheorems = "N/A", maxSubgoals = "N/A", maxProofNodes = "N/A"
  , totalSubgoals = "N/A", totalProofNodes = "N/A" }

getDiagnostics :: UTCTime -> UTCTime -> ProofState -> DiagnosticInfo
getDiagnostics st et s = DiagnosticInfo
  { moduleName       = curModuleName s
  , executionTime    = t
  , maxExecutionTime = t
  , minExecutionTime = t
  , didError         = not (null (scriptStateProblems s))
  , numTheorems      = show (Map.size (theorems s))
  , maxSubgoals      = show $ foldl' (\acc (_, i) -> max acc (numberOfSubgoals i)) 0 thms
  , maxProofNodes    = show $ foldl' (\acc (_, i) -> max acc (proofSize (proofObject i))) 0 thms
  , totalProofNodes  = show . sum $ (\(_, i) -> proofSize (proofObject i)) <$> thms
  , totalSubgoals    = show . sum $ (\(_, i) -> numberOfSubgoals i) <$> thms
  }
  where
    t    = realToFrac (diffUTCTime et st)
    thms = Map.toList (theorems s)

averageDiagnostic :: [DiagnosticInfo] -> DiagnosticInfo
averageDiagnostic ds = (head ds)
  { executionTime    = sum times / realToFrac (length ds)
  , maxExecutionTime = maximum times
  , minExecutionTime = minimum times
  , didError         = any didError ds
  }
  where times = executionTime <$> ds

-- | The results table, one row per module, as plain text (no escape codes).
renderResultsTable :: [DiagnosticInfo] -> String
renderResultsTable infos = unlines (formatRow headers : separator : map formatRow rows)
  where
    headers = ["Module", "Theorems", "Total Subgoals", "Total Proof Nodes", "Max Subgoals", "Max Proof Nodes", "Avg. Time (s)", "Max Time (s)", "Min Time (s)"]
    toRow r = [ moduleName r, numTheorems r, totalSubgoals r, totalProofNodes r, maxSubgoals r, maxProofNodes r
              , showFFloat (Just 6) (executionTime r) "", showFFloat (Just 6) (maxExecutionTime r) "", showFFloat (Just 6) (minExecutionTime r) "" ]
    rows      = map toRow infos
    colWidths = map (maximum . map length) (transpose (headers : rows))
    pad w s   = s ++ replicate (w - length s) ' '
    formatRow = intercalate " | " . zipWith pad colWidths
    separator = intercalate "-+-" (map (`replicate` '-') colWidths)
