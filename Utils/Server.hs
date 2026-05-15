module Utils.Server where

import Control.Exception (IOException, catch)
import Data.Map qualified as Map
import Data.Set qualified as S
import ECC.Kernel (emptyContext)
import Parser.CmdParsers (Command, CommandSpan (CommandSpan, spanRange, spanValue), Range (Range), evalCommand, evalCommandM, parseFileSpans)
import Control.Monad (foldM)
import SessionTypes.Kernel
import SessionTypes.Tactics (ProofState (..), allSubgoalNames)
import System.Directory (doesFileExist)
import System.IO (hPutStrLn, stderr)
import Text.Parsec (sourceColumn, sourceLine)
import Utils.Misc (namesInOrder)

-- ==========================================
-- State Initialization
-- ==========================================

emptyState :: ProofState
emptyState =
  S
    { subgoals = Map.empty,
      outputs = ["STILL Prover Initialized."],
      theorems = Map.empty,
      curTheoremName = "",
      curModuleName = "Main",
      loadedModules = Map.empty,
      openGoalStack = [],
      cachedProofStateNames = S.empty,
      newSubgoalNameList = allSubgoalNames,
      cachedVarNames = namesInOrder,
      stypeDecls = [],
      fnAssumptions = emptyContext,
      procAssumptions = [],
      errors = [],
      stypeAssumptions = [],
      curFnTheoremName = "",
      inProgressTopLevelFnProof = Nothing
    }

-- ==========================================
-- Script Execution
-- ==========================================

readFileSafe :: FilePath -> IO String
readFileSafe path = catch (readFile path) (\e -> let _ = (e :: IOException) in return "")

loadImports :: [String] -> ProofState -> IO ProofState
loadImports [] s = pure s
loadImports (m : ms) s =
  if Map.member m (loadedModules s)
    then loadImports ms s
    else do
      let filename = m ++ ".still"
      exists <- doesFileExist filename
      if not exists
        then do
          hPutStrLn stderr $ "[Warning] Import not found: " ++ filename
          loadImports ms s
        else do
          content <- readFileSafe filename
          case parseFileSpans filename content of
            Left err -> do
              hPutStrLn stderr $ "[Error] Failed to parse import " ++ m ++ ": " ++ show err
              loadImports ms s
            Right (_, subImports, subCmds) -> do
              s' <- loadImports subImports s
              let modState0 = s' {subgoals = Map.empty, theorems = Map.empty, curModuleName = m, openGoalStack = []}
                  modResult  = foldl (\st sp -> evalCommand (spanValue sp) st) modState0 subCmds
                  newLoaded  = Map.insert m (theorems modResult) (loadedModules s')
              loadImports ms (s' {subgoals = Map.empty, theorems = Map.empty, openGoalStack = [], loadedModules = newLoaded})

parseAndLoad
  :: FilePath -> String
  -> IO (Either String (String, [String], [CommandSpan Command], ProofState))
parseAndLoad fname content =
  case parseFileSpans fname content of
    Left err ->
      return . Left $ "--------------------------------\nParse Error:\n" ++ show err
    Right (moduleName, imports, cmdSpans) -> do
      stateWithImports <- loadImports imports emptyState
      let s0 = stateWithImports {curModuleName = moduleName}
      return $ Right (moduleName, imports, cmdSpans, s0)

runProofScript :: FilePath -> String -> IO (Either String ProofState)
runProofScript fname content = do
  res <- parseAndLoad fname content
  case res of
    Left err -> return (Left err)
    Right (_, _, cmdSpans, s0) -> do
      finalState <- foldM (\s sp -> evalCommandM (spanValue sp) s) s0 cmdSpans
      return (Right finalState)

-- ==========================================
-- Detailed Script Execution (with snapshots)
-- ==========================================

data Snapshot = Snapshot
  { beforeState :: ProofState,
    afterState :: ProofState
  }

-- psCommands !! i corresponds to psSnaps !! i
data ProcessedScript = ProcessedScript
  { psModuleName :: String,
    psImports :: [String],
    psCommands :: [CommandSpan Command],
    psSnaps :: [Snapshot]
  }

runProofScriptDetailed :: FilePath -> String -> IO (Either String ProcessedScript)
runProofScriptDetailed fname content = do
  res <- parseAndLoad fname content
  case res of
    Left err -> return (Left err)
    Right (moduleName, imports, cmds, initialState) -> do
      let step (st, acc) sp = do
            st' <- evalCommandM (spanValue sp) st
            return (st', acc ++ [Snapshot {beforeState = st, afterState = st'}])
      (_, snaps) <- foldM step (initialState, []) cmds
      return . Right $
        ProcessedScript
          { psModuleName = moduleName
          , psImports    = imports
          , psCommands   = cmds
          , psSnaps      = snaps
          }

-- ==========================================
-- Cursor Position Lookup
-- ==========================================

containsPos :: Range -> Int -> Int -> Bool
containsPos (Range s e) line col =
  let sl = sourceLine s
      sc = sourceColumn s
      el = sourceLine e
      ec = sourceColumn e
   in (line > sl || line == sl && col >= sc) && (line < el || line == el && col <= ec)

findSnapshotAt :: ProcessedScript -> Int -> Int -> Maybe (CommandSpan Command, Snapshot)
findSnapshotAt ps line col = go (zip (psCommands ps) (psSnaps ps))
  where
    go [] = Nothing
    go ((sp, snap) : xs)
      | containsPos (spanRange sp) line col = Just (sp, snap)
      | otherwise = go xs
