module Main where

import System.IO
import System.Directory (getModificationTime, doesFileExist)
import System.Environment (getArgs)
import Control.Concurrent (threadDelay)
import Control.Exception (catch, IOException)
import Data.Time.Clock (UTCTime)
import qualified Data.Map as Map
import qualified Data.Set as S
import Control.Monad.Identity (Identity, runIdentity)

import Tactics (ProofState(..)) -- Ensure you import necessary types
import LinearLogic
import STILLParser (parseFile, parseStringCommand)
import DisplayUtil

-- ==========================================
-- 1. State Initialization
-- ==========================================

emptyState :: ProofState Identity
emptyState = S {
    subgoals = Map.empty,
    outputs = ["STILL Prover Initialized."],
    theorems = Map.empty,
    curTheoremName = "",
    curModuleName = "Main",
    loadedModules = Map.empty,
    openGoalStack = []
}

-- ==========================================
-- Script Execution
-- ==========================================

-- Parses and runs a file, handling imports recursively
runProofScript :: FilePath -> String -> IO (Either String (ProofState Identity))
runProofScript fname content = do
    let res = parseFile fname content
    case res of
        Left err -> return . Left $ "--------------------------------\nParse Error:\n" ++ show err
        Right (imports, commands) -> do
            -- 1. Load Imports (IO Action)
            stateWithImports <- loadImports imports emptyState

            -- 2. Run Commands (Pure Fold)
            let finalState = foldl (\s f -> f s) stateWithImports commands

            -- 3. Return Output Log (Reversed because logs act like a stack)
            return . Right $ finalState -- unlines (reverse (outputs finalState))

-- Recursively load imported modules
loadImports :: [String] -> ProofState Identity -> IO (ProofState Identity)
loadImports [] s = return s
loadImports (m:ms) s = do
    if Map.member m (loadedModules s)
        then loadImports ms s -- Already loaded
        else do
            let filename = m ++ ".still" -- Assumption: Module X is in X.still
            exists <- doesFileExist filename
            if not exists
                then do
                    putStrLn $ "[Warning] Import not found: " ++ filename
                    loadImports ms s
                else do
                    content <- readFileSafe filename
                    case parseFile filename content of
                        Left err -> do
                            putStrLn $ "[Error] Failed to parse import " ++ m ++ ": " ++ show err
                            loadImports ms s
                        Right (subImports, subCmds) -> do
                            -- 1. Load recursive imports for this module
                            s' <- loadImports subImports s

                            -- 2. Run module commands on a clean slate (inheriting only loadedModules)
                            let modState = s' { subgoals = Map.empty, theorems = Map.empty, curModuleName = m, openGoalStack = [] }
                            let modResult = foldl (\st f -> f st) modState subCmds

                            -- 3. Store the resulting theorems in the global loadedModules map
                            let newLoaded = Map.insert m (theorems modResult) (loadedModules s')

                            -- 4. Continue
                            loadImports ms (s' { subgoals = Map.empty, theorems = Map.empty, openGoalStack = [], loadedModules = newLoaded })

-- ==========================================
-- 3. Main Entry Point
-- ==========================================

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    args <- getArgs
    case args of
        ("watch":fileName:[]) -> startWatcher fileName
        ("watch":[])          -> startWatcher "data.txt"
        ("repl":_)            -> startRepl
        (fname:[])            -> do -- Run once mode
            content <- readFileSafe fname
            result <- runProofScript fname content
            case result of Left e -> putStrLn e; Right fs -> putStrLn $ unlines (reverse (outputs fs))
        []                    -> startRepl

-- ==========================================
-- 4. REPL Implementation
-- ==========================================

startRepl :: IO ()
startRepl = do
    putStrLn "--- STILL Interactive Mode (Type :q to quit) ---"
    replLoop emptyState

replLoop :: ProofState Identity -> IO ()
replLoop currentState = do
    putStr "π> "
    done <- isEOF
    if done then putStrLn "\nGoodbye!" else do
        input <- getLine
        case input of
            ":q" -> putStrLn "Goodbye!"
            "quit" -> putStrLn "Goodbye!"
            _ -> do
                -- Parse and Execute
                case parseStringCommand input of
                    Left err -> do
                        putStrLn $ "Parse Error: " ++ show err
                        replLoop currentState
                    Right cmdFunc -> do
                        let newState = cmdFunc currentState
                        -- Print only the NEW output (head of the list)
                        mainPrinter (Right newState)
                        replLoop newState

-- ==========================================
-- 5. Watcher Implementation
-- ==========================================

startWatcher :: FilePath -> IO ()
startWatcher targetFile = do
    putStrLn $ "Watching " ++ targetFile ++ " ... (Ctrl+C to stop)"

    exists <- doesFileExist targetFile
    if not exists then writeFile targetFile "" else return ()

    initialTime <- getModificationTime targetFile
    initialContent <- readFileSafe targetFile

    -- Run logic immediately
    putStrLn "\n--- Reloading ---"
    output <- runProofScript targetFile initialContent
    case output of
        Left e -> putStrLn e
        Right s -> mainPrinter (Right s)

    watchLoop targetFile initialTime

watchLoop :: FilePath -> UTCTime -> IO ()
watchLoop filePath lastModified = do
    threadDelay 200000 -- 0.2 seconds check interval
    exists <- doesFileExist filePath
    if not exists
        then watchLoop filePath lastModified
        else do
            currentModified <- getModificationTime filePath
            if currentModified > lastModified
                then do
                    -- Clear Screen (ANSI code)
                    putStr "\ESC[2J\ESC[H"
                    putStrLn $ "--- Checked " ++ filePath ++ " at " ++ show currentModified ++ " ---"

                    content <- readFileSafe filePath
                    output <- runProofScript filePath content
                    case output of
                        Left e -> putStrLn e
                        Right s -> mainPrinter (Right s)

                    watchLoop filePath currentModified
                else
                    watchLoop filePath lastModified

readFileSafe :: FilePath -> IO String
readFileSafe path = catch (readFile path) (\e -> let _ = (e :: IOException) in return "")
