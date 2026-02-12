module Main where

import System.IO
import System.Directory (getModificationTime, doesFileExist)
import System.Environment (getArgs)
import System.FilePath.Posix (dropExtensions)
import Control.Concurrent (threadDelay)
import Control.Exception (catch, IOException)
import Data.Time.Clock (UTCTime, getCurrentTime, diffUTCTime)
import qualified Data.Map as Map
import qualified Data.Set as S
import Control.Monad.Identity (Identity, runIdentity)

import SessionTypes.Tactics (ProofState(..), Theorem (proofObject, numberOfSubgoals), allSubgoalNames) -- Ensure you import necessary types
import SessionTypes.Kernel
import STILLParser (parseFile, parseStringCommand)
import DisplayUtil
import Data.List (intercalate, transpose, foldl')
import Data.Map (toList)
import Data.Time (formatTime, defaultTimeLocale)
import Numeric (showFFloat)
import Util (namesInOrder)

-- ==========================================
-- State Initialization
-- ==========================================

emptyState :: ProofState Identity
emptyState = S {
    subgoals = Map.empty,
    outputs = ["STILL Prover Initialized."],
    theorems = Map.empty,
    curTheoremName = "",
    curModuleName = "Main",
    loadedModules = Map.empty,
    openGoalStack = [],
    cachedProofStateNames = S.empty,
    newSubgoalNameList = allSubgoalNames,
    cachedVarNames = namesInOrder
}

data DiagnosticInfo = DiagnosticInfo {
    moduleName :: String,
    executionTime :: Double,
    maxExecutionTime :: Double,
    minExecutionTime :: Double,
    didError :: Bool,
    numTheorems :: String,
    maxSubgoals :: String,
    maxProofNodes :: String,
    totalSubgoals :: String,
    totalProofNodes :: String
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
-- Main Entry Point
-- ==========================================

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    args <- getArgs
    case args of
        ("watch":fileName:[]) -> startWatcher fileName
        ("watch":[])          -> startWatcher "Scratch.still"
        ("repl":fnames)       -> startRepl fnames
        ("benchmark":fnames)  -> runDiagnostics fnames []
        (fname:fnames)        -> runScripts (fname:fnames)
        []                    -> startRepl []
    where
        runScripts :: [String] -> IO ()
        runScripts [] = return ()
        runScripts (fname:fnames) = do
            putStrLn $ "Running: " ++ fname
            runScript fname
            if null fnames then return () else putStrLn "" >> putStrLn ""
            runScripts fnames
            return ()

        runScript :: String -> IO ()
        runScript fname = do
            startTime <- getCurrentTime
            content <- readFileSafe fname
            afterReadTime <- getCurrentTime
            result <- runProofScript fname content
            case result of
                Left e -> putStrLn e
                Right fs -> putStrLn $ unlines (reverse (outputs fs))

        runDiagnostics :: [String] -> [DiagnosticInfo] -> IO ()
        runDiagnostics [] infos = printInfos (reverse infos)
        runDiagnostics (fname:fnames) infos = runDiagnostic fname >>= (\d -> runDiagnostics fnames (averageDiagnostic d:infos))

        runDiagnostic :: String -> IO [DiagnosticInfo]
        runDiagnostic fname = (\_ -> do
            startTime <- getCurrentTime
            content <- readFileSafe fname
            result <- runProofScript fname content
            mainPrinter result
            endTime <- getCurrentTime
            let exTime = realToFrac (diffUTCTime endTime startTime)
            case result of
                Left e -> return $ DiagnosticInfo { moduleName = fname, executionTime = exTime, didError = True, numTheorems = "N/A", maxSubgoals = "N/A", maxProofNodes = "N/A", totalSubgoals = "N/A", totalProofNodes = "N/A", maxExecutionTime = exTime, minExecutionTime = exTime }
                Right fs -> return $ getDiagnostics startTime endTime fs) `mapM` [1,2,3,4,5]

        averageDiagnostic ds = (head ds) { executionTime = sum (executionTime <$> ds) / realToFrac (length ds), maxExecutionTime = Data.List.foldl' max 0 (executionTime <$> ds), minExecutionTime = Data.List.foldl' min (executionTime . head $ ds) (executionTime <$> ds) }

        printInfos :: [DiagnosticInfo] -> IO ()
        printInfos infos = do
            -- Define the headers for your columns
            let headers = ["Module", "Theorems", "Total Subgoals", "Total Proof Nodes", "Max Subgoals", "Max Proof Nodes", "Avg. Time (s)", "Max Time (s)", "Min Time (s)"]

            -- Define how to turn a record into a list of Strings (one for each column)
            let toRow r = [ moduleName r
                        , numTheorems r
                        , totalSubgoals r
                        , totalProofNodes r
                        , maxSubgoals r
                        , maxProofNodes r
                        , showFFloat (Just 6) (executionTime r) ""
                        , showFFloat (Just 6) (maxExecutionTime r) ""
                        , showFFloat (Just 6) (minExecutionTime r) ""]

            -- Convert all records to rows
            let rows = map toRow infos

            -- Calculate the maximum width required for each column
            -- We include the headers in this calculation to ensure the title fits
            let allRows = headers : rows
            let columns = transpose allRows
            let colWidths = map (maximum . map length) columns

            -- Helper to pad a string with spaces to a specific width
            let pad width s = s ++ replicate (width - length s) ' '

            -- Helper to format a single row using the calculated widths
            let formatRow row = intercalate " | " $ zipWith pad colWidths row

            -- Create a separator line (e.g., "---+--------+...")
            let separator = intercalate "-+-" $ map (\w -> replicate w '-') colWidths

            -- 3. Printing
            -- Print Header
            putStr "\ESC[2J\ESC[H"
            putStrLn $ formatRow headers
            -- Print Separator
            putStrLn separator
            -- Print Data
            mapM_ (putStrLn . formatRow) rows

getDiagnostics :: UTCTime -> UTCTime -> ProofState m -> DiagnosticInfo
getDiagnostics st et s = DiagnosticInfo {
    moduleName = curModuleName s,
    executionTime = realToFrac $ diffUTCTime et st,
    maxExecutionTime = realToFrac $ diffUTCTime et st,
    minExecutionTime = realToFrac $ diffUTCTime et st,
    didError = False,
    numTheorems = show . length . Data.Map.toList $ theorems s,
    maxSubgoals = show $ Data.List.foldl' (\acc (n, i) -> max acc (numberOfSubgoals i)) 0 $ toList (theorems s),
    maxProofNodes = show $ Data.List.foldl' (\acc (n, i) -> max acc (proofSize (proofObject i))) 0 $ toList (theorems s),
    totalProofNodes = show . sum $ (\(n, i) -> proofSize (proofObject i)) <$> toList (theorems s),
    totalSubgoals = show . sum $ (\(n, i) -> numberOfSubgoals i) <$> toList (theorems s)
}

-- ==========================================
-- REPL Implementation
-- ==========================================

startRepl :: [String] -> IO ()
startRepl fnames = do
    initState <- loadImports (dropExtensions <$> fnames) emptyState
    putStrLn "--- STILL Interactive Mode (Type :q to quit) ---"
    replLoop initState

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
                        mainPrinter (Right newState)
                        replLoop newState

-- ==========================================
-- File Watcher
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
