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

import SessionTypes.Tactics (ProofState(..), Theorem (proofObject, numberOfSubgoals), allSubgoalNames)
import SessionTypes.Kernel
import Parser.CmdParsers (parseFile, parseStringCommand, CommandSpan (spanValue, spanRange, CommandSpan, spanText, trimmedRange), Command, parseFileSpans, evalCommand, evalCommandM, parseStringCommandSpan, Range (Range))
import Utils.Display
import Data.List (intercalate, transpose, foldl')
import Data.Map (toList)
import Data.Time (formatTime, defaultTimeLocale)
import Numeric (showFFloat)
import Utils.Misc (namesInOrder)
import Control.Monad (unless)
import ECC.Kernel (emptyContext)
import Text.Parsec (sourceLine, sourceColumn)
import Text.Read (readMaybe)
import Utils.Server
import MCP.Server (startMcpServer)

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
        ("serve":[])          -> startServer
        ("serve-mcp":[])      -> startMcpServer
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
                Right fs -> putStrLn (unlines (reverse (outputs fs))) >> unless (null (errors fs)) (putStrLn "Errors:" >> putStrLn (unlines (reverse (errors fs))))

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

getDiagnostics :: UTCTime -> UTCTime -> ProofState -> DiagnosticInfo
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

replLoop :: ProofState -> IO ()
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
                case parseStringCommandSpan input of
                    Left err -> do
                        putStrLn $ "Parse Error: " ++ show err
                        replLoop currentState
                    Right sp -> do
                        newState <- evalCommandM (spanValue sp) currentState
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

-- ===========================
-- Editor Integration
-- ===========================

data Request = ReqPing
    | ReqStateAt {
        reqPath :: FilePath,
        reqText :: String,
        reqLine :: Int, -- VSCode is 0-based
        reqCharacter :: Int -- VSCode is 0-based
    }
    deriving (Read, Show)

escapeField :: String -> String
escapeField = concatMap go
  where
    go '\\' = "\\\\"
    go ','  = "\\,"
    go '\n' = "\\n"
    go '\r' = "\\r"
    go c    = [c]

unescapeField :: String -> String
unescapeField [] = []
unescapeField ('\\':'n':xs)  = '\n' : unescapeField xs
unescapeField ('\\':'r':xs)  = '\r' : unescapeField xs
unescapeField ('\\':',':xs)  = ','  : unescapeField xs
unescapeField ('\\':'\\':xs) = '\\' : unescapeField xs
unescapeField ('\\':x:xs)    = x    : unescapeField xs
unescapeField (x:xs)         = x    : unescapeField xs

splitEscapedCommas :: String -> [String]
splitEscapedCommas = go [] [] 
  where
    go acc cur [] = reverse (reverse cur : acc)
    go acc cur ('\\':x:xs) = go acc (x:'\\':cur) xs
    go acc cur (',':xs)    = go (reverse cur : acc) [] xs
    go acc cur (x:xs)      = go acc (x:cur) xs

parseRequestLine :: String -> Either String Request
parseRequestLine line | line == "ping" = Right ReqPing
                      | otherwise =
    case splitEscapedCommas line of
        ["stateAt", lineStr, colStr, pathField, contentField] ->
            case (reads lineStr, reads colStr) of
            ([(ln, "")], [(col, "")]) ->
                Right $
                ReqStateAt { reqPath = unescapeField pathField, reqText = unescapeField contentField, reqLine = ln, reqCharacter = col }
            _ -> Left "Bad stateAt line/column"
        _ -> Left "Unknown request"

startServer :: IO ()
startServer = do
  hSetEncoding stdin utf8
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  hSetBuffering stdin LineBuffering
  hSetBuffering stdout LineBuffering
  loop
  where
    loop = do
      done <- isEOF
      if done then
        pure ()
      else do
        line <- getLine
        case parseRequestLine line of
          Left err -> do
            putStrLn ("error," ++ escapeField err)
            loop
          Right req -> do
            resp <- handleRequestPlain req
            putStrLn resp
            loop

handleRequestPlain :: Request -> IO String
handleRequestPlain ReqPing = return "pong"
handleRequestPlain (ReqStateAt path text line0 col0) = do
  let line = line0 + 1
      col  = col0 + 1
  res <- runProofScriptDetailed path text
  pure $ case res of
    Left err -> "error," ++ escapeField err
    Right ps ->
      case findSnapshotAt ps line col of
        Nothing ->
          "error," ++ escapeField "No command found at this position."
        Just (sp, snap) ->
          let Range s e = trimmedRange sp
          in intercalate ","
               [ "ok"
               , show (sourceLine s - 1)
               , show (sourceColumn s - 1)
               , show (sourceLine e - 1)
               , show (sourceColumn e - 1)
               , escapeField (spanText sp)
               , escapeField (renderState (afterState snap))
               ]
