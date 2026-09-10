module Main where

import System.IO
import System.Directory (getModificationTime, doesFileExist)
import System.Environment (getArgs)
import System.Exit (exitWith, ExitCode(..))
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
import Control.Monad (unless, when)
import ECC.Kernel (emptyContext)
import Text.Parsec (sourceLine, sourceColumn)
import Text.Read (readMaybe)
import Utils.Server
import Utils.Runner
import MCP.Server (startMcpServer)


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
        ("benchmark":fnames)  -> runDiagnostics fnames
        ("serve":[])          -> startServer
        ("serve-mcp":[])      -> startMcpServer
        (fname:fnames)        -> runScripts (fname:fnames)
        []                    -> startRepl []
    where
        -- Run each script in turn. The process exits with status 1 if any
        -- script could not be read or parsed, reported an error, or ended
        -- with a proof still in progress; otherwise it exits with status 0.
        runScripts :: [String] -> IO ()
        runScripts fnames = do
            oks <- mapM runOne fnames
            unless (and oks) $ exitWith (ExitFailure 1)
          where
            runOne fname = do
                putStrLn $ "Running: " ++ fname
                r <- runScriptFile fname
                putStr (scriptOutput r)
                unless (null (scriptProblems r)) $ putStrLn "Errors:" >> putStr (unlines (scriptProblems r))
                putStrLn ""
                return (scriptOk r)

        -- Each script is run five times for timing. Only the results table is
        -- written to stdout; problems are reported once per script on stderr.
        runDiagnostics :: [String] -> IO ()
        runDiagnostics fnames = do
            infos <- mapM benchOne fnames
            putStr (renderResultsTable infos)
            when (any didError infos) $ exitWith (ExitFailure 1)
          where
            benchOne fname = do
                (info, problems) <- benchmarkFile 5 fname
                unless (null problems) $ hPutStrLn stderr (fname ++ ":\n" ++ unlines problems)
                return info

-- ==========================================
-- REPL Implementation
-- ==========================================

startRepl :: [String] -> IO ()
startRepl fnames = do
    initState <- loadImports "." (dropExtensions <$> fnames) emptyState
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
        reqLine :: Int, -- 0-based
        reqCharacter :: Int -- 0-based
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
