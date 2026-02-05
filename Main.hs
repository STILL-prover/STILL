module Main where

import System.IO
import System.Directory (getModificationTime, doesFileExist)
import System.Environment (getArgs)
import Control.Concurrent (threadDelay)
import Control.Exception (catch, IOException)
import Data.Time.Clock (UTCTime)

runMyLogic :: String -> String
runMyLogic content = 
    let lineCount = length (lines content)
        wordCount = length (words content)
    in  "  [Result] Lines: " ++ show lineCount ++ ", Words: " ++ show wordCount

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering -- Ensures prompts appear immediately
    args <- getArgs
    case args of
        ("watch":fileName:[]) -> startWatcher fileName
        ("watch":[])          -> startWatcher "data.txt"

        -- REPL Mode (User typed: ./still repl)
        ("repl":_) -> startRepl

-- ==========================================
-- REPL IMPLEMENTATION (Interactive Mode)
-- ==========================================
startRepl :: IO ()
startRepl = do
    putStrLn "--- Interactive Mode (Type :q to quit) ---"
    replLoop

replLoop :: IO ()
replLoop = do
    putStr "Logic> " -- The Prompt
    
    -- Check for End of File (Ctrl+D)
    done <- isEOF
    if done 
        then putStrLn "\nGoodbye!"
        else do
            input <- getLine
            if input `elem` [":q", "quit", "exit"]
                then putStrLn "Goodbye!"
                else do
                    -- Run the logic on the input line
                    putStrLn (runMyLogic input)
                    -- Loop back to the start
                    replLoop

-- ==========================================
-- WATCHER IMPLEMENTATION (File Mode)
-- ==========================================
startWatcher :: FilePath -> IO ()
startWatcher targetFile = do
    putStrLn $ "Watching " ++ targetFile ++ " ... (Ctrl+C to stop)"

    exists <- doesFileExist targetFile
    if not exists then writeFile targetFile "" else return ()

    initialTime <- getModificationTime targetFile
    initialContent <- readFileSafe targetFile
    putStrLn (runMyLogic initialContent)

    watchLoop targetFile initialTime

watchLoop :: FilePath -> UTCTime -> IO ()
watchLoop filePath lastModified = do
    threadDelay 1000000 -- 1 second
    exists <- doesFileExist filePath
    if not exists
        then watchLoop filePath lastModified
        else do
            currentModified <- getModificationTime filePath
            if currentModified > lastModified
                then do
                    putStrLn $ "\n[Change detected in " ++ filePath ++ "]"
                    content <- readFileSafe filePath
                    putStrLn (runMyLogic content)
                    watchLoop filePath currentModified
                else 
                    watchLoop filePath lastModified

readFileSafe :: FilePath -> IO String
readFileSafe path = catch (readFile path) (\e -> let _ = (e :: IOException) in return "")