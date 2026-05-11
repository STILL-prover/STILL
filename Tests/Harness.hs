module Tests.Harness where

import Control.Exception (SomeException, try, evaluate)
import Data.IORef
import System.Exit (exitFailure)
import Control.Monad (when)

data TestState = TestState
    { passed   :: Int
    , failed   :: Int
    , failMsgs :: [String]
    }

newTestState :: IO (IORef TestState)
newTestState = newIORef (TestState 0 0 [])

assert :: IORef TestState -> String -> Bool -> IO ()
assert ref label ok = do
    s <- readIORef ref
    if ok
        then do
            writeIORef ref s { passed = passed s + 1 }
            putStrLn $ "  PASS: " ++ label
        else do
            let msg = "  FAIL: " ++ label
            writeIORef ref s
                { failed   = failed s + 1
                , failMsgs = msg : failMsgs s
                }
            putStrLn msg

assertEqual :: (Eq a, Show a) => IORef TestState -> String -> a -> a -> IO ()
assertEqual ref label expected actual =
    assert ref label' (expected == actual)
  where
    label'
        | expected == actual = label
        | otherwise = label
            ++ "\n    expected: " ++ show expected
            ++ "\n    actual:   " ++ show actual

assertLeft :: Show b => IORef TestState -> String -> Either a b -> IO ()
assertLeft ref label e =
    assert ref label $ case e of
        Left _  -> True
        Right v -> False

assertRight :: Show a => IORef TestState -> String -> Either a b -> IO ()
assertRight ref label e =
    assert ref label $ case e of
        Right _ -> True
        Left v  -> False

group :: IORef TestState -> String -> IO () -> IO ()
group ref name tests = do
    putStrLn $ "\n=== " ++ name ++ " ==="
    tests

finish :: IORef TestState -> IO ()
finish ref = do
    s <- readIORef ref
    putStrLn $ "\n----------------------------------------"
    putStrLn $ "Results: " ++ show (passed s) ++ " passed, "
                            ++ show (failed s) ++ " failed."
    when (failed s > 0) $ do
        putStrLn "\nFailed tests:"
        mapM_ putStrLn (reverse (failMsgs s))
        exitFailure
