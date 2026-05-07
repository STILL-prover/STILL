module Interpreter.Runtime (runProcess) where

import SessionTypes.Kernel (Process(..))
import ECC.Kernel (FunctionalTerm(..), allConversionSteps, functionalSubst)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Control.Concurrent (forkIO, MVar, newEmptyMVar, putMVar, takeMVar, Chan, newChan, readChan, writeChan, ThreadId)
import Data.IORef (IORef, modifyIORef, newIORef)
import Control.Exception (evaluate)

-- ---------------------------------------------------------------------------
-- Value and Channel types
-- ---------------------------------------------------------------------------

data Value
    = VInt  Integer
    | VStr  String
    | VUnit
    | VInl  Value
    | VInr  Value
    | VChan Channel
    | VTerm FunctionalTerm
    | VRecFn ([String] -> IO ())

data Channel
    = LinearChan (MVar Value)
    | RepChan    (Chan Value)

type Env     = Map String Value
type ChanEnv = Map String Channel

-- ---------------------------------------------------------------------------
-- Value display
-- ---------------------------------------------------------------------------

showValue :: Value -> String
showValue (VInt n)  = show n
showValue (VStr s)  = s
showValue VUnit     = "()"
showValue (VInl v)  = "inl(" ++ showValue v ++ ")"
showValue (VInr v)  = "inr(" ++ showValue v ++ ")"
showValue (VChan _) = "<channel>"
showValue (VTerm t) = show t
showValue (VRecFn _) = "<fn>"

-- ---------------------------------------------------------------------------
-- FunctionalTerm evaluation
-- ---------------------------------------------------------------------------

evalFT :: Env -> FunctionalTerm -> IO Value
evalFT env t = do
    let t1 = Map.foldlWithKey substOne t env
        nf  = last (allConversionSteps t1)
    evaluate (termToValue nf)
  where
    substOne acc k v = functionalSubst acc (valueToTerm v) k

    termToValue (IntLit n)    = VInt n
    termToValue (StringLit s) = VStr s
    termToValue other         = VTerm other

    valueToTerm (VInt n)    = IntLit n
    valueToTerm (VStr s)    = StringLit s
    valueToTerm (VTerm t)   = t
    valueToTerm _           = FHoleTerm

-- ---------------------------------------------------------------------------
-- Channel I/O helpers
-- ---------------------------------------------------------------------------

writeChannel :: Channel -> Value -> IO ()
writeChannel (LinearChan mv) v = putMVar mv v
writeChannel (RepChan ch)    v = writeChan ch v

readChannel :: Channel -> IO Value
readChannel (LinearChan mv) = takeMVar mv
readChannel (RepChan ch)    = readChan ch

lookupChan :: ChanEnv -> String -> Channel
lookupChan ce x = case Map.lookup x ce of
    Just ch -> ch
    Nothing -> error $ "Runtime: channel not found: " ++ x

lookupVal :: Env -> String -> Value
lookupVal env x = case Map.lookup x env of
    Just v -> v
    Nothing -> error $ "Runtime: variable not found: " ++ x

-- ---------------------------------------------------------------------------
-- Process interpreter
-- ---------------------------------------------------------------------------

runProcess :: Env -> ChanEnv -> IORef [ThreadId] -> Process -> IO ()

runProcess _   _  _    Halt = return ()

runProcess env ce tids (ParallelComposition p q) = do
    done <- newEmptyMVar
    tid <- forkIO (runProcess env ce tids p >> putMVar done ())
    modifyIORef tids (tid:)
    runProcess env ce tids q
    takeMVar done

runProcess env ce tids (Nu x _ p) = do
    mv <- newEmptyMVar
    let ce' = Map.insert x (LinearChan mv) ce
    runProcess env ce' tids p

runProcess env ce tids (Send x y p) = do
    let ch = lookupChan ce x
        v  = VChan (lookupChan ce y)
    writeChannel ch v
    runProcess env ce tids p

runProcess env ce tids (SendTerm x m p) = do
    v <- evalFT env m
    writeChannel (lookupChan ce x) v
    runProcess env ce tids p

runProcess env ce tids (SendType x _ p) =
    runProcess env ce tids p

runProcess env ce tids (Receive x y p) = do
    v <- readChannel (lookupChan ce x)
    let (env', ce') = bindValue y v env ce
    runProcess env' ce' tids p

runProcess env ce tids (ReplicateReceive x y p) = do
    let loop = do
            v <- readChannel (lookupChan ce x)
            let (env', ce') = bindValue y v env ce
            tid <- forkIO (runProcess env' ce' tids p >> loop)
            modifyIORef tids (tid:)
    loop

runProcess env ce tids (SendInl x p) = do
    writeChannel (lookupChan ce x) (VInl VUnit)
    runProcess env ce tids p

runProcess env ce tids (SendInr x p) = do
    writeChannel (lookupChan ce x) (VInr VUnit)
    runProcess env ce tids p

runProcess env ce tids (Case x p q) = do
    v <- readChannel (lookupChan ce x)
    case v of
        VInl _ -> runProcess env ce tids p
        VInr _ -> runProcess env ce tids q
        _ -> error "Runtime: Case received non-injection value"

runProcess env ce tids (Link x y) = do
    let chX = lookupChan ce x
        chY = lookupChan ce y
    v <- readChannel chX
    writeChannel chY v

runProcess env ce tids (LiftTerm x m) = do
    v <- evalFT env m
    writeChannel (lookupChan ce x) v

runProcess env ce tids (Print m p) = do
    v <- evalFT env m
    putStrLn (showValue v)
    runProcess env ce tids p

runProcess env ce tids (ReadLine x p) = do
    ln <- getLine
    let env' = Map.insert x (VStr ln) env
    runProcess env' ce tids p

runProcess env ce tids (Corec nm params body initArgs) = do
    let recEnv = Map.insert nm (VRecFn callFn) env
        callFn argNames =
            let argEnv = Map.fromList (zip params (map (\n -> lookupVal env n) argNames))
            in runProcess (Map.union argEnv recEnv) ce tids body
    callFn initArgs

runProcess env ce tids (Call nm args) =
    case Map.lookup nm env of
        Just (VRecFn f) -> f args
        _ -> error $ "Runtime: recursive function not found: " ++ nm

runProcess _ _ _ HoleTerm = error "Runtime: hole in executed process"

-- ---------------------------------------------------------------------------
-- Helper: bind a received value as a channel or term variable
-- ---------------------------------------------------------------------------

bindValue :: String -> Value -> Env -> ChanEnv -> (Env, ChanEnv)
bindValue name (VChan ch) env ce = (env, Map.insert name ch ce)
bindValue name v          env ce = (Map.insert name v env, ce)
