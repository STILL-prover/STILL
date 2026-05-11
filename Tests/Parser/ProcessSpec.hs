module Tests.Parser.ProcessSpec (run) where

import Tests.Harness
import Parser.TermParsers (parseStringProcess)
import SessionTypes.Kernel
import ECC.Kernel (FunctionalTerm(..))
import Data.IORef

parseProc :: String -> Either String Process
parseProc s = case parseStringProcess s of
    Left err -> Left (show err)
    Right p  -> Right p

run :: IORef TestState -> IO ()
run ref = group ref "Parser.process" $ do

    -- Basic atomic processes
    assertRight ref "parse 'stop'"                       (parseProc "stop")
    assertRight ref "parse '0'"                          (parseProc "0")

    -- Link
    assertRight ref "parse '[x <-> y]'"                  (parseProc "[x <-> y]")
    assertRight ref "parse '[a <-> b]'"                  (parseProc "[a <-> b]")

    -- Parallel composition
    assertRight ref "parse 'stop | stop'"                (parseProc "stop | stop")
    assertRight ref "parse 'stop | stop | stop'"         (parseProc "stop | stop | stop")

    -- Send/Receive
    assertRight ref "parse 'x[y].stop'"                  (parseProc "x[y].stop")
    assertRight ref "parse 'x(y).stop'"                  (parseProc "x(y).stop")

    -- Plus injections
    assertRight ref "parse 'x.inl;stop'"                 (parseProc "x.inl;stop")
    assertRight ref "parse 'x.inr;stop'"                 (parseProc "x.inr;stop")

    -- Case
    assertRight ref "parse 'x.case(inl: stop, inr: stop)'" (parseProc "x.case(inl: stop, inr: stop)")

    -- Nu restriction
    assertRight ref "parse '(nu x:1) stop'"              (parseProc "(nu x:1) stop")
    assertRight ref "parse '(nu x:a -o b) stop'"         (parseProc "(nu x:a -o b) stop")

    -- Replicated receive
    assertRight ref "parse '!x(y).stop'"                 (parseProc "!x(y).stop")

    -- LiftTerm via inline-bracket syntax
    assertRight ref "parse '[z <- 42]'"                  (parseProc "[z <- 42]")
    assertRight ref "parse '[c <- x]'"                   (parseProc "[c <- x]")

    -- Print
    assertRight ref "parse 'print[42].stop'"             (parseProc "print[42].stop")

    -- Structure checks

    -- Halt
    case parseProc "stop" of
        Left e  -> assert ref "stop produces Halt" False
        Right p -> assert ref "stop produces Halt" (p == Halt)

    case parseProc "0" of
        Left e  -> assert ref "0 produces Halt" False
        Right p -> assert ref "0 produces Halt" (p == Halt)

    -- Link structure
    case parseProc "[x <-> y]" of
        Left e  -> assert ref "[x <-> y] produces Link" False
        Right p -> assert ref "[x <-> y] produces Link x y"
            (case p of Link "x" "y" -> True; _ -> False)

    -- Parallel is right-associative: stop | stop | stop = stop | (stop | stop)
    case parseProc "stop | stop | stop" of
        Left e  -> assert ref "parallel right-assoc parses" False
        Right p -> assert ref "stop | stop | stop is right-associative"
            (case p of
                ParallelComposition _ (ParallelComposition _ _) -> True
                _ -> False)

    -- Send: x[y].P
    case parseProc "x[y].stop" of
        Left e  -> assert ref "x[y].stop produces Send" False
        Right p -> assert ref "x[y].stop produces Send x y Halt"
            (case p of Send "x" "y" Halt -> True; _ -> False)

    -- Receive: x(y).P
    case parseProc "x(y).stop" of
        Left e  -> assert ref "x(y).stop produces Receive" False
        Right p -> assert ref "x(y).stop produces Receive x y Halt"
            (case p of Receive "x" "y" Halt -> True; _ -> False)

    -- Case structure
    case parseProc "x.case(inl: stop, inr: stop)" of
        Left e  -> assert ref "case produces Case" False
        Right p -> assert ref "x.case(inl: stop, inr: stop) produces Case x Halt Halt"
            (case p of Case "x" Halt Halt -> True; _ -> False)

    -- LiftTerm structure: [z <- 42] produces LiftTerm "z" (IntLit 42)
    case parseProc "[z <- 42]" of
        Left e  -> assert ref "[z <- 42] produces LiftTerm" False
        Right p -> assert ref "[z <- 42] produces LiftTerm z (IntLit 42)"
            (case p of LiftTerm "z" (IntLit 42) -> True; _ -> False)

    -- Link is still parsed correctly when "<->" is present
    case parseProc "[x <-> y]" of
        Left e  -> assert ref "[x <-> y] still parses as Link after fix" False
        Right p -> assert ref "[x <-> y] still parses as Link x y after fix"
            (case p of Link "x" "y" -> True; _ -> False)

    -- Negative: empty string
    assertLeft ref "parse empty string fails"     (parseProc "")

    -- Negative: bare '|' without operands
    assertLeft ref "parse bare '|' fails"         (parseProc "|")

    -- Negative: incomplete send (missing continuation)
    assertLeft ref "parse 'x[y].' fails"          (parseProc "x[y].")
