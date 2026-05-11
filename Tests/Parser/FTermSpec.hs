module Tests.Parser.FTermSpec (run) where

import Tests.Harness
import Parser.TermParsers (parseStringTerm, fTerm)
import ECC.Kernel
import Text.Parsec (parse, eof)
import Data.IORef

parseFT :: String -> Either String FunctionalTerm
parseFT s = case parseStringTerm s of
    Left err -> Left (show err)
    Right t  -> Right t

run :: IORef TestState -> IO ()
run ref = group ref "Parser.fTerm" $ do

    -- Atomic terms
    assertRight ref "parse 'Type 0'"     (parseFT "Type 0")
    assertRight ref "parse 'Type 1'"     (parseFT "Type 1")
    assertRight ref "parse 'Prop'"       (parseFT "Prop")
    assertRight ref "parse 'x'"          (parseFT "x")
    assertRight ref "parse 'foo_bar'"    (parseFT "foo_bar")
    assertRight ref "parse '42'"         (parseFT "42")
    assertRight ref "parse '0'"          (parseFT "0")
    assertRight ref "parse 'Int'"        (parseFT "Int")
    assertRight ref "parse 'String'"     (parseFT "String")
    assertRight ref "parse '#add'"       (parseFT "#add")
    assertRight ref "parse '#mul'"       (parseFT "#mul")

    -- Lambda (uses backslash syntax)
    assertRight ref "parse lambda '\\\\x : Prop. x'"
        (parseFT "\\x : Prop. x")
    assertRight ref "parse lambda '\\\\A : Type 1. A'"
        (parseFT "\\A : Type 1. A")

    -- Pi (uses 'Pi' keyword, not bracket syntax)
    assertRight ref "parse Pi 'Pi x : Type 0. x'"
        (parseFT "Pi x : Type 0. x")
    assertRight ref "parse Pi 'Pi A : Type 1. Type 1'"
        (parseFT "Pi A : Type 1. Type 1")

    -- Sigma (uses 'Sigma' keyword)
    assertRight ref "parse Sigma 'Sigma x : Type 0. Type 0'"
        (parseFT "Sigma x : Type 0. Type 0")

    -- Application (left-associative juxtaposition)
    assertRight ref "parse application 'f x'"
        (parseFT "f x")
    assertRight ref "parse application '#add 3 4'"
        (parseFT "#add 3 4")

    -- Parenthesized
    assertRight ref "parse '(Type 0)'"
        (parseFT "(Type 0)")

    -- proj1, proj2 (if supported)
    assertRight ref "parse 'proj1 x'"
        (parseFT "proj1 x")
    assertRight ref "parse 'proj2 x'"
        (parseFT "proj2 x")

    -- String literal
    assertRight ref "parse single-quoted string '\\'hello\\''"
        (parseFT "'hello'")
    assertRight ref "parse empty string '\\'\\''"
        (parseFT "''")

    -- Structure checks: verify correct AST nodes
    case parseFT "\\A : Type 1. A" of
        Left e  -> assert ref "lambda parse produces Lambda node" False
        Right t -> assert ref "lambda produces Lambda node"
            (case t of Lambda{} -> True; _ -> False)

    case parseFT "Pi x : Prop. x" of
        Left e  -> assert ref "Pi parse produces Pi node" False
        Right t -> assert ref "Pi x : Prop. x produces Pi node"
            (case t of Pi{} -> True; _ -> False)

    case parseFT "f x" of
        Left e  -> assert ref "application produces App node" False
        Right t -> assert ref "application produces App node"
            (case t of App{} -> True; _ -> False)

    case parseFT "42" of
        Left e  -> assert ref "integer literal produces IntLit" False
        Right t -> assert ref "integer literal produces IntLit 42"
            (t == IntLit 42)

    case parseFT "Type 2" of
        Left e  -> assert ref "Type 2 produces Type node" False
        Right t -> assert ref "Type 2 produces Type 2"
            (t == Type 2)

    -- Application is left-associative: f x y = (f x) y
    case parseFT "f x y" of
        Left e  -> assert ref "f x y parse succeeds" False
        Right t -> assert ref "f x y is left-associative: (f x) y"
            (case t of
                App (App (Var "f") (Var "x")) (Var "y") -> True
                _ -> False)

    -- Negative: empty string
    assertLeft ref "parse empty string fails"
        (parseFT "")

    -- Negative: incomplete lambda (missing body)
    assertLeft ref "parse lone '\\\\' fails"
        (parseFT "\\")

    -- Negative: unclosed Pi bracket
    assertLeft ref "parse unclosed '[x : Prop.' fails"
        (parseFT "[x : Prop.")
