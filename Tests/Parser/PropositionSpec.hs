module Tests.Parser.PropositionSpec (run) where

import Tests.Harness
import Parser.TermParsers (parseStringProp)
import SessionTypes.Kernel
import ECC.Kernel (FunctionalTerm(..))
import Data.IORef

parseProp :: String -> Either String Proposition
parseProp s = case parseStringProp s of
    Left err -> Left (show err)
    Right p  -> Right p

run :: IORef TestState -> IO ()
run ref = group ref "Parser.proposition" $ do

    -- Atoms
    assertRight ref "parse '1' (Unit)"           (parseProp "1")
    assertRight ref "parse 'Unit'"               (parseProp "Unit")
    assertRight ref "parse identifier 'A'"       (parseProp "A")
    assertRight ref "parse 'nu x. x'"            (parseProp "nu x. x")
    assertRight ref "parse '$Type 0' (Lift)"     (parseProp "$Type 0")
    assertRight ref "parse '$42'"                (parseProp "$42")

    -- Connectives
    assertRight ref "parse 'a -o b'"                (parseProp "a -o b")
    assertRight ref "parse 'a * b' (Tensor)"        (parseProp "a * b")
    assertRight ref "parse 'a & b' (With)"          (parseProp "a & b")
    assertRight ref "parse 'a + b' (Plus)"          (parseProp "a + b")
    assertRight ref "parse '!a' (Replication)"      (parseProp "!a")

    -- Quantifiers (first-order)
    assertRight ref "parse 'forall x : Type 0. 1'" (parseProp "forall x : Type 0. 1")
    assertRight ref "parse 'exists x : Type 0. 1'" (parseProp "exists x : Type 0. 1")

    -- Second-order (stype keyword)
    assertRight ref "parse 'forall x : stype. 1'"  (parseProp "forall x : stype. 1")
    assertRight ref "parse 'exists x : stype. 1'"  (parseProp "exists x : stype. 1")

    -- Recursive types
    assertRight ref "parse 'nu x. x'"              (parseProp "nu x. x")
    assertRight ref "parse 'nu x. x -o x'"         (parseProp "nu x. x -o x")

    -- Parenthesized
    assertRight ref "parse '(a -o b)'"             (parseProp "(a -o b)")
    assertRight ref "parse '(a * b) -o c'"         (parseProp "(a * b) -o c")

    -- Structure checks

    -- Implication produces Implication node
    case parseProp "a -o b" of
        Left e  -> assert ref "a -o b produces Implication" False
        Right p -> assert ref "a -o b produces Implication"
            (case p of Implication{} -> True; _ -> False)

    -- Tensor produces Tensor node
    case parseProp "a * b" of
        Left e  -> assert ref "a * b produces Tensor" False
        Right p -> assert ref "a * b produces Tensor"
            (case p of Tensor{} -> True; _ -> False)

    -- Unit
    case parseProp "1" of
        Left e  -> assert ref "'1' produces Unit" False
        Right p -> assert ref "'1' produces Unit" (p == Unit)

    -- Operator precedence: * binds tighter than -o
    -- so "a * b -o c" = "(a * b) -o c" = Implication (Tensor ...) ...
    case parseProp "a * b -o c" of
        Left e  -> assert ref "precedence: a * b -o c parses" False
        Right p -> assert ref "a * b -o c = (a*b) -o c  (* tighter than -o)"
            (case p of Implication (Tensor _ _) _ -> True; _ -> False)

    -- -o is right-associative: a -o b -o c = a -o (b -o c)
    case parseProp "a -o b -o c" of
        Left e  -> assert ref "-o right-assoc parses" False
        Right p -> assert ref "a -o b -o c is right-associative"
            (case p of Implication _ (Implication _ _) -> True; _ -> False)

    -- * is left-associative: a * b * c = (a * b) * c
    case parseProp "a * b * c" of
        Left e  -> assert ref "* left-assoc parses" False
        Right p -> assert ref "a * b * c is left-associative"
            (case p of Tensor (Tensor _ _) _ -> True; _ -> False)

    -- ! binds tightest (prefix): !a * b = (!a) * b
    case parseProp "!a * b" of
        Left e  -> assert ref "! binds tightly" False
        Right p -> assert ref "!a * b = (!a) * b"
            (case p of Tensor (Replication _) _ -> True; _ -> False)

    -- Forall2 via stype keyword
    case parseProp "forall X : stype. X" of
        Left e  -> assert ref "forall X : stype. X parses" False
        Right p -> assert ref "forall X : stype. X produces Forall2"
            (case p of Forall2{} -> True; _ -> False)

    -- nu produces TyNu
    case parseProp "nu x. x" of
        Left e  -> assert ref "nu x. x produces TyNu" False
        Right p -> assert ref "nu x. x produces TyNu"
            (case p of TyNu "x" (TyVar "x") -> True; _ -> False)

    -- Negative: empty string
    assertLeft ref "parse empty string fails" (parseProp "")

    -- Negative: bare connective without operands
    assertLeft ref "parse bare '-o' fails" (parseProp "-o")

    -- Negative: unclosed quantifier
    assertLeft ref "parse 'forall x :' fails (incomplete)" (parseProp "forall x :")
