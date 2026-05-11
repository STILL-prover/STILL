module Tests.ECC.AlphaEquivSpec (run) where

import Tests.Harness
import ECC.Kernel
import Data.IORef

run :: IORef TestState -> IO ()
run ref = group ref "ECC.alphaEquivalent" $ do

    -- Reflexivity on atomic terms
    assert ref "Type 2 == Type 2"
        (alphaEquivalent (Type 2) (Type 2))
    assert ref "Prop == Prop"
        (alphaEquivalent Prop Prop)
    assert ref "Var x == Var x"
        (alphaEquivalent (Var "x") (Var "x"))
    assert ref "IntLit 42 == IntLit 42"
        (alphaEquivalent (IntLit 42) (IntLit 42))
    assert ref "IntTy == IntTy"
        (alphaEquivalent IntTy IntTy)
    assert ref "StringTy == StringTy"
        (alphaEquivalent StringTy StringTy)
    assert ref "StringLit hi == StringLit hi"
        (alphaEquivalent (StringLit "hi") (StringLit "hi"))
    assert ref "BuiltinFn add == BuiltinFn add"
        (alphaEquivalent (BuiltinFn "add") (BuiltinFn "add"))

    -- Lambda alpha-rename
    assert ref "Lambda x A x == Lambda y A y"
        (alphaEquivalent
            (Lambda "x" (Var "A") (Var "x"))
            (Lambda "y" (Var "A") (Var "y")))

    -- Pi alpha-rename
    assert ref "Pi x A x == Pi y A y"
        (alphaEquivalent
            (Pi "x" (Var "A") (Var "x"))
            (Pi "y" (Var "A") (Var "y")))

    -- Sigma alpha-rename
    assert ref "Sigma x A x == Sigma y A y"
        (alphaEquivalent
            (Sigma "x" (Var "A") (Var "x"))
            (Sigma "y" (Var "A") (Var "y")))

    -- Free var in body is not renamed
    assert ref "Lambda x A z == Lambda y A z (z free, unchanged)"
        (alphaEquivalent
            (Lambda "x" (Var "A") (Var "z"))
            (Lambda "y" (Var "A") (Var "z")))

    -- Nested binder: inner binder shadows outer rename
    assert ref "Lambda x A (Lambda x B x) == Lambda y A (Lambda z B z)"
        (alphaEquivalent
            (Lambda "x" (Var "A") (Lambda "x" (Var "B") (Var "x")))
            (Lambda "y" (Var "A") (Lambda "z" (Var "B") (Var "z"))))

    -- Application
    assert ref "App f x == App f x"
        (alphaEquivalent (App (Var "f") (Var "x")) (App (Var "f") (Var "x")))

    -- Proj1, Proj2
    assert ref "Proj1 (Var x) == Proj1 (Var x)"
        (alphaEquivalent (Proj1 (Var "x")) (Proj1 (Var "x")))
    assert ref "Proj2 (Var x) == Proj2 (Var x)"
        (alphaEquivalent (Proj2 (Var "x")) (Proj2 (Var "x")))

    -- FHoleTerm
    assert ref "FHoleTerm == FHoleTerm"
        (alphaEquivalent FHoleTerm FHoleTerm)

    -- Negative: different universe levels
    assert ref "Type 0 /= Type 1"
        (not $ alphaEquivalent (Type 0) (Type 1))

    -- Negative: Type vs Prop
    assert ref "Type 0 /= Prop"
        (not $ alphaEquivalent (Type 0) Prop)

    -- Negative: different free vars
    assert ref "Lambda x A x /= Lambda y A z (different body)"
        (not $ alphaEquivalent
            (Lambda "x" (Var "A") (Var "x"))
            (Lambda "y" (Var "A") (Var "z")))

    -- Negative: different literals
    assert ref "IntLit 1 /= IntLit 2"
        (not $ alphaEquivalent (IntLit 1) (IntLit 2))
    assert ref "StringLit a /= StringLit b"
        (not $ alphaEquivalent (StringLit "a") (StringLit "b"))

    -- Negative: different base types
    assert ref "IntTy /= StringTy"
        (not $ alphaEquivalent IntTy StringTy)

    -- Negative: different builtins
    assert ref "BuiltinFn add /= BuiltinFn mul"
        (not $ alphaEquivalent (BuiltinFn "add") (BuiltinFn "mul"))

    -- Negative: different constructors
    assert ref "Var x /= IntLit 0"
        (not $ alphaEquivalent (Var "x") (IntLit 0))
    assert ref "Lambda /= Pi (different binder kinds)"
        (not $ alphaEquivalent
            (Lambda "x" (Var "A") (Var "x"))
            (Pi "x" (Var "A") (Var "x")))
