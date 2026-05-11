module Tests.ECC.SubstSpec (run) where

import Tests.Harness
import ECC.Kernel
import Data.IORef

run :: IORef TestState -> IO ()
run ref = group ref "ECC.functionalSubst (capture-avoiding)" $ do

    -- Basic: substitute into a variable
    assert ref "Var x [Var y / x] = Var y"
        (alphaEquivalent
            (functionalSubst (Var "x") (Var "y") "x")
            (Var "y"))

    assert ref "Var z [Var y / x] = Var z  (z /= x, no-op)"
        (alphaEquivalent
            (functionalSubst (Var "z") (Var "y") "x")
            (Var "z"))

    -- Application distributes
    assert ref "App (Var f) (Var x) [Var g / f] = App (Var g) (Var x)"
        (alphaEquivalent
            (functionalSubst (App (Var "f") (Var "x")) (Var "g") "f")
            (App (Var "g") (Var "x")))

    -- Lambda: binder == substituted var → body unchanged (x is shadowed)
    assert ref "Lambda x A (Var x) [Var z / x] = Lambda x A (Var x)  (x shadowed)"
        (alphaEquivalent
            (functionalSubst (Lambda "x" (Var "A") (Var "x")) (Var "z") "x")
            (Lambda "x" (Var "A") (Var "x")))

    -- Lambda: x free in type, not captured in body
    assert ref "Lambda y (Var x) (Var y) [Var A / x] = Lambda y (Var A) (Var y)"
        (alphaEquivalent
            (functionalSubst (Lambda "y" (Var "x") (Var "y")) (Var "A") "x")
            (Lambda "y" (Var "A") (Var "y")))

    -- Capture-avoidance: substituting Var "y" for x in Lambda "y" Prop (Var "x")
    -- The binder y would capture the free y in the substituted term — must rename
    assert ref "Lambda y Prop (Var x) [Var y / x] avoids capture (renames binder)"
        (let result = functionalSubst (Lambda "y" Prop (Var "x")) (Var "y") "x"
         in case result of
                Lambda binder _ body ->
                    binder /= "y" && alphaEquivalent body (Var "y")
                _ -> False)

    -- Pi: binder == substituted var → type still gets subst, body unchanged
    assert ref "Pi x A (Var x) [Var z / x] = Pi x A (Var x)  (x shadowed)"
        (alphaEquivalent
            (functionalSubst (Pi "x" (Var "A") (Var "x")) (Var "z") "x")
            (Pi "x" (Var "A") (Var "x")))

    -- Pi capture-avoidance
    assert ref "Pi y Prop (Var x) [Var y / x] avoids capture"
        (let result = functionalSubst (Pi "y" Prop (Var "x")) (Var "y") "x"
         in case result of
                Pi binder _ body ->
                    binder /= "y" && alphaEquivalent body (Var "y")
                _ -> False)

    -- Sigma: binder scopes body only; type always gets substituted
    -- Sigma x (Var x) (Var x) [Var A / x]: binder x shadows in body, type Var x → Var A
    assert ref "Sigma x (Var x) (Var x) [Var A / x]: type subst'd, body unchanged"
        (alphaEquivalent
            (functionalSubst (Sigma "x" (Var "x") (Var "x")) (Var "A") "x")
            (Sigma "x" (Var "A") (Var "x")))

    -- Proj1
    assert ref "Proj1 (Var x) [Var A / x] = Proj1 (Var A)"
        (alphaEquivalent
            (functionalSubst (Proj1 (Var "x")) (Var "A") "x")
            (Proj1 (Var "A")))

    -- Proj2
    assert ref "Proj2 (Var x) [Var A / x] = Proj2 (Var A)"
        (alphaEquivalent
            (functionalSubst (Proj2 (Var "x")) (Var "A") "x")
            (Proj2 (Var "A")))

    -- No-op on type constructors
    assert ref "IntTy [Var A / x] = IntTy"
        (alphaEquivalent (functionalSubst IntTy (Var "A") "x") IntTy)
    assert ref "StringTy [Var A / x] = StringTy"
        (alphaEquivalent (functionalSubst StringTy (Var "A") "x") StringTy)
    assert ref "IntLit 5 [Var A / x] = IntLit 5"
        (alphaEquivalent (functionalSubst (IntLit 5) (Var "A") "x") (IntLit 5))
    assert ref "StringLit s [Var A / x] = StringLit s"
        (alphaEquivalent (functionalSubst (StringLit "s") (Var "A") "x") (StringLit "s"))
    assert ref "BuiltinFn add [Var A / x] = BuiltinFn add"
        (alphaEquivalent (functionalSubst (BuiltinFn "add") (Var "A") "x") (BuiltinFn "add"))

    -- Pair: binder scopes second type component only
    assert ref "Pair (Var x) (Var x) x (Var x) (Var x) [Var A / x]: first 2 subst'd"
        (alphaEquivalent
            (functionalSubst
                (Pair (Var "x") (Var "x") "x" (Var "x") (Var "x"))
                (Var "A") "x")
            (Pair (Var "A") (Var "A") "x" (Var "A") (Var "x")))

    -- Nested: subst inside a lambda body
    assert ref "Lambda z Prop (App (Var x) (Var z)) [Var A / x] = Lambda z Prop (App (Var A) (Var z))"
        (alphaEquivalent
            (functionalSubst
                (Lambda "z" Prop (App (Var "x") (Var "z")))
                (Var "A") "x")
            (Lambda "z" Prop (App (Var "A") (Var "z"))))

    -- Substituting FHoleTerm
    assert ref "FHoleTerm [Var A / x] = FHoleTerm"
        (alphaEquivalent (functionalSubst FHoleTerm (Var "A") "x") FHoleTerm)
