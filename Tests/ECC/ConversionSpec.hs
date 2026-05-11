module Tests.ECC.ConversionSpec (run) where

import Tests.Harness
import ECC.Kernel
import Data.IORef

run :: IORef TestState -> IO ()
run ref = group ref "ECC.allConversionSteps + cumulativiyRelation" $ do

    -- allConversionSteps: irreducible term produces singleton list
    assert ref "Var x is irreducible: steps = [Var x]"
        (allConversionSteps (Var "x") == [Var "x"])
    assert ref "Type 0 is irreducible: single step"
        (length (allConversionSteps (Type 0)) == 1)
    assert ref "IntLit 5 is irreducible"
        (allConversionSteps (IntLit 5) == [IntLit 5])

    -- Beta reduction: (\x:A.x) z  ->  z
    let betaRedex = App (Lambda "x" (Var "A") (Var "x")) (Var "z")
    assert ref "beta: (\\x:A.x) z first step is redex itself"
        (head (allConversionSteps betaRedex) == betaRedex)
    assert ref "beta: (\\x:A.x) z reduces to Var z"
        (Var "z" `elem` allConversionSteps betaRedex)

    -- Sigma projection: proj1 (x,y):... → x
    let pair = Pair (Var "x") (Var "y") "t" (Var "A") (Var "B")
    assert ref "proj1 (Pair x y t A B) reduces to Var x"
        (Var "x" `elem` allConversionSteps (Proj1 pair))
    assert ref "proj2 (Pair x y t A B) reduces to Var y"
        (Var "y" `elem` allConversionSteps (Proj2 pair))

    -- Builtin arithmetic
    assert ref "#add 3 4 reduces to IntLit 7"
        (IntLit 7 `elem`
            allConversionSteps (App (App (BuiltinFn "add") (IntLit 3)) (IntLit 4)))
    assert ref "#sub 10 3 reduces to IntLit 7"
        (IntLit 7 `elem`
            allConversionSteps (App (App (BuiltinFn "sub") (IntLit 10)) (IntLit 3)))
    assert ref "#mul 2 5 reduces to IntLit 10"
        (IntLit 10 `elem`
            allConversionSteps (App (App (BuiltinFn "mul") (IntLit 2)) (IntLit 5)))
    assert ref "#neg 3 reduces to IntLit (-3)"
        (IntLit (-3) `elem`
            allConversionSteps (App (BuiltinFn "neg") (IntLit 3)))

    -- Reduction under application: inner redex reduces
    let innerRedex = App (Var "f") (App (Lambda "x" (Var "A") (Var "x")) (Var "z"))
    assert ref "f ((\\x:A.x) z) reduces to f z"
        (App (Var "f") (Var "z") `elem` allConversionSteps innerRedex)

    -- cumulativiyRelation
    assert ref "Prop <= Type 0"
        (cumulativiyRelation Prop (Type 0))
    assert ref "Type 0 <= Type 0"
        (cumulativiyRelation (Type 0) (Type 0))
    assert ref "Type 0 <= Type 1"
        (cumulativiyRelation (Type 0) (Type 1))
    assert ref "Type 0 <= Type 5"
        (cumulativiyRelation (Type 0) (Type 5))
    assert ref "Type 1 NOT <= Type 0"
        (not $ cumulativiyRelation (Type 1) (Type 0))
    assert ref "Type 0 NOT <= Prop"
        (not $ cumulativiyRelation (Type 0) Prop)

    -- Via beta equality: Var z <= (λx:A.x) z
    assert ref "Var z <= App (Lambda x A x) (Var z)  (beta equal)"
        (cumulativiyRelation
            (Var "z")
            (App (Lambda "x" (Var "A") (Var "x")) (Var "z")))

    -- Pi cumulativity: covariant in codomain, domain requires conversion equality
    assert ref "Pi x (Type 1) (Type 2) <= Pi x (Type 1) (Type 3)"
        (cumulativiyRelation
            (Pi "x" (Type 1) (Type 2))
            (Pi "x" (Type 1) (Type 3)))

    -- Pi: binder names must match (uses == not alpha-equiv)
    assert ref "Pi x (Type 1) (Type 2) NOT <= Pi y (Type 1) (Type 3) (names differ)"
        (not $ cumulativiyRelation
            (Pi "x" (Type 1) (Type 2))
            (Pi "y" (Type 1) (Type 3)))

    -- Pi: domain must be conversion-equal (not merely cumulative)
    assert ref "Pi x (Type 1) T NOT <= Pi x (Type 2) T  (domain Type 1 /~ Type 2)"
        (not $ cumulativiyRelation
            (Pi "x" (Type 1) (Type 3))
            (Pi "x" (Type 2) (Type 3)))

    -- Sigma cumulativity: both domain and codomain are cumulative
    assert ref "Sigma x (Type 1) (Type 2) <= Sigma x (Type 1) (Type 3)"
        (cumulativiyRelation
            (Sigma "x" (Type 1) (Type 2))
            (Sigma "x" (Type 1) (Type 3)))

    assert ref "Sigma x (Type 0) (Type 0) <= Sigma x (Type 1) (Type 1)"
        (cumulativiyRelation
            (Sigma "x" (Type 0) (Type 0))
            (Sigma "x" (Type 1) (Type 1)))

    -- Doctest from ECC/Kernel.hs:663
    assert ref "Sigma x (Type 1) (Type 2) NOT <= Sigma x (Type 2) (Type 3) [doctest]"
        (cumulativiyRelation
            (Sigma "x" (Type 1) (Type 2))
            (Sigma "x" (Type 2) (Type 3)))
