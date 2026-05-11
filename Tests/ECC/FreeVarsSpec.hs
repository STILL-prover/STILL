module Tests.ECC.FreeVarsSpec (run) where

import Tests.Harness
import ECC.Kernel
import qualified Data.Set as S
import Data.IORef

run :: IORef TestState -> IO ()
run ref = group ref "ECC.functionalFreeVariables" $ do

    -- Atomic terms with no free vars
    assertEqual ref "Type 0 has no free vars"
        S.empty (functionalFreeVariables (Type 0))
    assertEqual ref "Prop has no free vars"
        S.empty (functionalFreeVariables Prop)
    assertEqual ref "IntTy has no free vars"
        S.empty (functionalFreeVariables IntTy)
    assertEqual ref "StringTy has no free vars"
        S.empty (functionalFreeVariables StringTy)
    assertEqual ref "IntLit 5 has no free vars"
        S.empty (functionalFreeVariables (IntLit 5))
    assertEqual ref "StringLit has no free vars"
        S.empty (functionalFreeVariables (StringLit "hello"))
    assertEqual ref "BuiltinFn has no free vars"
        S.empty (functionalFreeVariables (BuiltinFn "add"))
    assertEqual ref "FHoleTerm has no free vars"
        S.empty (functionalFreeVariables FHoleTerm)

    -- Variable
    assertEqual ref "Var x has {x}"
        (S.singleton "x") (functionalFreeVariables (Var "x"))

    -- Application: union of free vars
    assertEqual ref "App (Var f) (Var x) has {f,x}"
        (S.fromList ["f", "x"])
        (functionalFreeVariables (App (Var "f") (Var "x")))

    -- Lambda: binder removed from body, type kept
    assertEqual ref "Lambda x (Var A) (Var x) has {A} (x is bound)"
        (S.singleton "A")
        (functionalFreeVariables (Lambda "x" (Var "A") (Var "x")))

    assertEqual ref "Lambda x (Var A) (App (Var y) (Var x)) has {A,y}"
        (S.fromList ["A", "y"])
        (functionalFreeVariables (Lambda "x" (Var "A") (App (Var "y") (Var "x"))))

    -- Lambda: x free in type position is kept
    assertEqual ref "Lambda y (Var x) (Var y) has {x} (y bound, x free in type)"
        (S.singleton "x")
        (functionalFreeVariables (Lambda "y" (Var "x") (Var "y")))

    -- Pi: same binding rules as Lambda
    assertEqual ref "Pi x (Var A) (Var x) has {A}"
        (S.singleton "A")
        (functionalFreeVariables (Pi "x" (Var "A") (Var "x")))

    -- Sigma: binder scopes over second component only
    assertEqual ref "Sigma x (Var A) (App (Var B) (Var x)) has {A,B}"
        (S.fromList ["A", "B"])
        (functionalFreeVariables (Sigma "x" (Var "A") (App (Var "B") (Var "x"))))

    -- Proj1, Proj2
    assertEqual ref "Proj1 (Var x) has {x}"
        (S.singleton "x")
        (functionalFreeVariables (Proj1 (Var "x")))
    assertEqual ref "Proj2 (Var x) has {x}"
        (S.singleton "x")
        (functionalFreeVariables (Proj2 (Var "x")))

    -- Doctest-inspired example from ECC/Kernel.hs line 145.
    -- Note: "T" appears free in the Lambda type position, so the real free set is {A,B,T,y,z}.
    -- The original doctest in the source omits T (it appears to be outdated).
    let doctestTerm =
            App
              (App (Lambda "z" (Var "T") (Var "z")) (Var "z"))
              (Lambda "x" (Var "A") (App (Var "y") (Pi "w" (Var "B") (Var "x"))))
    assertEqual ref "free vars include T (free in Lambda type), A, B, y, z"
        (S.fromList ["A", "B", "T", "y", "z"])
        (functionalFreeVariables doctestTerm)
