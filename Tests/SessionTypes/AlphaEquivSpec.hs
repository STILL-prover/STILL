module Tests.SessionTypes.AlphaEquivSpec (run) where

import Tests.Harness
import SessionTypes.Kernel
import ECC.Kernel (FunctionalTerm(..))
import Data.IORef

run :: IORef TestState -> IO ()
run ref = group ref "SessionTypes.alphaEquivalent (Proposition)" $ do

    -- Reflexivity
    assert ref "Unit == Unit"
        (alphaEquivalent Unit Unit)
    assert ref "Lift (Var x) == Lift (Var x)"
        (alphaEquivalent (Lift (Var "x")) (Lift (Var "x")))
    assert ref "Replication Unit == Replication Unit"
        (alphaEquivalent (Replication Unit) (Replication Unit))

    -- Structural
    assert ref "Implication Unit Unit == Implication Unit Unit"
        (alphaEquivalent (Implication Unit Unit) (Implication Unit Unit))
    assert ref "Tensor Unit Unit == Tensor Unit Unit"
        (alphaEquivalent (Tensor Unit Unit) (Tensor Unit Unit))
    assert ref "With Unit Unit == With Unit Unit"
        (alphaEquivalent (With Unit Unit) (With Unit Unit))
    assert ref "Plus Unit Unit == Plus Unit Unit"
        (alphaEquivalent (Plus Unit Unit) (Plus Unit Unit))

    -- TyVar
    assert ref "TyVar x == TyVar x"
        (alphaEquivalent (TyVar "x") (TyVar "x"))

    -- Forall: alpha-rename bound variable
    assert ref "Forall x (Type 1) (Lift (Var x)) == Forall y (Type 1) (Lift (Var y))"
        (alphaEquivalent
            (Forall "x" (Type 1) (Lift (Var "x")))
            (Forall "y" (Type 1) (Lift (Var "y"))))

    -- Forall: free variable not renamed
    assert ref "Forall x (Type 1) (Lift (Var z)) == Forall y (Type 1) (Lift (Var z))  (z free)"
        (alphaEquivalent
            (Forall "x" (Type 1) (Lift (Var "z")))
            (Forall "y" (Type 1) (Lift (Var "z"))))

    -- Doctest from SessionTypes/Kernel.hs line 86: nested Pi in domain
    assert ref "doctest SessionTypes/Kernel.hs:86 - nested Pi in Forall domain"
        (alphaEquivalent
            (Forall "x" (Pi "y" (Type 1) (Var "y")) (Lift (Var "x")))
            (Forall "z" (Pi "p" (Type 1) (Var "p")) (Lift (Var "z"))))

    -- Exists alpha-rename
    assert ref "Exists x (Type 1) (TyVar x) == Exists y (Type 1) (TyVar y)"
        (alphaEquivalent
            (Exists "x" (Type 1) (TyVar "x"))
            (Exists "y" (Type 1) (TyVar "y")))

    -- Forall2 alpha-rename
    assert ref "Forall2 x (TyVar x) == Forall2 y (TyVar y)"
        (alphaEquivalent
            (Forall2 "x" (TyVar "x"))
            (Forall2 "y" (TyVar "y")))

    -- Exists2 alpha-rename
    assert ref "Exists2 x (TyVar x) == Exists2 y (TyVar y)"
        (alphaEquivalent
            (Exists2 "x" (TyVar "x"))
            (Exists2 "y" (TyVar "y")))

    -- TyNu alpha-rename
    assert ref "TyNu x (TyVar x) == TyNu y (TyVar y)"
        (alphaEquivalent
            (TyNu "x" (TyVar "x"))
            (TyNu "y" (TyVar "y")))

    -- TyNu free var preserved
    assert ref "TyNu x (TyVar z) == TyNu y (TyVar z)  (z free)"
        (alphaEquivalent
            (TyNu "x" (TyVar "z"))
            (TyNu "y" (TyVar "z")))

    -- Negative: different free vars in Lift
    assert ref "Lift (Var x) /= Lift (Var y)"
        (not $ alphaEquivalent (Lift (Var "x")) (Lift (Var "y")))

    -- Negative: With is not commutative for equality
    assert ref "With (Lift A) (Lift B) /= With (Lift B) (Lift A)"
        (not $ alphaEquivalent
            (With (Lift (Var "A")) (Lift (Var "B")))
            (With (Lift (Var "B")) (Lift (Var "A"))))

    -- Negative: Unit /= TyVar x
    assert ref "Unit /= TyVar x"
        (not $ alphaEquivalent Unit (TyVar "x"))

    -- Negative: Implication vs Tensor
    assert ref "Implication Unit Unit /= Tensor Unit Unit"
        (not $ alphaEquivalent (Implication Unit Unit) (Tensor Unit Unit))

    -- Negative: Forall with different domain types
    assert ref "Forall x (Type 0) (TyVar x) /= Forall y (Type 1) (TyVar y)"
        (not $ alphaEquivalent
            (Forall "x" (Type 0) (TyVar "x"))
            (Forall "y" (Type 1) (TyVar "y")))

    -- Forall2: free var in body not renamed
    assert ref "Forall2 x (TyVar z) == Forall2 y (TyVar z)"
        (alphaEquivalent
            (Forall2 "x" (TyVar "z"))
            (Forall2 "y" (TyVar "z")))
