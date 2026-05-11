module Tests.SessionTypes.FreeNamesSpec (run) where

import Tests.Harness
import SessionTypes.Kernel
import ECC.Kernel (FunctionalTerm(..))
import qualified Data.Set as S
import Data.IORef

run :: IORef TestState -> IO ()
run ref = group ref "SessionTypes.freePropNames" $ do

    -- Atomic terms
    assertEqual ref "Unit has no free names"
        S.empty (freePropNames Unit)

    assertEqual ref "TyVar x has {x}"
        (S.singleton "x") (freePropNames (TyVar "x"))

    -- Lift: delegates to functionalFreeVariables
    assertEqual ref "Lift (Var x) has {x}"
        (S.singleton "x") (freePropNames (Lift (Var "x")))
    assertEqual ref "Lift (Type 0) has no free names"
        S.empty (freePropNames (Lift (Type 0)))

    -- Implication, Tensor, With, Plus: union
    assertEqual ref "Implication (TyVar x) (TyVar y) has {x,y}"
        (S.fromList ["x", "y"])
        (freePropNames (Implication (TyVar "x") (TyVar "y")))

    assertEqual ref "Tensor (TyVar x) (TyVar y) has {x,y}"
        (S.fromList ["x", "y"])
        (freePropNames (Tensor (TyVar "x") (TyVar "y")))

    assertEqual ref "With (TyVar x) (TyVar y) has {x,y}"
        (S.fromList ["x", "y"])
        (freePropNames (With (TyVar "x") (TyVar "y")))

    assertEqual ref "Plus (TyVar x) (TyVar y) has {x,y}"
        (S.fromList ["x", "y"])
        (freePropNames (Plus (TyVar "x") (TyVar "y")))

    -- Replication
    assertEqual ref "Replication (TyVar x) has {x}"
        (S.singleton "x") (freePropNames (Replication (TyVar "x")))

    -- Forall: binder removes x from body, but domain Var T is still free
    -- freePropNames (Forall x t p) = functionalFreeVariables t ∪ (freePropNames p \ {x})
    assertEqual ref "Forall x (Var T) (TyVar x) has {T} (x bound in body, T free in domain)"
        (S.singleton "T") (freePropNames (Forall "x" (Var "T") (TyVar "x")))

    -- Forall: domain is always free
    assertEqual ref "Forall x (Var T) Unit has {T} (T free in domain)"
        (S.singleton "T") (freePropNames (Forall "x" (Var "T") Unit))

    -- Forall: domain and body free names union
    assertEqual ref "Forall x (Var T) (TyVar y) has {T,y}"
        (S.fromList ["T", "y"])
        (freePropNames (Forall "x" (Var "T") (TyVar "y")))

    -- Forall with no domain var: domain is Type 0 (no free vars)
    assertEqual ref "Forall x (Type 0) (TyVar x) has no free names (x bound, domain closed)"
        S.empty (freePropNames (Forall "x" (Type 0) (TyVar "x")))

    -- Exists: same rules as Forall
    assertEqual ref "Exists x (Var T) (TyVar x) has {T} (x bound in body, T free in domain)"
        (S.singleton "T") (freePropNames (Exists "x" (Var "T") (TyVar "x")))

    -- Forall2: binder removes x from body
    assertEqual ref "Forall2 x (TyVar x) has no free names"
        S.empty (freePropNames (Forall2 "x" (TyVar "x")))
    assertEqual ref "Forall2 x (TyVar y) has {y}"
        (S.singleton "y") (freePropNames (Forall2 "x" (TyVar "y")))

    -- Exists2: same
    assertEqual ref "Exists2 x (TyVar x) has no free names"
        S.empty (freePropNames (Exists2 "x" (TyVar "x")))

    -- TyNu: binder removes from body
    assertEqual ref "TyNu x (TyVar x) has no free names (x bound)"
        S.empty (freePropNames (TyNu "x" (TyVar "x")))
    assertEqual ref "TyNu x (TyVar y) has {y} (y free)"
        (S.singleton "y") (freePropNames (TyNu "x" (TyVar "y")))

    -- Nested: free names across structure
    assertEqual ref "Tensor (TyNu x (TyVar x)) (TyVar z) has {z}"
        (S.singleton "z")
        (freePropNames (Tensor (TyNu "x" (TyVar "x")) (TyVar "z")))
