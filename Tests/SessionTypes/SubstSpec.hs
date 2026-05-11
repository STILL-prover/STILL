module Tests.SessionTypes.SubstSpec (run) where

import Tests.Harness
import SessionTypes.Kernel
import ECC.Kernel (FunctionalTerm(..))
import Data.IORef

run :: IORef TestState -> IO ()
run ref = group ref "SessionTypes.substVarProp + substVarTerm + substVarType" $ do

    -- ===== substVarProp B x u: replace channel name u with x =====

    assert ref "substVarProp Unit x u = Unit"
        (substVarProp Unit "x" "u" == Unit)

    assert ref "substVarProp (TyVar u) x u = TyVar x"
        (substVarProp (TyVar "u") "x" "u" == TyVar "x")

    assert ref "substVarProp (TyVar z) x u = TyVar z  (z /= u, no-op)"
        (substVarProp (TyVar "z") "x" "u" == TyVar "z")

    assert ref "substVarProp (Tensor (TyVar u) (TyVar u)) x u = Tensor (TyVar x) (TyVar x)"
        (substVarProp (Tensor (TyVar "u") (TyVar "u")) "x" "u"
            == Tensor (TyVar "x") (TyVar "x"))

    assert ref "substVarProp (Implication (TyVar u) (TyVar u)) x u = Implication (TyVar x) (TyVar x)"
        (substVarProp (Implication (TyVar "u") (TyVar "u")) "x" "u"
            == Implication (TyVar "x") (TyVar "x"))

    assert ref "substVarProp (Replication (TyVar u)) x u = Replication (TyVar x)"
        (substVarProp (Replication (TyVar "u")) "x" "u"
            == Replication (TyVar "x"))

    -- Forall binder captures u → body unchanged
    assert ref "substVarProp (Forall u (Var T) (TyVar u)) x u: u captured, body unchanged"
        (substVarProp (Forall "u" (Var "T") (TyVar "u")) "x" "u"
            == Forall "u" (Var "T") (TyVar "u"))

    -- Forall binder does not capture u → body is substituted
    assert ref "substVarProp (Forall v (Var T) (TyVar u)) x u = Forall v T (TyVar x)"
        (substVarProp (Forall "v" (Var "T") (TyVar "u")) "x" "u"
            == Forall "v" (Var "T") (TyVar "x"))

    -- TyNu: binder captures → no substitution in body
    assert ref "substVarProp (TyNu u (TyVar u)) x u: u captured by TyNu"
        (substVarProp (TyNu "u" (TyVar "u")) "x" "u"
            == TyNu "u" (TyVar "u"))

    -- TyNu: binder does not capture
    assert ref "substVarProp (TyNu v (TyVar u)) x u = TyNu v (TyVar x)"
        (substVarProp (TyNu "v" (TyVar "u")) "x" "u"
            == TyNu "v" (TyVar "x"))

    -- Lift: contains a FunctionalTerm with Var u
    assert ref "substVarProp (Lift (Var u)) x u = Lift (Var x)"
        (substVarProp (Lift (Var "u")) "x" "u" == Lift (Var "x"))

    -- ===== substVarTerm B n x: replace functional var x with FunctionalTerm n =====

    assert ref "substVarTerm Unit n x = Unit"
        (substVarTerm Unit (Var "n") "x" == Unit)

    assert ref "substVarTerm (Lift (Var x)) (IntLit 42) x = Lift (IntLit 42)"
        (substVarTerm (Lift (Var "x")) (IntLit 42) "x" == Lift (IntLit 42))

    assert ref "substVarTerm (Lift (Var z)) n x = Lift (Var z)  (z /= x)"
        (substVarTerm (Lift (Var "z")) (IntLit 42) "x" == Lift (Var "z"))

    assert ref "substVarTerm (TyVar y) n x = TyVar y  (TyVars unaffected)"
        (substVarTerm (TyVar "y") (Var "n") "x" == TyVar "y")

    -- When binder y == substituted var x (both "y"):
    -- substVarTerm (Forall y T (Lift y)) n y = Forall y (substFT T n y) (Lift y)
    -- The first branch fires (y == x), so body is unchanged (y is captured).
    assert ref "substVarTerm (Forall y T (Lift y)) n y: y captured by binder, body unchanged"
        (substVarTerm
            (Forall "y" (Var "T") (Lift (Var "y")))
            (Var "z") "y"
            == Forall "y" (Var "T") (Lift (Var "y")))

    -- Capture avoidance: substituting (Var "y") for "x" in Forall "y" T (Lift (Var "x"))
    -- Binder "y" is free in the substituted term (Var "y"), so binder must be renamed.
    assert ref "substVarTerm (Forall y T (Lift x)) (Var y) x: avoids capture (renames binder y)"
        (let result = substVarTerm
                (Forall "y" (Var "T") (Lift (Var "x")))
                (Var "y") "x"
         in case result of
                Forall binder _ _ -> binder /= "y"
                _ -> False)

    -- No capture needed when free vars don't overlap
    assert ref "substVarTerm (Forall y (Var T) (Lift (Var x))) (Var z) x = Forall y T (Lift (Var z))"
        (substVarTerm
            (Forall "y" (Var "T") (Lift (Var "x")))
            (Var "z") "x"
            == Forall "y" (Var "T") (Lift (Var "z")))

    -- ===== substVarType B P x: replace type variable x with Proposition P =====

    assert ref "substVarType Unit P x = Unit"
        (substVarType Unit (Replication Unit) "x" == Unit)

    assert ref "substVarType (TyVar x) P x = P"
        (substVarType (TyVar "x") (Replication Unit) "x" == Replication Unit)

    assert ref "substVarType (TyVar z) P x = TyVar z  (z /= x)"
        (substVarType (TyVar "z") (Replication Unit) "x" == TyVar "z")

    -- Lift is unaffected by session type substitution (Lift contains FunctionalTerms)
    assert ref "substVarType (Lift (Var x)) P x = Lift (Var x)  (Lift is unaffected)"
        (substVarType (Lift (Var "x")) (Replication Unit) "x" == Lift (Var "x"))

    assert ref "substVarType (Tensor (TyVar x) (TyVar y)) P x = Tensor P (TyVar y)"
        (substVarType (Tensor (TyVar "x") (TyVar "y")) Unit "x"
            == Tensor Unit (TyVar "y"))

    -- Forall2 binder captures x → no substitution in body
    assert ref "substVarType (Forall2 x (TyVar x)) P x: x captured, body unchanged"
        (substVarType (Forall2 "x" (TyVar "x")) (Replication Unit) "x"
            == Forall2 "x" (TyVar "x"))

    -- TyNu binder captures x → no substitution
    assert ref "substVarType (TyNu x (TyVar x)) P x: x captured"
        (substVarType (TyNu "x" (TyVar "x")) Unit "x"
            == TyNu "x" (TyVar "x"))

    -- TyNu binder does not capture
    assert ref "substVarType (TyNu z (TyVar x)) P x = TyNu z P"
        (substVarType (TyNu "z" (TyVar "x")) (Replication Unit) "x"
            == TyNu "z" (Replication Unit))
