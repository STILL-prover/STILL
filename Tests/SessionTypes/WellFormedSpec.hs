module Tests.SessionTypes.WellFormedSpec (run) where

import Tests.Harness
import SessionTypes.Kernel
import ECC.Kernel (FunctionalTerm(..))
import qualified Data.Set as S
import Data.IORef

wf :: Proposition -> Either String ()
wf = wellFormedType S.empty

wfCtx :: [String] -> Proposition -> Either String ()
wfCtx xs = wellFormedType (S.fromList xs)

run :: IORef TestState -> IO ()
run ref = group ref "SessionTypes.wellFormedType" $ do

    -- ===== Simple well-formed propositions =====

    assertRight ref "Unit is well-formed"
        (wf Unit)

    assertRight ref "Lift (Var x) is well-formed"
        (wf (Lift (Var "x")))

    assertRight ref "Replication Unit is well-formed"
        (wf (Replication Unit))

    assertRight ref "Tensor Unit Unit is well-formed"
        (wf (Tensor Unit Unit))

    assertRight ref "With Unit Unit is well-formed"
        (wf (With Unit Unit))

    assertRight ref "Plus Unit Unit is well-formed"
        (wf (Plus Unit Unit))

    assertRight ref "Implication Unit Unit is well-formed"
        (wf (Implication Unit Unit))

    -- ===== TyVar scope =====

    assertLeft ref "TyVar X not in empty context fails"
        (wf (TyVar "X"))

    assertRight ref "TyVar X in context passes"
        (wfCtx ["X"] (TyVar "X"))

    assertLeft ref "TyVar X not in context {Y} fails"
        (wfCtx ["Y"] (TyVar "X"))

    assertRight ref "Forall2 X binds X for its body"
        (wf (Forall2 "X" (TyVar "X")))

    assertLeft ref "Forall2 X body may not reference Y (unbound)"
        (wf (Forall2 "X" (TyVar "Y")))

    assertRight ref "Exists2 X binds X for its body"
        (wf (Exists2 "X" (TyVar "X")))

    -- ===== TyNu structural: must mention bound variable =====

    assertLeft ref "nu X. 1 does not mention X -- rejected"
        (wf (TyNu "X" Unit))

    assertLeft ref "nu X. !1 does not mention X -- rejected"
        (wf (TyNu "X" (Replication Unit)))

    assertLeft ref "nu X. Y -o Y does not mention X -- rejected"
        (wfCtx ["Y"] (TyNu "X" (Implication (TyVar "Y") (TyVar "Y"))))

    -- ===== TyNu structural: body must not be just TyVar x =====

    assertLeft ref "nu X. X is not a productive coinductive type"
        (wf (TyNu "X" (TyVar "X")))

    -- ===== TyNu valid productive recursive types =====

    assertRight ref "nu X. 1 -o X is valid (X in output position)"
        (wf (TyNu "X" (Implication Unit (TyVar "X"))))

    assertRight ref "nu X. X * 1 is valid"
        (wf (TyNu "X" (Tensor (TyVar "X") Unit)))

    assertRight ref "nu X. 1 & X is valid"
        (wf (TyNu "X" (With Unit (TyVar "X"))))

    assertRight ref "nu X. X + 1 is valid"
        (wf (TyNu "X" (Plus (TyVar "X") Unit)))

    assertRight ref "nu X. !X is valid"
        (wf (TyNu "X" (Replication (TyVar "X"))))

    assertRight ref "nu X. X -o 1 is valid (X on left of implication)"
        (wf (TyNu "X" (Implication (TyVar "X") Unit)))

    -- ===== TyNu: bound variable is in scope for the body =====

    assertRight ref "nu X. forall2 Y. X -o Y: X and Y both in scope"
        (wf (TyNu "X" (Forall2 "Y" (Implication (TyVar "X") (TyVar "Y")))))

    -- ===== TyNu: nested nu scoping =====

    -- nu X. nu Y. X  : inner nu Y does not mention Y -- rejected
    assertLeft ref "nu X. nu Y. X  -- inner nu Y does not mention Y"
        (wf (TyNu "X" (TyNu "Y" (TyVar "X"))))

    -- nu X. nu Y. Y  : inner nu Y mentions Y; outer nu X mentions X (X appears in nu Y. Y)
    -- But does X appear in (nu Y. Y)? freePropNames (nu Y. Y) = {} (Y bound). So X NOT in freePropNames.
    assertLeft ref "nu X. nu Y. Y  -- outer nu X does not mention X"
        (wf (TyNu "X" (TyNu "Y" (TyVar "Y"))))

    assertLeft ref "nu X. nu X. (1 -o X)  -- outer nu X shadowed"
        (wf (TyNu "X" (TyNu "X" (Implication Unit (TyVar "X")))))

    -- nu X. nu Y. X * Y : inner nu Y mentions Y; outer nu X: freePropNames(nu Y. X*Y) = {X}
    assertRight ref "nu X. nu Y. X * Y  -- both nus mention their variables"
        (wf (TyNu "X" (TyNu "Y" (Tensor (TyVar "X") (TyVar "Y")))))

    -- ===== TyNu: strict positivity still enforced =====

    -- nu X. (X -o 1) -o 1  : X appears contravariantly (in left of left-of-implication)
    -- isStrictlyPositive "X" ((X -o 1) -o 1)
    --   go X ((X-o1) -o 1) = checkCons X (X-o1) && go X 1
    --   checkCons X (Implication (TyVar X) 1) = checkLeft X (TyVar X) && checkCons X 1
    --   checkLeft X (TyVar X) = False => strict positivity FAILS
    assertLeft ref "nu X. (X -o 1) -o 1  -- X in contravariant position"
        (wf (TyNu "X" (Implication (Implication (TyVar "X") Unit) Unit)))
