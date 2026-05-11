module Tests.SessionTypes.TypeCheckSpec (run) where

import Tests.Harness
import SessionTypes.Kernel
import ECC.Kernel (emptyContext, FunctionalTerm(..))
import qualified Data.Set as S
import qualified Data.Map as Map
import Data.IORef

-- Build a minimal sequent with no context, proving goal on channel "c"
emptySeq :: Proposition -> Sequent
emptySeq goal = Sequent
    { tyVarContext      = S.empty
    , fnContext         = emptyContext
    , unrestrictedContext = Map.empty
    , linearContext     = Map.empty
    , recursiveBindings = Map.empty
    , channel           = "c"
    , goalProposition   = goal
    }

-- Build a sequent with one linear assumption
withLinear :: String -> Proposition -> Proposition -> Sequent
withLinear varName varTy goal = (emptySeq goal)
    { linearContext = Map.singleton varName varTy }

run :: IORef TestState -> IO ()
run ref = group ref "SessionTypes.typeCheckProcessUnderSequent" $ do

    -- Halt proves Unit (empty linear context)
    assertRight ref "Halt proves Unit"
        (typeCheckProcessUnderSequent (emptySeq Unit) Halt)

    -- Halt fails on non-Unit goal
    assertLeft ref "Halt does NOT prove Implication Unit Unit"
        (typeCheckProcessUnderSequent (emptySeq (Implication Unit Unit)) Halt)

    assertLeft ref "Halt does NOT prove TyVar x"
        (typeCheckProcessUnderSequent (emptySeq (TyVar "x")) Halt)

    -- Halt fails when linear context has a non-auto-dischargeable assumption.
    -- Unit assumptions are auto-discharged, so use TyVar which cannot be.
    assertLeft ref "Halt fails when linear context has non-dischargeable assumption"
        (typeCheckProcessUnderSequent
            (withLinear "x" (TyVar "A") Unit)
            Halt)

    -- Link x c proves A when linearContext = {x: A} and channel = c
    -- Link "x" "c" : linearContext has x:A, goal is A, channel is c
    assertRight ref "Link x c proves A (identity rule)"
        (typeCheckProcessUnderSequent
            (withLinear "x" (TyVar "A") (TyVar "A"))
            (Link "x" "c"))

    -- Link fails when goal doesn't match context
    assertLeft ref "Link x c fails when goal A /= context type B"
        (typeCheckProcessUnderSequent
            (withLinear "x" (TyVar "A") (TyVar "B"))
            (Link "x" "c"))

    -- Link fails when linear context has extra variables
    assertLeft ref "Link fails when linear context has extra variables"
        (typeCheckProcessUnderSequent
            ((withLinear "x" (TyVar "A") (TyVar "A"))
                { linearContext = Map.fromList [("x", TyVar "A"), ("y", TyVar "B")] })
            (Link "x" "c"))

    -- SendInl on the goal channel proves Plus a b by proving a
    assertRight ref "SendInl c Halt proves Plus Unit Unit"
        (typeCheckProcessUnderSequent
            (emptySeq (Plus Unit Unit))
            (SendInl "c" Halt))

    -- SendInr on the goal channel proves Plus a b by proving b
    assertRight ref "SendInr c Halt proves Plus Unit Unit"
        (typeCheckProcessUnderSequent
            (emptySeq (Plus Unit Unit))
            (SendInr "c" Halt))

    -- SendInl fails when goal is not Plus
    assertLeft ref "SendInl fails when goal is not Plus"
        (typeCheckProcessUnderSequent
            (emptySeq (With Unit Unit))
            (SendInl "c" Halt))

    -- LiftTerm: prove Lift IntTy by sending IntLit 5
    assertRight ref "LiftTerm c (IntLit 5) proves Lift IntTy"
        (typeCheckProcessUnderSequent
            (emptySeq (Lift IntTy))
            (LiftTerm "c" (IntLit 5)))

    -- LiftTerm fails with wrong type
    assertLeft ref "LiftTerm c (IntLit 5) fails for Lift StringTy"
        (typeCheckProcessUnderSequent
            (emptySeq (Lift StringTy))
            (LiftTerm "c" (IntLit 5)))

    -- LiftTerm fails when linear context has a non-auto-dischargeable assumption.
    assertLeft ref "LiftTerm fails with non-dischargeable linear context"
        (typeCheckProcessUnderSequent
            (withLinear "x" (TyVar "A") (Lift IntTy))
            (LiftTerm "c" (IntLit 5)))

    -- ReplicateReceive: !A right rule
    assertRight ref "ReplicateReceive c y Halt proves !Unit"
        (typeCheckProcessUnderSequent
            (emptySeq (Replication Unit))
            (ReplicateReceive "c" "y" Halt))

    -- Case on goal channel: With right rule
    -- "c.case(inl: Halt, inr: Halt)" proves (Unit & Unit)
    assertRight ref "Case c (Halt) (Halt) proves With Unit Unit"
        (typeCheckProcessUnderSequent
            (emptySeq (With Unit Unit))
            (Case "c" Halt Halt))

    -- Case fails when goal is not With
    assertLeft ref "Case c fails when goal is not With"
        (typeCheckProcessUnderSequent
            (emptySeq (Plus Unit Unit))
            (Case "c" Halt Halt))
