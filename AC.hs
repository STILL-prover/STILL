module AC where

import LinearLogic
import FunctionalSystem as FS
import qualified FunctionalTactics as FT
import Control.Monad.Identity (Identity(Identity))
import Tactics
import Data.Map
import qualified Data.Set as S


axiomOfChoiceTypes :: Proposition -> Proposition
axiomOfChoiceTypes = Forall "A" (FS.Type 1) . Forall "B" (FS.Type 1)

gTy = FS.Pi "x" (FS.Var "A") (FS.Sigma "y" (FS.Var "B") (FS.App (FS.App (FS.Var "P") (FS.Var "x")) (FS.Var "y")))

axiomOfChoice :: Proposition
axiomOfChoice = axiomOfChoiceTypes (Forall "P" (FS.Pi "_1" (FS.Var "A") (FS.Pi "_2" (FS.Var "B") (FS.Type 1)))
    (Implication (Lift gTy)
        (Exists "f" (FS.implication "_4" (FS.Var "A") (FS.Var "B"))
            (Forall "x" (FS.Var "A") (Lift (FS.App (FS.App (FS.Var "P") (FS.Var "x")) (FS.App (FS.Var "f") (FS.Var "x"))))))))

axiomOfChoiceFunctional :: FS.FunctionalTerm -> FS.FunctionalTerm -> Proposition
axiomOfChoiceFunctional aTy bTy = Lift
    (FS.Pi "A" aTy
        (FS.Pi "B" bTy
            (FS.Pi "P" (FS.Pi "x" (FS.Var "A") (FS.Pi "y" (FS.Var "B") (FS.Type 1)))
                (FS.implication "_3" (FS.Pi "x" (FS.Var "A") (FS.Sigma "y" (FS.Var "B") (FS.App (FS.App (FS.Var "P") (FS.Var "x")) (FS.Var "y"))))
                    (FS.Sigma "f" (FS.implication "_4" (FS.Var "A") (FS.Var "B"))
                        (FS.Pi "x" (FS.Var "A")
                            (FS.App (FS.App (FS.Var "P") (FS.Var "x")) (FS.App (FS.Var "f") (FS.Var "x")))))))))

axiomOfChoiceTermProp :: FS.FunctionalTerm -> FS.FunctionalTerm -> FS.FunctionalTerm
axiomOfChoiceTermProp aTy bTy = FS.Pi "A" aTy
        (FS.Pi "B" bTy
            (FS.Pi "P" (FS.Pi "x" (FS.Var "A") (FS.Pi "y" (FS.Var "B") (FS.Type 1)))
                (FS.implication "_3" (FS.Pi "x" (FS.Var "A") (FS.Sigma "y" (FS.Var "B") (FS.App (FS.App (FS.Var "P") (FS.Var "x")) (FS.Var "y"))))
                    (FS.Sigma "f" (FS.implication "_4" (FS.Var "A") (FS.Var "B"))
                        (FS.Pi "x" (FS.Var "A")
                            (FS.App (FS.App (FS.Var "P") (FS.Var "x")) (FS.App (FS.Var "f") (FS.Var "x"))))))))

axiomOfChoiceProof = let
    t = _Theorem (_Init "AC") "axiomOfChoice" AC.axiomOfChoice
    s1 = _Apply t (_Repeat (_ForallR `_Alt` _ImpliesR `_Alt` _FTermL "a"))
    s2 = _Apply s1 _ExistsR
    f = Lambda "__4" (Var "A") (Proj1 (App (Var "a") (Var "__4")))
    s3 = _FApply s2 (FT._FExact f)
    s4 = _Apply s3 _ForallR
    s5 = _Apply s4 _FTermR
    s6 = _FApply s5 (FT._FSimp 2)
    s7 = _FApply s6 (FT._FExact (Proj2 (App (Var "a") (Var "x"))))
    in _Done s7

axiomOfChoiceInOnlyFunctionalSystem = let
    t = _Theorem (_Init "ACF") "axiomOfChoiceInOnlyFunctionalSystem" $ AC.axiomOfChoiceFunctional (Type 1) (Type 1)
    s1 = _Apply t _FTermR
    s2 = _FApply s1 (FT._FRepeat FT._FLambda)
    f = Lambda "__4" (Var "A") (Proj1 (App (Var "__3") (Var "__4")))
    f2 = Lambda "x" (Var "A") (Proj2 (App (Var "__3") (Var "x")))
    s3 = _FApply s2 (FT._FPair (Just f) (Just f2) 1)
    s4 = _FApply s3 FT._FExactKnown
    s5 = _FApply s4 FT._FExactKnown
    s6 = _FApply s5 FT._FExactKnown
    --s3 = _FApply s2 (FT._FExact (Pair f f2 "f" (Lambda "__4" (Var "A") (Var "B")) (Pi "x" (Var "A") (App (App (Var "P") (Var "x")) (App (Var "f") (Var "x"))))))
    in _Done s6

axiomOfChoiceTermProof :: Bool
axiomOfChoiceTermProof = let
    t = Right $ FT._FTheorem Data.Map.empty (AC.axiomOfChoiceTermProp (Type 1) (Type 1)) S.empty :: Either String (FT.ProofState Identity)
    s2 = FT._FApply t (FT._FRepeat FT._FLambda)
    f = Lambda "__4" (Var "A") (Proj1 (App (Var "__3") (Var "__4")))
    f2 = Lambda "x" (Var "A") (Proj2 (App (Var "__3") (Var "x")))
    s3 = FT._FApply s2 (FT._FPair (Just f) (Just f2) 1)
    s4 = FT._FApply s3 FT._FExactKnown
    s5 = FT._FApply s4 FT._FExactKnown
    s6 = FT._FApply s5 FT._FExactKnown
    --s3 = _FApply s2 (FT._FExact (Pair f f2 "f" (Lambda "__4" (Var "A") (Var "B")) (Pi "x" (Var "A") (App (App (Var "P") (Var "x")) (App (Var "f") (Var "x"))))))
    in (case s6 of Right s -> FT._FDone s; Left s -> False)
