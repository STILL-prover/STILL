module SessionTypes.Kernel where

import Data.Map
import qualified Data.Set as S
import qualified Control.Monad.State.Lazy as ST
import qualified Data.List as L
import Control.Monad (when, unless)
import Text.Read (readMaybe)
import Data.Maybe (isJust, fromMaybe)
import ECC.Kernel
    ( abstTermFunctional,
      extractProofFromTermUnderCtx,
      ftToS,
      functionalFreeVariables,
      functionalNames,
      functionalRename,
      functionalSubst,
      getFunctionalContextNames,
      getFunctionalProofNames,
      substVarFunctional,
      verifyFunctionalProofM,
      FunctionalContext,
      FunctionalProof,
      FunctionalSequent(goalTerm, goalType, functionalContext),
      FunctionalTerm(..),
      foldFunctionalProof,
      getFunctionalContextFreeNames,
      ctxToList, renameVarInFnCtx, ctxLookup, ctxMember, ctxKeys, ctxEitherLookup, ctxDelete, safeInsert )
import qualified ECC.Kernel as ECC (renameVarInProof, alphaEquivalentWithRenamings)
import Utils.Misc
import qualified Debug.Trace as DBG

data Proposition = Unit
    | Lift FunctionalTerm
    | Implication Proposition Proposition
    | Tensor Proposition Proposition
    | Replication Proposition
    | With Proposition Proposition
    | Plus Proposition Proposition
    | Forall String FunctionalTerm Proposition
    | Exists String FunctionalTerm Proposition
    | Forall2 String Proposition
    | Exists2 String Proposition
    | TyNu String Proposition
    | TyVar String
    deriving (Show, Read)

{-|
Check for alpha equivalence of two propositions under some free variable
renamings that have already been determined.
-}
alphaEquivalentWithRenamings :: [(String, String)] -> Proposition -> Proposition -> Bool
alphaEquivalentWithRenamings ren p1 p2 = go ren (p1, p2)
    where
        go :: [(String, String)] -> (Proposition, Proposition) -> Bool
        go ren (Unit, Unit) = True
        go ren (Lift t1, Lift t2) = ECC.alphaEquivalentWithRenamings ren t1 t2
        go ren (Implication a1 b1, Implication a2 b2) = go ren (a1, a2) && go ren (b1, b2)
        go ren (Tensor a1 b1, Tensor a2 b2) = go ren (a1, a2) && go ren (b1, b2)
        go ren (Replication a1, Replication a2) = go ren (a1, a2)
        go ren (With a1 b1, With a2 b2) = go ren (a1, a2) && go ren (b1, b2)
        go ren (Plus a1 b1, Plus a2 b2) = go ren (a1, a2) && go ren (b1, b2)
        go ren (Forall x1 t1 a1, Forall x2 t2 a2) = ECC.alphaEquivalentWithRenamings ren t1 t2 && go ((x1, x2):ren) (a1, a2)
        go ren (Exists x1 t1 a1, Exists x2 t2 a2) = ECC.alphaEquivalentWithRenamings ren t1 t2 && go ((x1, x2):ren) (a1, a2)
        go ren (Forall2 x1 a1, Forall2 x2 a2) = go ((x1, x2):ren) (a1, a2)
        go ren (Exists2 x1 a1, Exists2 x2 a2) = go ((x1, x2):ren) (a1, a2)
        go ren (TyNu x1 a1, TyNu x2 a2) = go ((x1, x2):ren) (a1, a2)
        go ren (TyVar x1, TyVar x2) = eqName ren x1 x2
        go ren _ = False

        eqName :: [(String, String)] -> String -> String -> Bool
        eqName [] x1 x2                                         = x1 == x2
        eqName ((r1,r2):rest) x1 x2  | r1 == x1 && r2 == x2     = True
        eqName ((r1, r2):rest) x1 x2 | r1 == x1 || r2 == x2     = False
        eqName ((r1, r2):rest) x1 x2 | r1 /= x1 && r2 /= x2     = eqName rest x1 x2

{-|
Check for alpha equivalence of two propositions.

>>> alphaEquivalent (Forall "x" (Type 1) (Lift (Var "x"))) (Forall "y" (Type 1) (Lift (Var "y")))
True

>>> alphaEquivalent (Forall "x" (Type 1) (Lift (Var "z"))) (Forall "y" (Type 1) (Lift (Var "z")))
True

>>> alphaEquivalent (Forall "x" (Pi "y" (Type 1) (Var "y")) (Lift (Var "x"))) (Forall "z" (Pi "p" (Type 1) (Var "p")) (Lift (Var "z")))
True
-}
alphaEquivalent :: Proposition -> Proposition -> Bool
alphaEquivalent = alphaEquivalentWithRenamings []

instance Eq Proposition where
    (==) :: Proposition -> Proposition -> Bool
    (==) = alphaEquivalent

propToS :: Proposition -> String
propToS = go 0
  where
    -- Precedence levels (bigger = tighter):
    -- 0: top level
    -- 1: implication
    -- 2: additive (&, ⊕)
    -- 3: multiplicative (⊗)
    -- 4: atomic / prefix
        go :: Int -> Proposition -> String
        go _ Unit = "1"
        go _ (Lift t) = "$" ++ ftToS t
        go p (Replication a) =
            parensIf (p > 4) $ "!" ++ go 4 a
        go p (Tensor a b) =
            infixOp p 3 " ⊗ " a b
        go p (With a b) =
            infixOp p 2 " & " a b
        go p (Plus a b) =
            infixOp p 2 " ⊕ " a b
        go p (Implication a b) =
            infixOp p 1 " ⊸ " a b
        go p (Forall x ty a) =
            parensIf (p > 1) $ "∀" ++ x ++ " : " ++ ftToS ty ++ ". " ++ go 0 a
        go p (Exists x ty a) =
            parensIf (p > 1) $ "∃" ++ x ++ " : " ++ ftToS ty ++ ". " ++ go 0 a
        go p (Forall2 x a) =
            parensIf (p > 1) $ "∀" ++ x ++ ". " ++ go 0 a
        go p (Exists2 x a) =
            parensIf (p > 1) $ "∃" ++ x ++ ". " ++ go 0 a
        go p1 (TyNu x p) = parensIf (p1 > 1) $ "ν" ++ x ++ ". " ++ go 0 p
        go _ (TyVar x) = x
        infixOp :: Int -> Int -> String -> Proposition -> Proposition -> String
        infixOp ctxPrec myPrec op a b =
            parensIf (ctxPrec > myPrec) $
            go (myPrec + 1) a ++ op ++ go myPrec b
        parensIf :: Bool -> String -> String
        parensIf False s = s
        parensIf True s = "(" ++ s ++ ")"

{-| Get all names occuring in a proposition.

>>> propNames (With (Lift (Var "A")) (Forall "x" (Var "B") Unit))
fromList ["A","B","x"]
-}
propNames :: Proposition -> S.Set String
propNames Unit = S.empty
propNames (Lift t) = functionalNames t
propNames (Implication p1 p2) = propNames p1 `S.union` propNames p2
propNames (Tensor p1 p2) = propNames p1 `S.union` propNames p2
propNames (Replication p) = propNames p
propNames (With p1 p2) = propNames p1 `S.union` propNames p2
propNames (Plus p1 p2) = propNames p1 `S.union` propNames p2
propNames (Forall x t p) = S.insert x $ functionalNames t `S.union` propNames p
propNames (Exists x t p) = S.insert x $ functionalNames t `S.union` propNames p
propNames (Forall2 x p) = S.insert x $ propNames p
propNames (Exists2 x p) = S.insert x $ propNames p
propNames (TyNu x p) = S.insert x $ propNames p
propNames (TyVar x) = S.singleton x

{-| Returns the set of free variables in the proposition. -}
freePropNames :: Proposition -> S.Set String
freePropNames Unit = S.empty
freePropNames (Lift t) = functionalFreeVariables t
freePropNames (Implication p1 p2) = freePropNames p1 `S.union` freePropNames p2
freePropNames (Tensor p1 p2) = freePropNames p1 `S.union` freePropNames p2
freePropNames (Replication p) = freePropNames p
freePropNames (With p1 p2) = freePropNames p1 `S.union` freePropNames p2
freePropNames (Plus p1 p2) = freePropNames p1 `S.union` freePropNames p2
freePropNames (Forall x t p) = functionalFreeVariables t `S.union` S.delete x (freePropNames p)
freePropNames (Exists x t p) = functionalFreeVariables t `S.union` S.delete x (freePropNames p)
freePropNames (Forall2 x p) = S.delete x (freePropNames p)
freePropNames (Exists2 x p) = S.delete x (freePropNames p)
freePropNames (TyNu x p) = S.delete x $ freePropNames p
freePropNames (TyVar x) = S.singleton x

{-| Rename a var name in a process. P{x/u}. Replace the name u with x in P. Does not avoid capturing. -}
renameVarProp :: Proposition -> String -> String -> Proposition
renameVarProp Unit x u = Unit
renameVarProp (Lift t) x u = Lift (functionalRename t x u)
renameVarProp (Implication p1 p2) x u = Implication (renameVarProp p1 x u) (renameVarProp p2 x u)
renameVarProp (Tensor p1 p2) x u = Tensor (renameVarProp p1 x u) (renameVarProp p2 x u)
renameVarProp (Replication p) x u = Replication (renameVarProp p x u)
renameVarProp (With p1 p2) x u = With (renameVarProp p1 x u) (renameVarProp p2 x u)
renameVarProp (Plus p1 p2) x u = Plus (renameVarProp p1 x u) (renameVarProp p2 x u)
renameVarProp (Forall y p1 p2) x u = Forall (if y == u then x else y) (functionalRename p1 x u) (renameVarProp p2 x u)
renameVarProp (Exists y p1 p2) x u = Exists (if y == u then x else y) (functionalRename p1 x u) (renameVarProp p2 x u)
renameVarProp (Forall2 y p2) x u = Forall2 (if y == u then x else y) (renameVarProp p2 x u)
renameVarProp (Exists2 y p2) x u = Exists2 (if y == u then x else y) (renameVarProp p2 x u)
renameVarProp (TyNu y p) x u = TyNu (if y == u then x else y) (renameVarProp p x u)
renameVarProp (TyVar y) x u = TyVar $ if y == u then x else y

alphaConvertProp :: Proposition -> S.Set String -> Proposition
alphaConvertProp (Forall y p1 p2) names =
    let
        z = getFreshName names
    in
        Forall z (functionalRename p1 z y) (renameVarProp p2 z y)
alphaConvertProp (Exists y p1 p2) names =
    let
        z = getFreshName names
    in
        Exists z (functionalRename p1 z y) (renameVarProp p2 z y)
alphaConvertProp (Forall2 y p2) names =
    let
        z = getFreshName names
    in
        Forall2 z (renameVarProp p2 z y)
alphaConvertProp (Exists2 y p2) names =
    let
        z = getFreshName names
    in
        Exists2 z (renameVarProp p2 z y)
alphaConvertProp (TyNu y p) names =
    let
        z = getFreshName names
    in
        TyNu z (renameVarProp p z y)

{-| substVarProp B n x = B{n/x} replace x with n in b -}
substVarProp :: Proposition -> String -> String -> Proposition
substVarProp Unit x u = Unit
substVarProp (Lift t) x u = Lift (functionalSubst t (Var x) u)
substVarProp (Implication p1 p2) x u = Implication (substVarProp p1 x u) (substVarProp p2 x u)
substVarProp (Tensor p1 p2) x u = Tensor (substVarProp p1 x u) (substVarProp p2 x u)
substVarProp (Replication p) x u = Replication (substVarProp p x u)
substVarProp (With p1 p2) x u = With (substVarProp p1 x u) (substVarProp p2 x u)
substVarProp (Plus p1 p2) x u = Plus (substVarProp p1 x u) (substVarProp p2 x u)
substVarProp (Forall y p1 p2) x u = if y == u then Forall y (functionalSubst p1 (Var x) u) p2 -- u is captured and no longer replaced
    else if x == y then substVarProp (alphaConvertProp (Forall y p1 p2) (S.fromList [x, y] `S.union` functionalNames p1 `S.union` propNames p2)) x u -- new x would get captured
    else Forall y (functionalSubst p1 (Var x) u) (substVarProp p2 x u)
substVarProp (Exists y p1 p2) x u = if y == u then Exists y (functionalSubst p1 (Var x) u) p2 -- u is captured and no longer replaced
    else if x == y then substVarProp (alphaConvertProp (Exists y p1 p2) (S.fromList [x, y] `S.union` functionalNames p1 `S.union` propNames p2)) x u -- new x would get captured
    else Exists y (functionalSubst p1 (Var x) u) (substVarProp p2 x u)
substVarProp (Forall2 y p2) x u = if y == u then Forall2 y p2 -- u is captured and no longer replaced
    else if x == y then substVarProp (alphaConvertProp (Forall2 y p2) (S.fromList [x, y] `S.union` propNames p2)) x u -- new x would get captured
    else Forall2 y (substVarProp p2 x u)
substVarProp (Exists2 y p2) x u = if y == u then Exists2 y p2 -- u is captured and no longer replaced
    else if x == y then substVarProp (alphaConvertProp (Exists2 y p2) (S.fromList [x, y] `S.union` propNames p2)) x u -- new x would get captured
    else Exists2 y (substVarProp p2 x u)
substVarProp (TyNu y p) x u = if y == u then TyNu y p -- u is captured and no longer replaced
    else if x == y then substVarProp (alphaConvertProp (TyNu y p) (S.fromList [x, y] `S.union` propNames p)) x u -- new x would get captured
    else TyNu y (substVarProp p x u)
substVarProp (TyVar y) x u = TyVar $ if y == u then x else y

{-| substVarProp B n x = B{N/x} replace x with functional term n in b -}
substVarTerm :: Proposition -> FunctionalTerm -> String -> Proposition
substVarTerm Unit n x = Unit
substVarTerm (Lift t) n x = Lift (functionalSubst t n x)
substVarTerm (Forall y p1 p2) n x = if y == x then Forall y (functionalSubst p1 n x) p2 -- u is captured and no longer replaced
    else if (y `S.member` functionalFreeVariables n) then substVarTerm (alphaConvertProp (Forall y p1 p2) (S.fromList [x, y] `S.union` functionalNames p1 `S.union` propNames p2)) n x -- new x would get captured
    else Forall y (functionalSubst p1 n x) (substVarTerm p2 n x)
substVarTerm (Exists y p1 p2) n x = if y == x then Exists y (functionalSubst p1 n x) p2 -- u is captured and no longer replaced
    else if (y `S.member` functionalFreeVariables n) then substVarTerm (alphaConvertProp (Exists y p1 p2) (S.fromList [x, y] `S.union` functionalNames p1 `S.union` propNames p2)) n x -- new x would get captured
    else Exists y (functionalSubst p1 n x) (substVarTerm p2 n x)
substVarTerm (Forall2 y p2) n x = if y == x then Forall2 y p2 -- u is captured and no longer replaced
    else if (y `S.member` functionalFreeVariables n) then substVarTerm (alphaConvertProp (Forall2 y p2) (S.fromList [x, y] `S.union` propNames p2)) n x -- new x would get captured
    else Forall2 y (substVarTerm p2 n x)
substVarTerm (Exists2 y p2) n x = if y == x then Exists2 y p2 -- u is captured and no longer replaced
    else if (y `S.member` functionalFreeVariables n) then substVarTerm (alphaConvertProp (Exists2 y p2) (S.fromList [x, y] `S.union` propNames p2)) n x -- new x would get captured
    else Exists2 y (substVarTerm p2 n x)
substVarTerm (Implication p1 p2) n x = Implication (substVarTerm p1 n x) (substVarTerm p2 n x)
substVarTerm (Tensor p1 p2) n x = Tensor (substVarTerm p1 n x) (substVarTerm p2 n x)
substVarTerm (Replication p) n x = Replication (substVarTerm p n x)
substVarTerm (With p1 p2) n x = With (substVarTerm p1 n x) (substVarTerm p2 n x)
substVarTerm (Plus p1 p2) n x = Plus (substVarTerm p1 n x) (substVarTerm p2 n x)
substVarTerm (TyNu y p) n x = if y == x then TyNu y p -- x is captured and no longer replaced
    else if (y `S.member` functionalFreeVariables n) then substVarTerm (alphaConvertProp (TyNu y p) (S.fromList [x, y] `S.union` propNames p)) n x -- new x would get captured
    else TyNu y (substVarTerm p n x)
substVarTerm (TyVar y) n x = TyVar y

{-| substVarProp B n x = B{N/x} replace x with session type n in b -}
substVarType :: Proposition -> Proposition -> String -> Proposition
substVarType Unit n x = Unit
substVarType (Lift t) n x = Lift t
substVarType (Forall y p1 p2) n x = if y == x then Forall y p1 p2 -- u is captured and no longer replaced
    else if (y `S.member` freePropNames n) then substVarType (alphaConvertProp (Forall y p1 p2) (S.fromList [x, y] `S.union` functionalNames p1 `S.union` propNames p2)) n x -- new x would get captured
    else Forall y p1 (substVarType p2 n x)
substVarType (Exists y p1 p2) n x = if y == x then Exists y p1 p2 -- u is captured and no longer replaced
    else if (y `S.member` freePropNames n) then substVarType (alphaConvertProp (Exists y p1 p2) (S.fromList [x, y] `S.union` functionalNames p1 `S.union` propNames p2)) n x -- new x would get captured
    else Exists y p1 (substVarType p2 n x)
substVarType (Forall2 y p2) n x = if y == x then Forall2 y p2 -- u is captured and no longer replaced
    else if (y `S.member` freePropNames n) then substVarType (alphaConvertProp (Forall2 y p2) (S.fromList [x, y] `S.union` propNames p2)) n x -- new x would get captured
    else Forall2 y (substVarType p2 n x)
substVarType (Exists2 y p2) n x = if y == x then Exists2 y p2 -- u is captured and no longer replaced
    else if (y `S.member` freePropNames n) then substVarType (alphaConvertProp (Exists2 y p2) (S.fromList [x, y] `S.union` propNames p2)) n x -- new x would get captured
    else Exists2 y (substVarType p2 n x)
substVarType (Implication p1 p2) n x = Implication (substVarType p1 n x) (substVarType p2 n x)
substVarType (Tensor p1 p2) n x = Tensor (substVarType p1 n x) (substVarType p2 n x)
substVarType (Replication p) n x = Replication (substVarType p n x)
substVarType (With p1 p2) n x = With (substVarType p1 n x) (substVarType p2 n x)
substVarType (Plus p1 p2) n x = Plus (substVarType p1 n x) (substVarType p2 n x)
substVarType (TyNu y p) n x = if y == x then TyNu y p -- x is captured and no longer replaced
    else if (y `S.member` freePropNames n) then substVarType (alphaConvertProp (TyNu y p) (S.fromList [x, y] `S.union` propNames p)) n x -- new x would get captured
    else TyNu y (substVarType p n x)
substVarType (TyVar y) n x = if y == x then n else TyVar y

data Process = Halt
    | ParallelComposition Process Process
    | Nu String Proposition Process
    | Send String String Process
    | SendTerm String FunctionalTerm Process
    | SendType String Proposition Process
    | Receive String String Process -- Need to a separate receive type?
    | ReplicateReceive String String Process
    | SendInl String Process
    | SendInr String Process
    | Case String Process Process
    | Link String String
    | LiftTerm String FunctionalTerm
    | Corec String [String] Process [String]
    | Call String [String]
    | HoleTerm
    deriving (Eq, Show, Read)

pToS :: Process -> String
pToS = go 0
  where
    precPar = 0
    precNu = 1
    precPrefix = 2
    parens :: Bool -> String -> String
    parens True s = "(" ++ s ++ ")"
    parens False s = s
    joinArgs :: [String] -> String
    joinArgs = L.intercalate ", "

    go :: Int -> Process -> String
    go _ Halt = "0"
    go d (ParallelComposition p q) =
        parens (d > precPar) $ go precPar p ++ " | " ++ go precPar q
    go d (Nu x _ p) =
        parens (d > precNu) $ "(ν " ++ x ++ ") " ++ go precNu p
    go d (Send ch v p) =
        parens (d > precPrefix) $ ch ++ "[" ++ v ++ "]." ++ go precPrefix p
    go d (SendTerm ch term p) =
        parens (d > precPrefix) $ ch ++ "[" ++ ftToS term ++ "]." ++ go precPrefix p
    go d (SendType ch ty p) =
        parens (d > precPrefix) $ ch ++ "[" ++ propToS ty ++ "]." ++ go precPrefix p
    go d (Receive ch x p) =
        parens (d > precPrefix) $ ch ++ "(" ++ x ++ ")." ++ go precPrefix p
    go d (ReplicateReceive ch x p) =
        parens (d > precPrefix) $ "!" ++ ch ++ "(" ++ x ++ ")." ++ go precPrefix p
    go d (SendInl ch p) =
        parens (d > precPrefix) $ ch ++ ".inl;" ++ go precPrefix p
    go d (SendInr ch p) =
        parens (d > precPrefix) $ ch ++ ".inr;" ++ go precPrefix p
    -- Case arguments usually reset precedence because they are enclosed in syntax
    go d (Case ch p q) =
        parens (d > precPrefix) $ ch ++ ".case(inl: " ++ go 0 p ++ ", inr: " ++ go 0 q ++ " )"
    go _ (Link x y) =
        "[" ++ x ++ " <-> " ++ y ++ "]"
    go _ (LiftTerm ch term) =
        "[ " ++ ch ++ " <- " ++ ftToS term ++ " ]"
    go d (Corec x ys p zs) =
        parens (d > precPrefix) $
        "(corec " ++ x ++ "(" ++ joinArgs ys ++ ")." ++ go precPrefix p ++ ") " ++
        "(" ++ joinArgs zs ++ ")"
    go _ (Call x zs) =
        x ++ "(" ++ joinArgs zs ++ ")"
    go _ HoleTerm = "_"

processNames :: Process -> S.Set String
processNames Halt = S.empty
processNames (Nu y prop p) = S.singleton y `S.union` processNames p `S.union` propNames prop
processNames (Send x y p) = S.fromList [x, y] `S.union` processNames p
processNames (SendTerm x t p) = S.singleton x `S.union` functionalNames t `S.union` processNames p
processNames (SendType x t p) = S.singleton x `S.union` propNames t `S.union` processNames p
processNames (Receive x y p) = S.fromList [x, y] `S.union` processNames p
processNames (ReplicateReceive x y p) = S.fromList [x, y] `S.union` processNames p
processNames (SendInl x p) = S.singleton x `S.union` processNames p
processNames (SendInr x p) = S.singleton x `S.union` processNames p
processNames (Case x p1 p2) = S.singleton x `S.union` processNames p1 `S.union` processNames p2
processNames (Link x y) = S.fromList [x, y]
processNames (LiftTerm x t) = S.singleton x `S.union` functionalNames t
processNames (ParallelComposition p1 p2) = processNames p1 `S.union` processNames p2
processNames (Corec x ys p zs) = S.insert x $ S.fromList ys `S.union` processNames p `S.union` S.fromList zs
processNames (Call x zs) = S.insert x . S.fromList $ zs
processNames HoleTerm = S.empty

processFreeNames :: Process -> S.Set String
processFreeNames Halt = S.empty
processFreeNames (Nu y prop p) = S.delete y $ processFreeNames p `S.union` freePropNames prop
processFreeNames (Send x y p) = S.fromList [x, y] `S.union` processFreeNames p
processFreeNames (SendTerm x t p) = S.singleton x `S.union` functionalNames t `S.union` processFreeNames p
processFreeNames (SendType x t p) = S.singleton x `S.union` freePropNames t `S.union` processFreeNames p
processFreeNames (Receive x y p) = S.delete y . S.insert x $ processFreeNames p
processFreeNames (ReplicateReceive x y p) = S.delete y . S.insert x $ processFreeNames p
processFreeNames (SendInl x p) = S.singleton x `S.union` processFreeNames p
processFreeNames (SendInr x p) = S.singleton x `S.union` processFreeNames p
processFreeNames (Case x p1 p2) = S.singleton x `S.union` processFreeNames p1 `S.union` processFreeNames p2
processFreeNames (Link x y) = S.fromList [x, y]
processFreeNames (LiftTerm x t) = S.singleton x `S.union` functionalFreeVariables t
processFreeNames (ParallelComposition p1 p2) = processFreeNames p1 `S.union` processFreeNames p2
processFreeNames (Corec x ys p zs) = S.difference (processFreeNames p `S.union` S.fromList zs) (S.insert x (S.fromList ys))
processFreeNames (Call x zs) = S.insert x . S.fromList $ zs
processFreeNames HoleTerm = S.empty

{-| Rename a var name in a process. P{x/u}. Replace the name u with x in P. Does not avoid capturing. -}
renameVar :: Process -> String -> String -> Process
renameVar Halt x u = Halt
renameVar (Nu y prop p) x u = Nu (if y == u then x else y) (renameVarProp prop x u) (renameVar p x u)
renameVar (Send v w p) x u = Send (if v == u then x else v) (if w == u then x else w) (renameVar p x u)
renameVar (SendTerm v t p) x u = SendTerm (if v == u then x else v) (substVarFunctional t x u) (renameVar p x u)
renameVar (SendType v t p) x u = SendType (if v == u then x else v) (substVarProp t x u) (renameVar p x u)
renameVar (Receive v w p) x u = Receive (if v == u then x else v) (if w == u then x else w) (renameVar p x u)
renameVar (ReplicateReceive v w p) x u = ReplicateReceive (if v == u then x else v) (if w == u then x else w) (renameVar p x u)
renameVar (SendInl v p) x u = SendInl (if v == u then x else v) (renameVar p x u)
renameVar (SendInr v p) x u = SendInr (if v == u then x else v) (renameVar p x u)
renameVar (Case v p1 p2) x u = Case (if v == u then x else v) (renameVar p1 x u) (renameVar p2 x u)
renameVar (Link v w) x u = Link (if v == u then x else v) (if w == u then x else w)
renameVar (LiftTerm v t) x u = LiftTerm (if v == u then x else v) (substVarFunctional t x u)
renameVar (ParallelComposition p1 p2) x u = ParallelComposition (renameVar p1 x u) (renameVar p2 x u)
renameVar (Corec y ys p zs) x u = Corec (if y == u then x else y) ((\y -> if y == x then u else y) <$> ys) (renameVar p x u) ((\y -> if y == x then u else y) <$> zs)
renameVar (Call y zs) x u = Call (if y == u then x else y) ((\y -> if y == x then u else y) <$> zs)
renameVar HoleTerm x u = HoleTerm

alphaConvertProcess :: Process -> S.Set String -> Process
alphaConvertProcess (Nu y prop p) names =
    let
        z = getFreshName (S.insert y $ names `S.union` propNames prop `S.union` processNames p)
    in
        Nu z prop (renameVar p z y)
alphaConvertProcess (Receive x y p) names =
    let
        z = getFreshName names
    in
        Receive x z (renameVar p z y)
alphaConvertProcess (ReplicateReceive x y p) names =
    let
        z = getFreshName names
    in
        ReplicateReceive x z (renameVar p z y)
alphaConvertProcess (Corec x ys p zs) names =
    let
        newZProc = renameVar p z x
        (newP, newYs, allNames) = L.foldl (\(latestP, newYs, allNames) y ->
            let
                newY = getFreshName allNames
            in
                (renameVar latestP newY y, newY:newYs, S.insert newY allNames)) (p, [], names) ys
        z = getFreshName allNames
    in
        Corec z newYs (renameVar newP z x) zs

{-| P{x/u} replace free occurances of u with x in P

>>> substVar (Send "x" "y" Halt) "z" "y"
Send "x" "z" Halt

>>> substVar (ParallelComposition (Nu "y" (Send "x" "y" Halt)) (Send "x" "y" (Receive "y" "w" Halt))) "z" "y"
ParallelComposition (Nu "y" (Send "x" "y" Halt)) (Send "x" "z" (Receive "z" "w" Halt))

>>> substVar (ParallelComposition (Nu "y" (Send "x" "y" Halt)) (Receive "x" "y" (Send "y" "w" Halt))) "z" "y"
ParallelComposition (Nu "y" (Send "x" "y" Halt)) (Receive "x" "y" (Send "y" "w" Halt))
 -}
substVar :: Process -> String -> String -> Process
substVar Halt x u = Halt
substVar (ParallelComposition p1 p2) x u = ParallelComposition (substVar p1 x u) (substVar p2 x u)
substVar outerP@(Nu y prop p) x u =
    let
        newY = if u == y then x else y
        newProp = substVarProp prop x u
        allNamesConsidered = S.fromList [y, x, u] `S.union` processNames p `S.union` propNames prop
    in
        if u == y then Nu y newProp p -- u is no longer free. No more work.
        else if x == y then substVar (alphaConvertProcess outerP allNamesConsidered) x u -- new variable name will be captured
        else Nu y newProp (substVar p x u)
substVar (Send y z p) x u =
    let
        newY = if y == u then x else y
        newZ = if z == u then x else z
    in
        Send newY newZ (substVar p x u)
substVar (SendTerm y t p) x u = SendTerm (if y == u then x else y) (substVarFunctional t x u) (substVar p x u)
substVar (SendType y t p) x u = SendType (if y == u then x else y) (substVarProp t x u) (substVar p x u)
substVar outerP@(Receive w z p) x u = let
    newW = if w == u then x else w
    allNamesConsidered = S.fromList [w, z, x, u] `S.union` processNames p
    in if z == u then Receive newW z p -- Variable being replaced is not free anymore.
    else if x == z then substVar (alphaConvertProcess outerP allNamesConsidered) x u -- New name will get captured.
    else Receive newW z (substVar p x u)
substVar outerP@(ReplicateReceive w z p) x u = let
    newW = if w == u then x else w
    allNamesConsidered = S.fromList [w, z, x, u] `S.union` processNames p
    in if z == u then ReplicateReceive newW z p -- Variable being replaced is not free anymore. Only replace w if it should be.
    else if x == z then substVar (alphaConvertProcess outerP allNamesConsidered) x u -- New name will get captured. Alpha convert and go again.
    else ReplicateReceive newW z (substVar p x u) -- No issues. Do regular substitution.
substVar (SendInl v p) x u = SendInl (if v == u then x else v) (substVar p x u)
substVar (SendInr v p) x u = SendInr (if v == u then x else v) (substVar p x u)
substVar (Case v p1 p2) x u = Case (if v == u then x else v) (substVar p1 x u) (substVar p2 x u)
substVar (Link v w) x u = Link (if v == u then x else v) (if w == u then x else w)
substVar (LiftTerm v t) x u = LiftTerm (if v == u then x else v) (substVarFunctional t x u)
substVar outerP@(Corec y ys p zs) x u = let
    newZs = ((\z -> if z == u then x else z) <$> zs)
    allNamesConsidered = S.fromList (y:x:u:(ys ++ zs)) `S.union` processNames p
    in if y == u || L.elem u ys then Corec y ys p newZs -- Variable being replaced is not free anymore. Only replace zs if they should be.
    else if x == y || x `L.elem` ys then substVar (alphaConvertProcess outerP allNamesConsidered) x u -- New name will get captured. Alpha convert and go again.
    else Corec y ys (substVar p x u) newZs -- No issues. Do regular substitution.
substVar (Call y zs) x u = Call (if y == u then x else y) ((\y -> if y == u then x else y) <$> zs)
substVar HoleTerm x u = HoleTerm

type Context = Map String Proposition

getContextNames :: Context -> S.Set String
getContextNames c = S.fromList (Data.Map.keys c) `S.union` S.unions (propNames <$> Data.Map.elems c)

getContextFreeNames :: Context -> S.Set String
getContextFreeNames c = S.fromList (Data.Map.keys c) `S.union` S.unions (freePropNames <$> Data.Map.elems c)

alphaEquivalentContexts :: Context -> Context -> Bool
alphaEquivalentContexts ctx1 ctx2 = let
    ctx1Subset2 = Data.Map.foldlWithKey' (\acc k v -> case Data.Map.lookup k ctx2 of Just res -> acc && alphaEquivalent v res; Nothing -> False) False ctx1
    ctx2Subset1 = Data.Map.foldlWithKey' (\acc k v -> case Data.Map.lookup k ctx1 of Just res -> acc && alphaEquivalent v res; Nothing -> False) False ctx2
    in ctx1Subset2 && ctx2Subset1

{-| Map from bound process variable names to parameter list, functional context, unrestricted context, linear context, channel name, type variable name -}
data BindingSequent = BindingSequent {
    bindingTyVarContext :: S.Set String,
    bindingFnContext :: FunctionalContext,
    bindingUC :: Context,
    bindingLC :: Context,
    bindingChan :: String,
    bindingTyVar :: String
} deriving (Eq, Show, Read)

getBindingSequentNames :: BindingSequent -> S.Set String
getBindingSequentNames (BindingSequent tv fc uc lc c v) = S.insert c $ S.insert v $ tv `S.union` getFunctionalContextNames fc `S.union` getContextNames uc `S.union` getContextNames lc

getBindingSequentFreeNames :: BindingSequent -> S.Set String
getBindingSequentFreeNames (BindingSequent tv fc uc lc c v) = S.insert c $ S.insert v $ tv `S.union` getFunctionalContextFreeNames fc `S.union` getContextFreeNames uc `S.union` getContextFreeNames lc

type RecursiveBindings = Map String ([String], BindingSequent)

getRecursiveBindingsNames :: RecursiveBindings -> S.Set String
getRecursiveBindingsNames rb = S.fromList (Data.Map.keys rb) `S.union` S.unions ((\(ps, bs) -> S.fromList ps `S.union` getBindingSequentNames bs) <$> Data.Map.elems rb)

getRecursiveBindingsFreeNames :: RecursiveBindings -> S.Set String
getRecursiveBindingsFreeNames rb = S.fromList (Data.Map.keys rb) `S.union` S.unions ((\(ps, bs) -> S.fromList ps `S.union` getBindingSequentFreeNames bs) <$> Data.Map.elems rb)

data Sequent = Sequent {
    tyVarContext :: S.Set String,
    fnContext :: FunctionalContext,
    unrestrictedContext :: Context,
    linearContext :: Context,
    recursiveBindings :: RecursiveBindings,
    channel :: String,
    goalProposition :: Proposition
} deriving (Eq)

seqToS :: Sequent -> String
seqToS seq =
    if length singleLine > 80
    then multiLine
    else singleLine
  where
    -- Extract and format the raw components into lists of strings
    tyVars = S.toList (tyVarContext seq)
    fns = [k ++ ":" ++ ftToS v | (k,v) <- ctxToList (fnContext seq)]
    unres = [k ++ ":" ++ propToS v | (k,v) <- Data.Map.toList (unrestrictedContext seq)]
    lin = [k ++ ":" ++ propToS v | (k,v) <- Data.Map.toList (linearContext seq)]
    goal = channel seq ++ ":" ++ propToS (goalProposition seq)

    -- Define the single-line representation (Original logic)
    -- Join the internal lists with comma-space, and the sections with semicolons.
    parts = [tyVars, fns, unres, lin]
    joinedParts = L.map (L.intercalate ", ") parts
    singleLine = L.intercalate "; " joinedParts ++ " |- " ++ goal

    -- Define the multi-line representation
    -- If a specific context list is empty, keep it empty. 
    -- Otherwise, join items with newlines and indentation.
    formatBlock [] = ""
    formatBlock items = "\n    " ++ L.intercalate ",\n    " items

    multiLine =
        "\n  Ω: " ++ (if L.null tyVars then "" else formatBlock tyVars) ++ ";" ++
        "\n  Ψ:  " ++ (if L.null fns then "" else formatBlock fns) ++ ";" ++
        "\n  Γ:  " ++ (if L.null unres then "" else formatBlock unres) ++ ";" ++
        "\n  Δ: " ++ (if L.null lin then "" else formatBlock lin) ++
        "\n  |- " ++ goal

getSequentNames :: Sequent -> S.Set String
getSequentNames (Sequent tv fc uc lc eta ch goalProp) = S.insert ch $ tv `S.union` getFunctionalContextNames fc `S.union` getContextNames uc `S.union` getContextNames lc `S.union` propNames goalProp `S.union` getRecursiveBindingsNames eta

getSequentFreeNames :: Sequent -> S.Set String
getSequentFreeNames (Sequent tv fc uc lc eta ch goalProp) = S.insert ch $ tv `S.union` getFunctionalContextFreeNames fc `S.union` getContextFreeNames uc `S.union` getContextFreeNames lc `S.union` freePropNames goalProp `S.union` getRecursiveBindingsFreeNames eta

{-| Rename a type variable in the type variable context. substVarTyVarContext ctx x u replaces u with x in ctx. -}
substVarTyVarContext :: S.Set String -> String -> String -> S.Set String
substVarTyVarContext ctx x u = S.fromList $ (\n -> if n == u then x else n) <$> S.toList ctx

{-| Rename a variable in a context. substVarContext ctx x u replaces u with x in ctx. -}
substVarContext :: Context -> String -> String -> Context
substVarContext ctx x u = Data.Map.fromList $ (\(n, k) -> (if n == u then x else n, substVarProp k x u)) <$> Data.Map.toList ctx


-- the correct type, or extract a term after applying tactics
-- a is type of functional proof
-- b is type of functional propositions
-- Strings refer to variables in the rule alphabetically according to "Dependent
-- Session Types via Intuitionistic Linear Type Theory" by Toninho et al.
data Proof = IdRule String String (S.Set String) FunctionalContext Context RecursiveBindings Proposition
    | FunctionalTermRightRule String FunctionalProof (S.Set String) Context RecursiveBindings
    | FunctionalTermLeftRule String Proof
    | UnitRightRule String (S.Set String) FunctionalContext Context RecursiveBindings
    | UnitLeftRule String Proof
    | ReplicationRightRule String Proof
    | ReplicationLeftRule String String Proof
    | CopyRule String String Proof
    | WithRightRule Proof Proof
    | WithLeft1Rule String Proposition Proof
    | WithLeft2Rule String Proposition Proof
    | ImpliesRightRule String Proof
    | ImpliesLeftRule String Proof Proof
    | TensorRightRule Proof Proof
    | TensorLeftRule String String Proof
    | PlusRight1Rule Proposition Proof
    | PlusRight2Rule Proposition Proof
    | PlusLeftRule String Proof Proof
    | ForallRightRule String Proof
    | ForallLeftRule String String FunctionalProof Proof
    | ExistsRightRule String FunctionalProof Proof
    | ExistsLeftRule String String Proof
    | ForallRight2Rule String Proof
    | ForallLeft2Rule String String Proposition Proof
    | ExistsRight2Rule String Proposition Proof
    | ExistsLeft2Rule String String Proof
    | CutRule Proof Proof
    | CutReplicationRule String Proof Proof
    | TyNuRightRule String [String] Proof
    | TyNuLeftRule String String Proof
    | TyVarRule RecursiveBindings String [String]
    | ReplWeakening String Proposition Proof
    | FnWeakening String FunctionalTerm Proof
    | TyVarWeakening String Proof
    | RecBindingWeakening String ([String], BindingSequent) Proof
    | ProcessFiatRule String String Proposition Proof -- ProcessName:x::Prop
    | HoleRule (S.Set String) FunctionalContext Context Context RecursiveBindings String Proposition
    deriving (Eq, Show, Read)

-- Extracts children from Proof as Either FunctionalProof or Proof
subProofs :: Proof -> [Either FunctionalProof Proof]
subProofs rule = case rule of
    -- Cases with FunctionalProof
    FunctionalTermRightRule _ fp _ _ _ -> [Left fp]
    ForallLeftRule _ _ fp p -> [Left fp, Right p]
    ExistsRightRule _ fp p -> [Left fp, Right p]

    -- Binary Proof cases
    WithRightRule p1 p2 -> [Right p1, Right p2]
    ImpliesLeftRule _ p1 p2 -> [Right p1, Right p2]
    TensorRightRule p1 p2 -> [Right p1, Right p2]
    PlusLeftRule _ p1 p2 -> [Right p1, Right p2]
    CutRule p1 p2 -> [Right p1, Right p2]
    CutReplicationRule _ p1 p2 -> [Right p1, Right p2]

    -- Unary Proof cases
    FunctionalTermLeftRule _ p -> [Right p]
    UnitLeftRule _ p -> [Right p]
    ReplicationRightRule _ p -> [Right p]
    ReplicationLeftRule _ _ p -> [Right p]
    CopyRule _ _ p -> [Right p]
    WithLeft1Rule _ _ p -> [Right p]
    WithLeft2Rule _ _ p -> [Right p]
    ImpliesRightRule _ p -> [Right p]
    TensorLeftRule _ _ p -> [Right p]
    PlusRight1Rule _ p -> [Right p]
    PlusRight2Rule _ p -> [Right p]
    ForallRightRule _ p -> [Right p]
    ExistsLeftRule _ _ p -> [Right p]
    ForallRight2Rule _ p -> [Right p]
    ForallLeft2Rule _ _ _ p -> [Right p]
    ExistsRight2Rule _ _ p -> [Right p]
    ExistsLeft2Rule _ _ p -> [Right p]
    TyNuRightRule _ _ p -> [Right p]
    TyNuLeftRule _ _ p -> [Right p]
    ReplWeakening _ _ p -> [Right p]
    FnWeakening _ _ p -> [Right p]
    TyVarWeakening _ p -> [Right p]
    RecBindingWeakening _ _ p -> [Right p]
    ProcessFiatRule _ _ _ p -> [Right p]

    -- Leaf cases
    IdRule{} -> []
    UnitRightRule{} -> []
    TyVarRule{} -> []
    HoleRule{} -> []

foldProof :: ([a] -> a) -> ([a] -> a) -> Proof -> a
foldProof fProof fFunc rule =
    fProof (L.map resolve (subProofs rule))
  where
    resolve (Left fp) = foldFunctionalProof fFunc fp
    resolve (Right p) = foldProof fProof fFunc p

proofSize :: Proof -> Integer
proofSize = foldProof sumResults sumResults
  where
    sumResults results = 1 + sum results

proofDepth :: Proof -> Integer
proofDepth = foldProof maxDepth maxDepth
  where
    maxDepth results = 1 + maximum (0 : results)

{-| Get all the names used in a proof derivation. -}
getProofNames :: Proof -> S.Set String
getProofNames (IdRule x z tv fc c eta p) = S.fromList [x, z] `S.union` tv `S.union` getFunctionalContextNames fc `S.union` getContextNames c `S.union` propNames p `S.union` getRecursiveBindingsNames eta
getProofNames (FunctionalTermRightRule z p tv c eta) = S.singleton z `S.union` tv `S.union` getFunctionalProofNames p `S.union` getContextNames c `S.union` getRecursiveBindingsNames eta
getProofNames (FunctionalTermLeftRule x p) = S.singleton x `S.union` getProofNames p
getProofNames (UnitRightRule z tv fc uc eta) = S.singleton z `S.union` tv `S.union` getFunctionalContextNames fc `S.union` getContextNames uc `S.union` getRecursiveBindingsNames eta
getProofNames (UnitLeftRule x p) = S.singleton x `S.union` getProofNames p
getProofNames (ReplicationRightRule z p) = S.singleton z `S.union` getProofNames p
getProofNames (ReplicationLeftRule u x p) = S.fromList [u,x] `S.union` getProofNames p
getProofNames (CopyRule u y p) = S.fromList [u,y] `S.union` getProofNames p
getProofNames (WithRightRule p1 p2) = getProofNames p1 `S.union` getProofNames p2
getProofNames (WithLeft1Rule x prop p) = S.singleton x `S.union` propNames prop `S.union` getProofNames p
getProofNames (WithLeft2Rule x prop p) = S.singleton x `S.union` propNames prop `S.union` getProofNames p
getProofNames (TensorRightRule p1 p2) = getProofNames p1 `S.union` getProofNames p2
getProofNames (TensorLeftRule x y p) = S.fromList [x,y] `S.union` getProofNames p
getProofNames (PlusRight1Rule prop p) = propNames prop `S.union` getProofNames p
getProofNames (PlusRight2Rule prop p) = propNames prop `S.union` getProofNames p
getProofNames (PlusLeftRule x p1 p2) = S.singleton x `S.union` getProofNames p1 `S.union` getProofNames p2
getProofNames (ImpliesRightRule x p) = S.insert x $ getProofNames p
getProofNames (ImpliesLeftRule x p1 p2) = S.insert x $ getProofNames p1 `S.union` getProofNames p2
getProofNames (ForallRightRule x p) = S.singleton x `S.union` getProofNames p
getProofNames (ForallLeftRule x y p1 p2) = S.fromList [x, y] `S.union` getFunctionalProofNames p1 `S.union` getProofNames p2
getProofNames (ExistsRightRule x p1 p2) = S.singleton x `S.union` getFunctionalProofNames p1 `S.union` getProofNames p2
getProofNames (ExistsLeftRule x y p) = S.singleton x `S.union` getProofNames p
getProofNames (ForallRight2Rule x p) = S.singleton x `S.union` getProofNames p
getProofNames (ForallLeft2Rule x y p1 p2) = S.fromList [x, y] `S.union` propNames p1 `S.union` getProofNames p2
getProofNames (ExistsRight2Rule x p1 p2) = S.singleton x `S.union` propNames p1 `S.union` getProofNames p2
getProofNames (ExistsLeft2Rule x y p) = S.singleton x `S.union` getProofNames p
getProofNames (CutRule p1 p2) = getProofNames p1 `S.union` getProofNames p2
getProofNames (CutReplicationRule u p1 p2) = S.singleton u `S.union` getProofNames p1 `S.union` getProofNames p2
getProofNames (TyNuRightRule x zs p) = S.fromList (x:zs) `S.union` getProofNames p
getProofNames (TyNuLeftRule c x p) = S.fromList [c, x] `S.union` getProofNames p
getProofNames (TyVarRule eta x zs) = S.insert x $ S.fromList zs `S.union` getRecursiveBindingsNames eta
getProofNames (ReplWeakening u prop proof) = S.insert u $ propNames prop `S.union` getProofNames proof
getProofNames (FnWeakening a fterm proof) = S.insert a $ functionalNames fterm `S.union` getProofNames proof
getProofNames (TyVarWeakening a proof) = S.insert a $ getProofNames proof
getProofNames (RecBindingWeakening a (ps, bs) proof) = S.fromList (a:ps) `S.union` getBindingSequentNames bs `S.union` getProofNames proof
getProofNames (HoleRule tv fc uc lc eta z p) = tv `S.union` getFunctionalContextNames fc `S.union` getContextNames uc `S.union` getContextNames lc `S.union` propNames p `S.union` S.singleton z `S.union` getRecursiveBindingsNames eta
getProofNames (ProcessFiatRule procName chanName prop p) = S.fromList [procName, chanName] `S.union` propNames prop `S.union` getProofNames p

isFreshInProof :: String -> Proof -> Bool
isFreshInProof x p = not $ x `S.member` getProofNames p

{-| renameVarInProof x y = P[x/y]. Rename y with x in proof P. -}
renameVarInProof :: Proof -> String -> String -> Proof
renameVarInProof p x y {- DBG.trace "Renaming" True-} = if isFreshInProof x p
    then go p
    else renameVarInProof (renameVarInProof p newFreshName x) x y -- Rename x first, then y
    where
        allVars = S.fromList [x, y] `S.union` getProofNames p

        newFreshName :: String
        newFreshName = getFreshName $ S.fromList [x, y] `S.union` getProofNames p

        swap :: String -> String
        swap test = if test == y then x else test
        swapSet :: S.Set String -> S.Set String
        swapSet = (swap `S.map`)

        swapFTerm :: FunctionalTerm -> FunctionalTerm
        swapFTerm t = functionalSubst t (Var x) y

        swapFn :: FunctionalContext -> FunctionalContext
        swapFn fnCtx = renameVarInFnCtx allVars fnCtx x y

        swapCtx :: Context -> Context
        swapCtx ctx = Data.Map.fromList $ (\(k, a) -> (swap k, substVarProp a x y)) <$> Data.Map.toList ctx

        swapBinding :: BindingSequent -> BindingSequent
        swapBinding (BindingSequent tv fc uc lc c v) = BindingSequent (swap `S.map` tv) (swapFn fc) (swapCtx uc) (swapCtx lc) (swap c) (swap v)

        swapRec :: RecursiveBindings -> RecursiveBindings
        swapRec eta = Data.Map.fromList $ (\(k, (ps, bs)) -> (swap k, (swap <$> ps, swapBinding bs))) <$> Data.Map.toList eta

        swapProp :: Proposition -> Proposition
        swapProp p = substVarProp p x y

        swapFnProof :: FunctionalProof -> FunctionalProof
        swapFnProof p = ECC.renameVarInProof allVars p x y

        go :: Proof -> Proof
        go (IdRule x z tv fc c eta p) = IdRule (swap x) (swap z) (swapSet tv) (swapFn fc) (swapCtx c) (swapRec eta) (swapProp p)
        go (FunctionalTermRightRule z p tv c eta) = FunctionalTermRightRule (swap z) (swapFnProof p) (swap `S.map` tv) (swapCtx c) (swapRec eta)
        go (FunctionalTermLeftRule x p) = FunctionalTermLeftRule (swap x) (go p)
        go (UnitRightRule z tv fc uc eta) = UnitRightRule (swap z) (swapSet tv) (swapFn fc) (swapCtx uc) (swapRec eta)
        go (UnitLeftRule x p) = UnitLeftRule (swap x) (go p)
        go (ReplicationRightRule z p) = ReplicationRightRule (swap z) (go p)
        go (ReplicationLeftRule u x p) = ReplicationLeftRule (swap u) (swap x) (go p)
        go (CopyRule u y p) = CopyRule (swap u) (swap y) (go p)
        go (WithRightRule p1 p2) = WithRightRule (go p1) (go p2)
        go (WithLeft1Rule z prop p) = WithLeft1Rule (swap z) (swapProp prop) (go p)
        go (WithLeft2Rule z prop p) = WithLeft2Rule (swap z) (swapProp prop) (go p)
        go (TensorRightRule p1 p2) = TensorRightRule (go p1) (go p2)
        go (TensorLeftRule x y p) = TensorLeftRule (swap x) (swap y) (go p)
        go (PlusRight1Rule prop p) = PlusRight1Rule (swapProp prop) (go p)
        go (PlusRight2Rule prop p) = PlusRight2Rule (swapProp prop) (go p)
        go (PlusLeftRule x p1 p2) = PlusLeftRule (swap x) (go p1) (go p2)
        go (ImpliesRightRule x p) = ImpliesRightRule (swap x) (go p)
        go (ImpliesLeftRule x p1 p2) = ImpliesLeftRule (swap x) (go p1) (go p2)
        go (ForallRightRule x p) = ForallRightRule (swap x) (go p)
        go (ForallLeftRule x y p1 p2) = ForallLeftRule (swap x) (swap y) (swapFnProof p1) (go p2)
        go (ExistsRightRule x p1 pOther) = ExistsRightRule (swap x) (swapFnProof p1) (go pOther)--(go p2)
        go (ExistsLeftRule x y p) = ExistsLeftRule (swap x) (swap y) (go p)
        go (ForallRight2Rule x p) = ForallRight2Rule (swap x) (go p)
        go (ForallLeft2Rule x y p1 p2) = ForallLeft2Rule (swap x) (swap y) (swapProp p1) (go p2)
        go (ExistsRight2Rule x p1 p2) = ExistsRight2Rule (swap x) (swapProp p1) (go p2)
        go (ExistsLeft2Rule x y p) = ExistsLeft2Rule (swap x) (swap y) (go p)
        go (CutRule p1 p2) = CutRule (go p1) (go p2)
        go (CutReplicationRule u p1 p2) = CutReplicationRule (swap u) (go p1) (go p2)
        go (TyNuRightRule x zs p) = TyNuRightRule (swap x) (swap <$> zs) (go p)
        go (TyNuLeftRule c x p) = TyNuLeftRule (swap c) (swap x) (go p)
        go (TyVarRule eta x zs) = TyVarRule (swapRec eta) (swap x) (swap <$> zs)
        go (ReplWeakening u prop proof) = ReplWeakening (swap u) (swapProp prop) (go proof)
        go (FnWeakening a fterm proof) = FnWeakening (swap a) (swapFTerm fterm) (go proof)
        go (TyVarWeakening a proof) = TyVarWeakening (swap a) (go proof)
        go (RecBindingWeakening a (ps, bs) p) = RecBindingWeakening (swap a) ((swap <$> ps), (swapBinding bs)) (go p)
        go (HoleRule tv fc uc lc eta z p) = HoleRule (swapSet tv) (swapFn fc) (swapCtx uc) (swapCtx lc) (swapRec eta) (swap z) (swapProp p)
        go (ProcessFiatRule procName chanName prop p) = ProcessFiatRule (swap procName) (swap chanName) (swapProp prop) (go p)

{-| A{y/N} replace N with y in A. -}
abstTerm :: Proposition -> String -> FunctionalTerm -> Proposition
abstTerm Unit y n = Unit
abstTerm (Lift t) y n = Lift (abstTermFunctional t y n)
abstTerm (Implication p1 p2) y n = Implication (abstTerm p1 y n) (abstTerm p2 y n)
abstTerm (Tensor p1 p2) y n = Tensor (abstTerm p1 y n) (abstTerm p2 y n)
abstTerm (Replication p) y n = Replication (abstTerm p y n)
abstTerm (With p1 p2) y n = With (abstTerm p1 y n) (abstTerm p2 y n)
abstTerm (Plus p1 p2) y n = Plus (abstTerm p1 y n) (abstTerm p2 y n)
abstTerm (Forall x p1 p2) y n = if x `S.member` functionalFreeVariables n then (Forall x (abstTermFunctional p1 y n) p2) -- n is no longer possible in p2
    else if x == y then abstTerm (alphaConvertProp (Forall x p1 p2) (S.fromList [x, y] `S.union` functionalNames p1 `S.union` propNames p2 `S.union` functionalNames n)) y n -- new var will be captured
    else Forall x (abstTermFunctional p1 y n) (abstTerm p2 y n)
abstTerm (Exists x p1 p2) y n = if x `S.member` functionalFreeVariables n then (Exists x (abstTermFunctional p1 y n) p2) -- n is no longer possible in p2
    else if x == y then abstTerm (alphaConvertProp (Exists x p1 p2) (S.fromList [x, y] `S.union` functionalNames p1 `S.union` propNames p2 `S.union` functionalNames n)) y n -- new var will be captured
    else Exists x (abstTermFunctional p1 y n) (abstTerm p2 y n)
abstTerm (Forall2 x p2) y n = if x `S.member` functionalFreeVariables n then (Forall2 x p2) -- n is no longer possible in p2
    else if x == y then abstTerm (alphaConvertProp (Forall2 x p2) (S.fromList [x, y] `S.union` propNames p2 `S.union` functionalNames n)) y n -- new var will be captured
    else Forall2 x (abstTerm p2 y n)
abstTerm (Exists2 x p2) y n = if x `S.member` functionalFreeVariables n then (Exists2 x p2) -- n is no longer possible in p2
    else if x == y then abstTerm (alphaConvertProp (Exists2 x p2) (S.fromList [x, y] `S.union` propNames p2 `S.union` functionalNames n)) y n -- new var will be captured
    else Exists2 x (abstTerm p2 y n)
abstTerm (TyNu x p) y n = if x `S.member` functionalFreeVariables n then (TyNu x p)
    else if x == y then abstTerm (alphaConvertProp (TyNu x p) (S.fromList [x, y] `S.union` propNames p `S.union` functionalNames n)) y n -- new var will be captured
    else TyNu x (abstTerm p y n)
abstTerm (TyVar x) y n = TyVar x

{-| A{y/N} replace N with y in A.
>>> abstProp Unit ("x") Unit
TyVar "x"

>>> abstProp Unit "x" (TyVar "y")
Unit
-}
abstProp :: Proposition -> String -> Proposition -> Proposition
abstProp n1 y n | n1 == n = TyVar y
abstProp Unit y n = Unit
abstProp (Lift t) y n = Lift t
abstProp (Implication p1 p2) y n = Implication (abstProp p1 y n) (abstProp p2 y n)
abstProp (Tensor p1 p2) y n = Tensor (abstProp p1 y n) (abstProp p2 y n)
abstProp (Replication p) y n = Replication (abstProp p y n)
abstProp (With p1 p2) y n = With (abstProp p1 y n) (abstProp p2 y n)
abstProp (Plus p1 p2) y n = Plus (abstProp p1 y n) (abstProp p2 y n)
abstProp (Forall x p1 p2) y n = if x `S.member` freePropNames n then (Forall x p1 p2) -- n is no longer possible in p2
    else if x == y then abstProp (alphaConvertProp (Forall x p1 p2) (S.fromList [x, y] `S.union` functionalNames p1 `S.union` propNames p2 `S.union` freePropNames n)) y n -- new var will be captured
    else Forall x p1 (abstProp p2 y n)
abstProp (Exists x p1 p2) y n = if x `S.member` freePropNames n then (Exists x p1 p2) -- n is no longer possible in p2
    else if x == y then abstProp (alphaConvertProp (Exists x p1 p2) (S.fromList [x, y] `S.union` functionalNames p1 `S.union` propNames p2 `S.union` freePropNames n)) y n -- new var will be captured
    else Exists x p1 (abstProp p2 y n)
abstProp (Forall2 x p2) y n = if x `S.member` freePropNames n then (Forall2 x p2) -- n is no longer possible in p2
    else if x == y then abstProp (alphaConvertProp (Forall2 x p2) (S.fromList [x, y] `S.union` propNames p2 `S.union` freePropNames n)) y n -- new var will be captured
    else Forall2 x (abstProp p2 y n)
abstProp (Exists2 x p2) y n = if x `S.member` freePropNames n then (Exists2 x p2) -- n is no longer possible in p2
    else if x == y then abstProp (alphaConvertProp (Exists2 x p2) (S.fromList [x, y] `S.union` propNames p2 `S.union` freePropNames n)) y n -- new var will be captured
    else Exists2 x (abstProp p2 y n)
abstProp (TyNu x p) y n = if x `S.member` freePropNames n then (TyNu x p)
    else if x == y then abstProp (alphaConvertProp (TyNu x p) (S.fromList [x, y] `S.union` propNames p `S.union` freePropNames n)) y n -- new var will be captured
    else TyNu x (abstProp p y n)
abstProp (TyVar x) y n = TyVar x

{-| Folds up an unfolded recursive type. -}
foldUpRec :: String -> Proposition -> Proposition
foldUpRec x Unit = Unit
foldUpRec x (Lift t) = Lift t
foldUpRec x (Implication p1 p2) = Implication (foldUpRec x p1) (foldUpRec x p2)
foldUpRec x (Tensor p1 p2) = Tensor (foldUpRec x p1) (foldUpRec x p2)
foldUpRec x (Replication p) = Replication (foldUpRec x p)
foldUpRec x (With p1 p2) = With (foldUpRec x p1) (foldUpRec x p2)
foldUpRec x (Plus p1 p2) = Plus (foldUpRec x p1) (foldUpRec x p2)
foldUpRec x (Forall y p1 p2) = Forall y p1 (foldUpRec x p2) -- Doesn't bind at type variable level, so no issues.
foldUpRec x (Exists y p1 p2) = Exists y p1 (foldUpRec x p2)
foldUpRec x (Forall2 y p2) = if y == x then Forall2 y p2 else Forall2 y (foldUpRec x p2)
foldUpRec x (Exists2 y p2) = if y == x then Exists2 y p2 else Exists2 y (foldUpRec x p2)
foldUpRec x (TyNu y p) = if x == y then TyVar x else TyNu y (foldUpRec x p)
foldUpRec x (TyVar y) = TyVar y

{-| Unfolds a recursive type one level. unfoldRec a x b puts Nu x.a on x in b -}
unfoldRec :: Proposition -> String -> Proposition -> Proposition
unfoldRec a x Unit = Unit
unfoldRec a x (Lift t) = Lift t
unfoldRec a x (Implication p1 p2) = Implication (unfoldRec a x p1) (unfoldRec a x p2)
unfoldRec a x (Tensor p1 p2) = Tensor (unfoldRec a x p1) (unfoldRec a x p2)
unfoldRec a x (Replication p) = Replication (unfoldRec a x p)
unfoldRec a x (With p1 p2) = With (unfoldRec a x p1) (unfoldRec a x p2)
unfoldRec a x (Plus p1 p2) = Plus (unfoldRec a x p1) (unfoldRec a x p2)
unfoldRec a x (Forall y p1 p2) = if x == y then (Forall y p1 p2) -- variable being replaced is now captured
    else if y `S.member` freePropNames a then unfoldRec a x (alphaConvertProp (Forall y p1 p2) (S.fromList [x, y] `S.union` freePropNames a `S.union` functionalFreeVariables p1 `S.union` freePropNames p2)) -- variables in a will be captured
    else Forall y p1 $ unfoldRec a x p2 -- no issues
unfoldRec a x (Exists y p1 p2) = if x == y then (Exists y p1 p2) -- variable being replaced is now captured
    else if y `S.member` freePropNames a then unfoldRec a x (alphaConvertProp (Exists y p1 p2) (S.fromList [x, y] `S.union` freePropNames a `S.union` functionalFreeVariables p1 `S.union` freePropNames p2)) -- variables in a will be captured
    else Exists y p1 $ unfoldRec a x p2 -- no issues
unfoldRec a x (Forall2 y p2) = if x == y then (Forall2 y p2) -- variable being replaced is now captured
    else if y `S.member` freePropNames a then unfoldRec a x (alphaConvertProp (Forall2 y p2) (S.fromList [x, y] `S.union` freePropNames a `S.union` freePropNames p2)) -- variables in a will be captured
    else Forall2 y $ unfoldRec a x p2 -- no issues
unfoldRec a x (Exists2 y p2) = if x == y then (Exists2 y p2) -- variable being replaced is now captured
    else if y `S.member` freePropNames a then unfoldRec a x (alphaConvertProp (Exists2 y p2) (S.fromList [x, y] `S.union` freePropNames a `S.union` freePropNames p2)) -- variables in a will be captured
    else Exists2 y $ unfoldRec a x p2 -- no issues
unfoldRec a x (TyNu y p) = if x == y then TyNu y p -- Var being unfolded is captured. Nothing else to do.
    else if S.member y (freePropNames a) then unfoldRec a x (alphaConvertProp (TyNu y p) (S.fromList [x,y] `S.union` propNames a `S.union` propNames p))
    else TyNu y (unfoldRec a x p)
unfoldRec a x (TyVar y) = if x == y then TyNu x a else TyVar y

validBindingSequent :: BindingSequent -> Bool
validBindingSequent (BindingSequent tv fc uc lc z p) = L.null (ctxKeys fc `L.intersect` Data.Map.keys uc `L.intersect` Data.Map.keys lc) && not (ctxMember z fc || Data.Map.member z uc || Data.Map.member z lc)

validRecursiveBindings :: RecursiveBindings -> Bool
validRecursiveBindings eta = Data.Map.foldl (\acc (ps, bs) -> acc && validBindingSequent bs) True eta

validSequent :: Sequent -> Bool
validSequent (Sequent tv fc uc lc eta z p) = L.null (ctxKeys fc `L.intersect` Data.Map.keys uc `L.intersect` Data.Map.keys lc) && not (ctxMember z fc || Data.Map.member z uc || Data.Map.member z lc) && validRecursiveBindings eta

{-| Checks that a type variable occurs in a strictly positive position in a
proposition.

>>> isStrictlyPositive "Y" (TyVar "Y")
True

>>> isStrictlyPositive "Y" (Implication (TyVar "Y") (Unit))
True

>>> isStrictlyPositive "Y" (Implication (Implication Unit (TyVar "Y")) (Unit))
True

>>> isStrictlyPositive "Y" (Implication (Implication (TyVar "Y") Unit) (Unit))
False
-}
isStrictlyPositive :: String -> Proposition -> Bool
isStrictlyPositive y p = go y p
    where
        checkLeft :: String -> Proposition -> Bool
        checkLeft y1 (TyVar y2) | y1 == y2 = False
        checkLeft y1 (Implication p1 p2) = checkLeft y p1 && checkLeft y p2
        checkLeft y1 (Tensor p1 p2) = checkLeft y p1 && checkLeft y p2
        checkLeft y1 (Replication p1) = checkLeft y p1
        checkLeft y1 (With p1 p2) = checkLeft y p1 && checkLeft y p2
        checkLeft y1 (Plus p1 p2) = checkLeft y p1 && checkLeft y p2
        checkLeft y (Forall x p1 p2) | x /= y = checkLeft y p2
        checkLeft y (Exists x p1 p2) | x /= y = checkLeft y p2
        checkLeft y (Forall2 x p1) | x /= y = checkLeft y p1
        checkLeft y (Exists2 x p1) | x /= y = checkLeft y p1
        checkLeft y _ = True -- Variable is shadowed or a lift/tyvar of another var/unit is encountered

        checkCons :: String -> Proposition -> Bool
        checkCons y (Implication p1 p2) = checkLeft y p1 && checkCons y p2
        checkCons y (Tensor p1 p2) = checkCons y p1 && checkCons y p2
        checkCons y (Replication p1) = checkCons y p1
        checkCons y (With p1 p2) = checkCons y p1 && checkCons y p2
        checkCons y (Plus p1 p2) = checkCons y p1 && checkCons y p2
        checkCons y (Forall x p1 p2) | x /= y = checkCons y p2
        checkCons y (Exists x p1 p2) | x /= y = checkCons y p2
        checkCons y (Forall2 x p1) | x /= y = checkCons y p1
        checkCons y (Exists2 x p1) | x /= y = checkCons y p1
        checkCons y (TyNu x p1) | x /= y = checkCons y p1
        checkCons y _ = True -- Variable is shadowed or a lift/tyvar/unit is encountered

        go :: String -> Proposition -> Bool
        go y (Implication p1 p2) = checkCons y p1 && go y p2
        go y (Tensor p1 p2) = go y p1 && go y p2
        go y (Replication p1) = go y p1
        go y (With p1 p2) = go y p1 && go y p2
        go y (Plus p1 p2) = go y p1 && go y p2
        go y (Forall x p1 p2) | x /= y = go y p2
        go y (Exists x p1 p2) | x /= y = go y p2
        go y (Forall2 x p1) | x /= y = go y p1
        go y (Exists2 x p1) | x /= y = go y p1
        go y (TyNu x p1) | x /= y = go y p1
        go y _ = True -- Variable is shadowed or a lift/tyvar/unit is encountered

wellFormedTypeWithFreeVars :: Proposition -> Either String ()
wellFormedTypeWithFreeVars b = case b of
    Unit -> return ()
    Lift ft -> return ()
    Implication p1 p2 -> wf2 p1 p2
    Tensor p1 p2 -> wf2 p1 p2
    Replication p -> wf p
    With p1 p2 -> wf2 p1 p2
    Plus p1 p2 -> wf2 p1 p2
    Forall x p1 p2 -> wf p2
    Exists x p1 p2 -> wf p2
    Forall2 x p -> wellFormedTypeWithFreeVars p
    Exists2 x p -> wellFormedTypeWithFreeVars p
    TyNu x p -> unless (isStrictlyPositive x p) (Left (x ++ " is not strictly positive in " ++ propToS p)) >> wellFormedTypeWithFreeVars p
    TyVar x -> return ()
    where
        wf2 p1 p2 = wellFormedTypeWithFreeVars p1 >> wellFormedTypeWithFreeVars p2
        wf = wellFormedTypeWithFreeVars

wellFormedType :: S.Set String -> Proposition -> Either String ()
wellFormedType tyVarContext b = case b of
    Unit -> return ()
    Lift ft -> return ()
    Implication p1 p2 -> wf2 p1 p2
    Tensor p1 p2 -> wf2 p1 p2
    Replication p -> wf p
    With p1 p2 -> wf2 p1 p2
    Plus p1 p2 -> wf2 p1 p2
    Forall x p1 p2 -> wf p2
    Exists x p1 p2 -> wf p2
    Forall2 x p -> wellFormedType (S.insert x tyVarContext) p
    Exists2 x p -> wellFormedType (S.insert x tyVarContext) p
    TyNu x p -> unless (isStrictlyPositive x p) (Left (x ++ " is not strictly positive in " ++ propToS p)) >> wellFormedType (S.insert x tyVarContext) p
    TyVar x -> if S.member x tyVarContext then return () else Left (x ++ " is free in what should be a well-formed type.")
    where
        wf2 p1 p2 = wellFormedType tyVarContext p1 >> wellFormedType tyVarContext p2
        wf = wellFormedType tyVarContext

verifyProofM :: Proof -> Either String (Process, Sequent)
verifyProofM (IdRule x z tv fc c eta p) = do
    let xValid = not $ ctxMember x fc || Data.Map.member x c
        zValid = not $ ctxMember z fc || Data.Map.member z c
        allValid = S.intersection (S.fromList (ctxKeys fc)) (S.fromList (Data.Map.keys c)) == S.empty && x /= z && xValid && zValid && validRecursiveBindings eta
    unless xValid $ Left (x ++ " is not valid.")
    unless zValid $ Left (z ++ " is not valid.")
    unless allValid $ Left "Invalid contexts or bindings in IdRule."
    return (Link x z, Sequent { tyVarContext = tv, fnContext = fc, unrestrictedContext = c, linearContext = Data.Map.singleton x p, recursiveBindings = eta, channel = z, goalProposition = p })
verifyProofM (FunctionalTermRightRule z p tv c eta) = do
    fConcl <- verifyFunctionalProofM p
    unless (L.null (L.intersect (ctxKeys (functionalContext fConcl)) (Data.Map.keys c)) && validRecursiveBindings eta) $ 
        Left "Invalid context in FunctionalTermRightRule"
    let seq = Sequent { tyVarContext = tv, fnContext = functionalContext fConcl, unrestrictedContext = c, linearContext = Data.Map.empty, recursiveBindings = eta, channel = z, goalProposition = Lift (goalType fConcl) }
    return (LiftTerm z (goalTerm fConcl), seq)
verifyProofM (FunctionalTermLeftRule x p) = do
    (process, seq) <- verifyProofM p
    xTy <- ctxEitherLookup x (fnContext seq)
    newFnContext <- ctxDelete x (fnContext seq)
    return (process, seq { fnContext = newFnContext, unrestrictedContext = unrestrictedContext seq, linearContext = Data.Map.insert x (Lift xTy) $ linearContext seq })
verifyProofM (UnitRightRule z tv fc uc eta) = do
    unless (validRecursiveBindings eta && L.null (ctxKeys fc `L.intersect` Data.Map.keys uc)) $ 
        Left "Invalid contexts or bindings in UnitRightRule"
    return (Halt, Sequent { tyVarContext = tv, fnContext = fc, unrestrictedContext = uc, linearContext = Data.Map.empty, recursiveBindings = eta, channel = z, goalProposition = Unit })
verifyProofM (UnitLeftRule x p) = do
    (process, seq) <- verifyProofM p
    unless (x `isFreshInProof` p) $ Left (x ++ " not fresh in UnitLeftRule.")
    return (process, seq { linearContext = Data.Map.insert x Unit $ linearContext seq })
verifyProofM (ReplicationRightRule z p) = do
    (process, seq) <- verifyProofM p
    unless (Data.Map.null (linearContext seq)) $ Left "Linear context is not empty in ReplicationRightRule."
    unless (z `isFreshInProof` p) $ Left (z ++ " not fresh in ReplicationRightRule.")
    return (ReplicateReceive z (channel seq) process, seq { channel = z, goalProposition = Replication $ goalProposition seq })
verifyProofM (ReplicationLeftRule u x p) = do
    (process, seq) <- verifyProofM p
    uProp <- eitherLookup u $ unrestrictedContext seq
    unless (x `isFreshInProof` p) $ Left (x ++ " not fresh in ReplicationLeftRule.")
    return (substVar process x u, seq { unrestrictedContext = Data.Map.delete u $ unrestrictedContext seq, linearContext = Data.Map.insert x (Replication uProp) $ linearContext seq })
verifyProofM (CopyRule u y p) = do
    (process, seq) <- verifyProofM p
    uProp <- eitherLookup u $ unrestrictedContext seq
    yProp <- eitherLookup y $ linearContext seq
    unless (uProp == yProp) $ Left "Type mismatch in CopyRule."
    return (Nu y yProp (Send u y process), seq { linearContext = Data.Map.delete y $ linearContext seq })
verifyProofM (WithRightRule p1 p2) = do
    (process1, seq1) <- verifyProofM p1
    (process2, seq2) <- verifyProofM p2
    let sameContexts = channel seq1 == channel seq2
            && fnContext seq1 == fnContext seq2
            && unrestrictedContext seq1 == unrestrictedContext seq2
            && linearContext seq1 == linearContext seq2
    unless sameContexts $ Left ("Sequents do not match: " ++ seqToS seq1 ++ " and " ++ seqToS seq2)
    return (Case (channel seq1) process1 process2, seq1 { goalProposition = With (goalProposition seq1) (goalProposition seq2) })
verifyProofM (WithLeft1Rule x newProp p) = do
    (process, seq) <- verifyProofM p
    xProp <- eitherLookup x $ linearContext seq
    return (SendInl x process, seq { linearContext = Data.Map.insert x (With xProp newProp) $ linearContext seq })
verifyProofM (WithLeft2Rule x newProp p) = do
    (process, seq) <- verifyProofM p
    xProp <- eitherLookup x $ linearContext seq
    return (SendInr x process, seq { linearContext = Data.Map.insert x (With newProp xProp) $ linearContext seq })
verifyProofM (ImpliesRightRule x p) = do
    (process, seq) <- verifyProofM p
    xProp <- eitherLookup x $ linearContext seq
    return (Receive (channel seq) x process, seq { linearContext = Data.Map.delete x $ linearContext seq, goalProposition = Implication xProp (goalProposition seq) })
verifyProofM (ImpliesLeftRule x p1 p2) = do
    (process1, seq1) <- verifyProofM p1
    (process2, seq2) <- verifyProofM p2
    xProp <- eitherLookup x $ linearContext seq2
    let disjointLinearContexts = Data.Map.null $ linearContext seq1 `Data.Map.intersection` linearContext seq2
        validUnrestrictedContexts = unrestrictedContext seq1 == unrestrictedContext seq2
        validFnContexts = fnContext seq1 == fnContext seq2
        rightGoalFresh = not (Data.Map.member (channel seq2) (linearContext seq1))
    unless disjointLinearContexts $ Left "Invalid linear contexts in ImpliesLeftRule."
    unless validUnrestrictedContexts $ Left "Invalid unrestricted contexts in ImpliesLeftRule."
    unless validFnContexts $ Left "Invalid functional contexts in ImpliesLeftRule."
    unless rightGoalFresh $ Left "Right goal not fresh in ImpliesLeftRule."
    let outSeq = seq2 { 
        linearContext = Data.Map.insert x (Implication (goalProposition seq1) xProp) (linearContext seq1 `Data.Map.union` linearContext seq2), 
        unrestrictedContext = unrestrictedContext seq1, 
        fnContext = fnContext seq1 
    }
    return (Nu (channel seq1) (goalProposition seq1) (Send x (channel seq1) (ParallelComposition process1 process2)), outSeq)
verifyProofM (TensorRightRule p1 p2) = do
    (process1, seq1) <- verifyProofM p1
    (process2, seq2) <- verifyProofM p2
    let validLinearContexts = Data.Map.null $ linearContext seq1 `Data.Map.intersection` linearContext seq2
        validUnrestrictedContexts = unrestrictedContext seq1 == unrestrictedContext seq2
        validFnContexts = fnContext seq1 == fnContext seq2
        z = channel seq2
        zInvalid = z `elem` (Data.Map.keys (linearContext seq1) ++ Data.Map.keys (unrestrictedContext seq1) ++ ctxKeys (fnContext seq1))
    unless (validLinearContexts && validUnrestrictedContexts && validFnContexts && not zInvalid) $ Left "Invalid contexts in TensorRightRule."
    let outSeq = seq2 { linearContext = linearContext seq1 `Data.Map.union` linearContext seq2, goalProposition = Tensor (goalProposition seq1) (goalProposition seq2) }
    return (Nu (channel seq1) (goalProposition seq1) (Send (channel seq2) (channel seq1) (ParallelComposition process1 process2)), outSeq)
verifyProofM (TensorLeftRule x y p) = do
    (process, seq) <- verifyProofM p
    xProp <- eitherLookup x $ linearContext seq
    yProp <- eitherLookup y $ linearContext seq
    return (Receive x y process, seq { linearContext = Data.Map.insert x (Tensor yProp xProp) $ Data.Map.delete y $ linearContext seq })
verifyProofM (PlusRight1Rule newProp p) = do
    (process, seq) <- verifyProofM p
    return (SendInl (channel seq) process, seq { goalProposition = Plus (goalProposition seq) newProp })
verifyProofM (PlusRight2Rule newProp p) = do
    (process, seq) <- verifyProofM p
    return (SendInr (channel seq) process, seq { goalProposition = Plus newProp (goalProposition seq) })
verifyProofM (PlusLeftRule x p1 p2) = do
    (process1, seq1) <- verifyProofM p1
    (process2, seq2) <- verifyProofM p2
    xProp1 <- eitherLookup x $ linearContext seq1
    xProp2 <- eitherLookup x $ linearContext seq2
    let validLinearContexts = Data.Map.delete x (linearContext seq1) == Data.Map.delete x (linearContext seq2)
        validUnrestrictedContexts = unrestrictedContext seq1 == unrestrictedContext seq2
        validFnContexts = fnContext seq1 == fnContext seq2
        validChannel = channel seq1 == channel seq2
        validGoal = goalProposition seq1 == goalProposition seq2
    unless (validLinearContexts && validUnrestrictedContexts && validFnContexts && validChannel && validGoal) $ Left "Context or goal mismatch in PlusLeftRule."
    return (Case x process1 process2, seq2 { linearContext = Data.Map.insert x (Plus xProp1 xProp2) $ linearContext seq2 })
verifyProofM (ForallRightRule x p) = do
    (process, seq) <- verifyProofM p
    xFnProp <- ctxEitherLookup x $ fnContext seq
    newFnContext <- ctxDelete x (fnContext seq)
    return (Receive (channel seq) x process, seq { fnContext = newFnContext, goalProposition = Forall x xFnProp (goalProposition seq) })
verifyProofM (ForallLeftRule x y p1 p2) = do
    fConcl <- verifyFunctionalProofM p1
    (process2, seq) <- verifyProofM p2
    xProp <- eitherLookup x $ linearContext seq
    let tau = goalType fConcl
        n = goalTerm fConcl
    return (SendTerm x n process2, seq { linearContext = Data.Map.insert x (Forall y tau (abstTerm xProp y n)) $ linearContext seq })
verifyProofM (ExistsRightRule x p1 p2) = do
    fConcl <- verifyFunctionalProofM p1
    (process2, seq) <- verifyProofM p2
    let tau = goalType fConcl
        n = goalTerm fConcl
        zProp = goalProposition seq
    return (SendTerm (channel seq) n process2, seq { goalProposition = Exists x tau $ abstTerm zProp x n })
verifyProofM (ExistsLeftRule x y p) = do
    (process, seq) <- verifyProofM p
    yProp <- ctxEitherLookup y $ fnContext seq
    xProp <- eitherLookup x $ linearContext seq
    newFnContext <- ctxDelete y $ fnContext seq
    return (Receive x y process, seq { fnContext = newFnContext, linearContext = Data.Map.insert x (Exists y yProp xProp) $ linearContext seq })
verifyProofM (ForallRight2Rule x p) = do
    (process, seq) <- verifyProofM p
    unless (S.member x (tyVarContext seq)) $ Left "x not found in tyVarContext."
    return (Receive (channel seq) x process, seq { tyVarContext = S.delete x $ tyVarContext seq, goalProposition = Forall2 x (goalProposition seq) })
verifyProofM (ForallLeft2Rule x y b p) = do
    (process, seq) <- verifyProofM p
    xProp <- eitherLookup x $ linearContext seq
    let eta = recursiveBindings seq
    wellFormedType (tyVarContext seq `S.union` S.fromList (bindingTyVar . snd . snd <$> Data.Map.toList eta)) b
    return (SendType x b process, seq { linearContext = Data.Map.insert x (Forall2 y (abstProp xProp y b)) $ linearContext seq })
verifyProofM (ExistsRight2Rule x b p) = do
    (process, seq) <- verifyProofM p
    let zProp = goalProposition seq
        eta = recursiveBindings seq
    wellFormedType (tyVarContext seq `S.union` S.fromList (bindingTyVar . snd . snd <$> Data.Map.toList eta)) b
    return (SendType (channel seq) b process, seq { goalProposition = Exists2 x (abstProp zProp x b) })
verifyProofM (ExistsLeft2Rule x y p) = do
    (process, seq) <- verifyProofM p
    xProp <- eitherLookup x $ linearContext seq
    unless (S.member y (tyVarContext seq)) $ Left "y not found in tyVarContext."
    return (Receive x y process, seq { tyVarContext = S.delete y $ tyVarContext seq, linearContext = Data.Map.insert x (Exists2 y xProp) $ linearContext seq })
verifyProofM (TyNuRightRule x zs p) = do
    (process, seq) <- verifyProofM p
    (ys, xBinding) <- eitherLookup x (recursiveBindings seq)
    let yzs = zip ys zs
        renamedBoundTyVarContext = L.foldl (\acc (y, z) -> substVarTyVarContext acc z y) (bindingTyVarContext xBinding) yzs
        renamedBoundFnContext = L.foldl (\acc (y, z) -> renameVarInFnCtx S.empty acc z y) (bindingFnContext xBinding) yzs
        renamedBoundUC = L.foldl (\acc (y, z) -> substVarContext acc z y) (bindingUC xBinding) yzs
        renamedBoundLC = L.foldl (\acc (y, z) -> substVarContext acc z y) (bindingLC xBinding) yzs
        renamedChan = L.foldl (\acc (y,z) -> if acc == y then z else acc) (bindingChan xBinding) yzs
    unless (L.length zs == L.length ys) $ Left "Mismatch number of args and params."
    unless (renamedBoundTyVarContext == tyVarContext seq) $ Left $ show renamedBoundTyVarContext ++ " is not equal to " ++ show (tyVarContext seq)
    unless (renamedBoundFnContext == fnContext seq) $ Left $ show renamedBoundFnContext ++ " is not equal to " ++ show (fnContext seq)
    unless (renamedBoundUC == unrestrictedContext seq) $ Left $ show renamedBoundUC ++ " is not equal to " ++ show (unrestrictedContext seq)
    unless (renamedBoundLC == linearContext seq) $ Left $ show renamedBoundLC ++ " is not equal to " ++ show (linearContext seq)
    unless (renamedChan == channel seq) $ Left $ renamedChan ++ " is not equal to " ++ channel seq
    let finalProc = Corec x ys (L.foldl (\newP (y, z) -> substVar newP y z) process yzs) zs
        finalSeq = seq { recursiveBindings = Data.Map.delete x $ recursiveBindings seq, goalProposition = TyNu (bindingTyVar xBinding) (goalProposition seq) }
    return (finalProc, finalSeq)
verifyProofM (TyNuLeftRule c x p) = do
    (process, seq) <- verifyProofM p
    cProp <- eitherLookup c $ linearContext seq
    let newCProp = TyNu x (foldUpRec x cProp)
    return (process, seq { linearContext = Data.Map.insert c newCProp $ linearContext seq })
verifyProofM (TyVarRule eta x zs) = do
    unless (validRecursiveBindings eta) $ Left "Invalid recursive bindings."
    (ys, xBinding) <- eitherLookup x eta
    unless (L.length ys == L.length zs) $ Left "Length mismatch in TyVarRule."
    let yzs = zip ys zs
        newTyVarBindingContext = bindingTyVarContext xBinding
        newFunctionalContext = L.foldl (\curMap (y,z) -> renameVarInFnCtx S.empty curMap z y) (bindingFnContext xBinding) yzs
        newUnrestrictedContext = L.foldl (\curMap (y,z) -> substVarContext curMap z y) (bindingUC xBinding) yzs
        newLinearContext = L.foldl (\curMap (y,z) -> substVarContext curMap z y) (bindingLC xBinding) yzs
        newChannel = L.foldl (\curVar (y, z) -> if y == curVar then z else curVar) (bindingChan xBinding) yzs
    return (Call x zs, Sequent { tyVarContext = newTyVarBindingContext, fnContext = newFunctionalContext, unrestrictedContext = newUnrestrictedContext, linearContext = newLinearContext, recursiveBindings = eta, channel = newChannel, goalProposition = TyVar (bindingTyVar xBinding) })
verifyProofM (CutRule p1 p2) = do
    (process1, seq1) <- verifyProofM p1
    (process2, seq2) <- verifyProofM p2
    let xProp1 = goalProposition seq1
    xProp2 <- eitherLookup (channel seq1) $ linearContext seq2
    let validLinearContexts = Data.Map.null $ linearContext seq1 `Data.Map.intersection` Data.Map.delete (channel seq1) (linearContext seq2)
        validUnrestrictedContexts = unrestrictedContext seq1 == unrestrictedContext seq2
        validFnContexts = fnContext seq1 == fnContext seq2
    unless (xProp1 == xProp2) $ Left $ "CutRule: Left side goal " ++ propToS xProp1 ++ " is not equal to prop in linear context " ++ propToS xProp2
    unless validLinearContexts $ Left $ "CutRule: Linear contexts are not disjoint. They share " ++ show (Data.Map.keys (linearContext seq1 `Data.Map.intersection` Data.Map.delete (channel seq1) (linearContext seq2)))
    unless validUnrestrictedContexts $ Left $ "CutRule: Unrestricted contexts are not equal: " ++ show (unrestrictedContext seq1) ++ " and " ++ show (unrestrictedContext seq2)
    unless validFnContexts $ Left $ "CutRule: Functional contexts are not equal: " ++ show (ctxToList (fnContext seq1)) ++ " and " ++ show (ctxToList (fnContext seq2))
    when (Data.Map.member (channel seq2) (linearContext seq1)) $ Left $ "CutRule: channel is a member of the other linear context: " ++ channel seq2 ++ " in " ++ show (linearContext seq1)
    let finalProc = Nu (channel seq1) (goalProposition seq1) $ ParallelComposition process1 process2
    return (finalProc, seq2 { linearContext = linearContext seq1 `Data.Map.union` Data.Map.delete (channel seq1) (linearContext seq2) })
verifyProofM (CutReplicationRule u p1 p2) = do
    (process1, seq1) <- verifyProofM p1
    (process2, seq2) <- verifyProofM p2
    let xProp = goalProposition seq1
    uProp <- eitherLookup u $ unrestrictedContext seq2
    let validUnrestrictedContexts = unrestrictedContext seq1 == Data.Map.delete u (unrestrictedContext seq2)
        validFnContexts = fnContext seq1 == fnContext seq2
    unless (xProp == uProp && Data.Map.null (linearContext seq1) && validUnrestrictedContexts && validFnContexts && not (Data.Map.member (channel seq2) (linearContext seq1))) $ 
        Left "CutReplicationRule validation failed."
    let finalProc = Nu u (goalProposition seq1) $ ParallelComposition (ReplicateReceive u (channel seq2) process1) process2
    return (finalProc, seq2 { unrestrictedContext = Data.Map.delete u $ unrestrictedContext seq2 })
verifyProofM (ReplWeakening u prop proof) = do
    (process, seq) <- verifyProofM proof
    unless (not $ Data.Map.member u $ unrestrictedContext seq) $ Left "u already in unrestrictedContext."
    return (process, seq { unrestrictedContext = Data.Map.insert u prop $ unrestrictedContext seq })
verifyProofM (FnWeakening a ft proof) = do
    (process, seq) <- verifyProofM proof
    unless (not $ ctxMember a $ fnContext seq) $ Left "a already in fnContext."
    newFnCtx <- safeInsert a ft $ fnContext seq
    return (process, seq { fnContext = newFnCtx })
verifyProofM (TyVarWeakening a proof) = do
    (process, seq) <- verifyProofM proof
    unless (not $ S.member a $ tyVarContext seq) $ Left "a already in tyVarContext."
    return (process, seq { tyVarContext = S.insert a $ tyVarContext seq })
verifyProofM (RecBindingWeakening a (ps, bs) proof) = do
    (process, seq) <- verifyProofM proof
    unless (not $ Data.Map.member a $ recursiveBindings seq) $ Left "a already in recursiveBindings."
    return (process, seq { recursiveBindings = Data.Map.insert a (ps, bs) $ recursiveBindings seq })
verifyProofM (HoleRule tv fc uc lc eta z p) = 
    return (HoleTerm, Sequent { tyVarContext = tv, fnContext = fc, unrestrictedContext = uc, linearContext = lc, recursiveBindings = eta, channel = z, goalProposition = p })
verifyProofM (ProcessFiatRule procName chanName prop p) = do
    (q, seq) <- verifyProofM p
    let finalProc = Nu chanName prop (ParallelComposition (Call procName [chanName]) q)
    return (finalProc, seq { linearContext = Data.Map.insert chanName prop (linearContext seq) })
{-|
>>> verifyProof (HoleRule Data.Map.empty Data.Map.empty Data.Map.empty "z" Unit)
False
-}
verifyProof :: Proof -> Bool
verifyProof p = case verifyProofM p of
    Right seq -> True
    _ -> False

extractFunctionalTerm :: FunctionalProof -> Maybe FunctionalTerm
extractFunctionalTerm t = case verifyFunctionalProofM t of
    Right seq -> return $ goalTerm seq
    _ -> Nothing

checkNamesMatch z1 z2 = when (z1 /= z2) $ Left $ "Expected matching channels do not match: " ++ z1 ++ ", " ++ z2

typeCheckProcessUnderSequent :: Sequent -> Process -> Either String Proof
typeCheckProcessUnderSequent seq process =
    let
        linearAssms = Data.Map.toList (linearContext seq)
        unitAssms = L.filter (\(k, v) -> v == Unit) linearAssms
        replAssms = L.filter (\(k, v) -> case v of Replication _ -> True; _ -> False) linearAssms
        liftAssms = L.filter (\(k, v) -> case v of Lift _ -> True; _ -> False) linearAssms
        tyNuAssms = L.filter (\(k, v) -> case v of TyNu{} -> True; _ -> False) linearAssms
        freshName = getFreshName $ getSequentNames seq `S.union` processNames process
        unitAttempt (k, v) = do
            case linearContext seq ! k of Unit -> return (); _ -> Left "Not a unit even though it was filtered!"
            proof <- typeCheckProcessUnderSequent (seq { linearContext = Data.Map.delete k (linearContext seq) }) process
            return $ UnitLeftRule k proof
        replAttempt (k, v) = do
            a <- case linearContext seq ! k of Replication a -> return a; _ -> Left "Not a replication even though it was filtered!"
            proof <- typeCheckProcessUnderSequent (seq{unrestrictedContext = Data.Map.insert freshName a (unrestrictedContext seq), linearContext = Data.Map.delete k (linearContext seq) }) (substVar process freshName k)
            return $ ReplicationLeftRule freshName k proof
        liftAttempt (k, v) = do
            a <- case linearContext seq ! k of Lift a -> return a; _ -> Left "Not a lift even though it was filtered!"
            newFnCtx <- safeInsert k a $ fnContext seq
            proof <- typeCheckProcessUnderSequent (seq{ fnContext = newFnCtx, linearContext = Data.Map.delete k (linearContext seq) }) process
            return $ FunctionalTermLeftRule k proof
        tyNuAttempt (k, v) = do
            (y, a) <- case linearContext seq ! k of TyNu y a -> return (y, a); _ -> Left "Not a lift even though it was filtered!"
            proof <- typeCheckProcessUnderSequent (seq{ linearContext = Data.Map.insert k (unfoldRec a y a) (linearContext seq) }) process
            return $ FunctionalTermLeftRule k proof
        unitAttempts = unitAttempt <$> unitAssms
        replAttempts = replAttempt <$> replAssms
        liftAttempts = liftAttempt <$> liftAssms
        tyNuAttempts = tyNuAttempt <$> tyNuAssms
        allAttempts = typeCheckProcessUnderSequentAtom seq process:(unitAttempts ++ replAttempts ++ liftAttempts ++ tyNuAttempts)
        successfulAttempt = L.take 1 . L.dropWhile (\a -> case a of Right p -> False; Left e -> True) $ allAttempts
    in
        case successfulAttempt of
            [] -> head allAttempts
            (a:_) -> a

{-|
    Must be checked after proof is derived.
    Pass functional context, unrestricted context, linear context, active channel name, and process.
-}
typeCheckProcessUnderSequentAtom :: Sequent -> Process -> Either String Proof
typeCheckProcessUnderSequentAtom seq process = case process of
    Link x z -> do
        when (z /= channel seq) $ Left $ "Identity fail: Process channel " ++ z ++ " does not match goal " ++ channel seq
        ty <- case Data.Map.lookup x (linearContext seq) of
            Just t -> return t
            Nothing -> Left $ "Identity fail: Variable " ++ x ++ " not found in linear context."
        unless (linearContext seq == Data.Map.singleton x ty) (Left ("Identity fail: Linear context has more than " ++ x ++ " see " ++ show (linearContext seq)))
        if ty == goalProposition seq
        then return $ IdRule x z (tyVarContext seq) (fnContext seq) (unrestrictedContext seq) (recursiveBindings seq) ty
        else Left $ "Identity fail: Type mismatch. Have " ++ propToS ty ++ ", want " ++ propToS (goalProposition seq)
    LiftTerm z m -> do
        unless (Data.Map.empty == linearContext seq) $ Left $ "Lift fail: Linear context should be empty: " ++ show (linearContext seq)
        (ty, mProof) <- extractProofFromTermUnderCtx (fnContext seq) m
        mConcl <- verifyFunctionalProofM mProof
        unless (goalProposition seq == Lift (goalType mConcl)) $ Left $ "Lift fail: Expected type is not correct " ++ propToS (goalProposition seq) ++ " " ++ (propToS (Lift (goalType mConcl)))
        return $ FunctionalTermRightRule z mProof (tyVarContext seq) (unrestrictedContext seq) (recursiveBindings seq)
    Halt -> do
        unless (Data.Map.empty == linearContext seq) $ Left $ "Halt fail: Linear context should be empty: " ++ show (linearContext seq)
        unless (goalProposition seq == Unit) $ Left $ "Halt fail: Expected type is not Unit " ++ propToS (goalProposition seq)
        return $ UnitRightRule (channel seq) (tyVarContext seq) (fnContext seq) (unrestrictedContext seq) (recursiveBindings seq)
    ReplicateReceive z y p -> do
        unless (z == channel seq) $ Left $ "Replicate receive fail: Channel does not match " ++ z ++ " vs. " ++ channel seq
        unless (Data.Map.empty == linearContext seq) $ Left $ "Replicate receive fail: Linear context is not empty " ++ show (linearContext seq)
        nextTy <- case goalProposition seq of
            Replication p -> return p
            _ -> Left $ "Replicate receive fail: Proposition is not replication " ++ propToS (goalProposition seq)
        pTy <- typeCheckProcessUnderSequent (seq { channel = y, goalProposition = nextTy }) p
        return $ ReplicationRightRule z pTy
    Nu y1 ty (Send u y2 p) | y1 == y2 && Data.Map.member u (unrestrictedContext seq) -> do
        let uTy = unrestrictedContext seq ! u
        unless (uTy == ty) $ Left $ "Copy fail: Expected type is not the type in context: " ++ propToS ty ++ " " ++ propToS uTy
        pTy <- typeCheckProcessUnderSequent (seq { linearContext = Data.Map.insert y1 ty (linearContext seq) }) p
        return $ CopyRule u y1 pTy
    Case z p q | z == channel seq -> do
        (a, b) <- case goalProposition seq of With a b -> return (a, b); _ -> Left $ "Case fail: not a With prop: " ++ propToS (goalProposition seq)
        leftProof <- typeCheckProcessUnderSequent (seq { goalProposition = a }) p
        rightProof <- typeCheckProcessUnderSequent (seq { goalProposition = b }) q
        return $ WithRightRule leftProof rightProof
    Case x p q | Data.Map.member x (linearContext seq) -> do
        (a, b) <- case linearContext seq ! x of With a b -> return (a, b); _ -> Left $ "Case fail: not a With prop: " ++ propToS (goalProposition seq)
        leftProof <- typeCheckProcessUnderSequent (seq { linearContext = Data.Map.insert x a (linearContext seq) }) p
        rightProof <- typeCheckProcessUnderSequent (seq { linearContext = Data.Map.insert x b (linearContext seq) }) q
        return $ PlusLeftRule x leftProof rightProof
    SendInl z p | z == channel seq -> do
        (a, b) <- case goalProposition seq of Plus a b -> return (a, b); _ -> Left $ "SendInl fail: not a Plus prop: " ++ propToS (goalProposition seq)
        proof <- typeCheckProcessUnderSequent (seq { goalProposition = a }) p
        return $ PlusRight1Rule b proof
    SendInr z p | z == channel seq -> do
        (a, b) <- case goalProposition seq of Plus a b -> return (a, b); _ -> Left $ "SendInr fail: not a Plus prop: " ++ propToS (goalProposition seq)
        proof <- typeCheckProcessUnderSequent (seq { goalProposition = b }) p
        return $ PlusRight2Rule a proof
    SendInl x p | Data.Map.member x (linearContext seq) -> do
        (a, b) <- case linearContext seq ! x of With a b -> return (a, b); _ -> Left $ "SendInl fail: not a With prop: " ++ propToS (linearContext seq ! x)
        proof <- typeCheckProcessUnderSequent (seq { linearContext = Data.Map.insert x a (linearContext seq) }) p
        return $ WithLeft1Rule x b proof
    SendInr x p | Data.Map.member x (linearContext seq) -> do
        (a, b) <- case linearContext seq ! x of With a b -> return (a, b); _ -> Left $ "SendInr fail: not a With prop: " ++ propToS (linearContext seq ! x)
        proof <- typeCheckProcessUnderSequent (seq { linearContext = Data.Map.insert x b (linearContext seq) }) p
        return $ WithLeft2Rule x a proof
    Nu y1 ty (Send z y2 (ParallelComposition p q)) | y1 == y2 && z == channel seq -> do
        (a, b) <- case goalProposition seq of Tensor a b -> return (a, b); _ -> Left $ "Tensor fail: not a Tensor prop: " ++ propToS (goalProposition seq)
        let freeLeftVars = processFreeNames p
            leftLCtx = Data.Map.filterWithKey (\k v -> S.member k freeLeftVars) (linearContext seq)
            rightLCtx = Data.Map.difference (linearContext seq) leftLCtx
        proof1 <- typeCheckProcessUnderSequent (seq { linearContext = leftLCtx, channel = y1, goalProposition = a }) p
        proof2 <- typeCheckProcessUnderSequent (seq { linearContext = rightLCtx, channel = z, goalProposition = b }) q
        return $ TensorRightRule proof1 proof2
    Nu y1 ty (Send x y2 (ParallelComposition p q)) | y1 == y2 && Data.Map.member x (linearContext seq) -> do
        (a, b) <- case linearContext seq ! x of Implication a b -> return (a, b); _ -> Left $ "Implication fail: not an Implication prop: " ++ propToS (linearContext seq ! x)
        let freeLeftVars = processFreeNames p
            leftLCtx = Data.Map.delete y1 $ Data.Map.filterWithKey (\k v -> S.member k freeLeftVars) (linearContext seq)
            rightLCtx = Data.Map.insert x b $ Data.Map.difference (linearContext seq) leftLCtx
        proof1 <- typeCheckProcessUnderSequent (seq { linearContext = leftLCtx, channel = y1, goalProposition = a }) p
        proof2 <- typeCheckProcessUnderSequent (seq { linearContext = rightLCtx }) q
        return $ ImpliesLeftRule x proof1 proof2
    Receive z x p | z == channel seq -> case goalProposition seq of
        Implication a b -> do
            proof <- typeCheckProcessUnderSequent (seq { linearContext = Data.Map.insert x a (linearContext seq), goalProposition = b }) p
            return $ ImpliesRightRule x proof
        Forall x2 t a | x == x2 -> do
            newFnCtx <- safeInsert x t $ fnContext seq
            proof <- typeCheckProcessUnderSequent (seq { fnContext = newFnCtx, goalProposition = a }) p
            return $ ForallRightRule x proof
        Forall2 x2 a | x == x2 -> do
            proof <- typeCheckProcessUnderSequent (seq { tyVarContext = S.insert x (tyVarContext seq), goalProposition = a }) p
            return $ ForallRight2Rule x proof
        e -> Left $ "Receive fail: not a valid type " ++ propToS e
    Receive x y1 p | Data.Map.member x (linearContext seq) -> case linearContext seq ! x of
        Tensor a b -> do
            proof <- typeCheckProcessUnderSequent (seq { linearContext = Data.Map.insert y1 a $ Data.Map.insert x b (linearContext seq) }) p
            return $ TensorLeftRule x y1 proof
        Exists y2 t a | y1 == y2 -> do
            newFnCtx <- safeInsert y1 t $ fnContext seq
            proof <- typeCheckProcessUnderSequent (seq { fnContext = newFnCtx, linearContext = Data.Map.insert x a $ (linearContext seq) }) p
            return $ ExistsLeftRule x y1 proof
        Exists2 y2 a | y1 == y2 -> do
            proof <- typeCheckProcessUnderSequent (seq { tyVarContext = S.insert y1 (tyVarContext seq), linearContext = Data.Map.insert x a (linearContext seq)}) p
            return $ ExistsLeft2Rule x y1 proof
        e -> Left $ "Receive fail: not a valid type in linear context " ++ propToS e
    SendTerm z n p | z == channel seq -> do
        (x, t, a) <- case goalProposition seq of Exists x t a -> return (x, t, a); e -> Left $ "SendTerm error: Not an Exists proposition: " ++ propToS e
        (tyExt, proof1) <- extractProofFromTermUnderCtx (fnContext seq) n
        proof1Concl <- verifyFunctionalProofM proof1
        unless (t == goalType proof1Concl) $ Left $ "Expected type does not match derived type: " ++ ftToS (goalType proof1Concl) ++ " and " ++ ftToS t
        proof2 <- typeCheckProcessUnderSequent (seq { goalProposition = substVarTerm a n x}) p
        return $ ExistsRightRule x proof1 proof2
    SendTerm x n p | Data.Map.member x (linearContext seq) -> do
        (y, t, a) <- case linearContext seq ! x of Forall y t a -> return (y, t, a); e -> Left $ "SendTerm error: Not a Forall proposition: " ++ propToS e
        (tyExt, proof1) <- extractProofFromTermUnderCtx (fnContext seq) n
        proof1Concl <- verifyFunctionalProofM proof1
        unless (t == goalType proof1Concl) $ Left $ "Expected type does not match derived type: " ++ ftToS (goalType proof1Concl) ++ " and " ++ ftToS t
        proof2 <- typeCheckProcessUnderSequent (seq {linearContext = Data.Map.insert x (substVarTerm a n y) (linearContext seq)}) p
        return $ ForallLeftRule x y proof1 proof2
    SendType z n p | z == channel seq -> do
        (x, a) <- case goalProposition seq of Exists2 x a -> return (x, a); e -> Left $ "SendTerm error: Not an Exists proposition: " ++ propToS e
        wellFormedType (tyVarContext seq `S.union` S.fromList ((\v -> bindingTyVar v) . snd . snd <$> Data.Map.toList (recursiveBindings seq))) n
        proof <- typeCheckProcessUnderSequent (seq { goalProposition = substVarType a n x}) p
        return $ ExistsRight2Rule x n proof
    SendType x n p | Data.Map.member x (linearContext seq) -> do
        (y, a) <- case linearContext seq ! x of Forall2 y a -> return (y, a); e -> Left $ "SendTerm error: Not a Forall proposition: " ++ propToS e
        wellFormedType (tyVarContext seq `S.union` S.fromList ((\v -> bindingTyVar v) . snd . snd <$> Data.Map.toList (recursiveBindings seq))) n
        proof <- typeCheckProcessUnderSequent (seq { linearContext = Data.Map.insert x (substVarType a n y) (linearContext seq) }) p
        return $ ForallLeft2Rule x y n proof
    Nu u1 a (ParallelComposition (ReplicateReceive u2 x p) q) | u1 == u2 -> do
        let freeLeftVars = processFreeNames p
            leftLCtx = Data.Map.empty
        proof1 <- typeCheckProcessUnderSequent (seq { linearContext = leftLCtx, goalProposition = a, channel = x }) p
        proof2 <- typeCheckProcessUnderSequent (seq { unrestrictedContext = Data.Map.insert u1 a (unrestrictedContext seq) }) q
        return $ CutRule proof1 proof2
    Nu x a (ParallelComposition p q) -> do
        let freeLeftVars = processFreeNames p
            leftLCtx = Data.Map.delete x $ Data.Map.filterWithKey (\k v -> S.member k freeLeftVars) (linearContext seq)
            rightLCtx = Data.Map.insert x a $ Data.Map.difference (linearContext seq) leftLCtx
        proof1 <- typeCheckProcessUnderSequent (seq { linearContext = leftLCtx, goalProposition = a, channel = x }) p
        proof2 <- typeCheckProcessUnderSequent (seq { linearContext = rightLCtx }) q
        return $ CutRule proof1 proof2
    Corec x ys p zs -> do
        (y, a) <- case goalProposition seq of TyNu y a -> return (y, a); e -> Left $ "Corec error: not a TyNu proposition: " ++ propToS e
        let yzs = zip ys zs
            newTyVarCtx = L.foldl (\acc (y, z) -> substVarTyVarContext acc y z) (tyVarContext seq) yzs
            newFnCtx = L.foldl (\acc (y, z) -> renameVarInFnCtx S.empty acc y z) (fnContext seq) yzs
            newUC = L.foldl (\acc (y, z) -> substVarContext acc y z) (unrestrictedContext seq) yzs
            newLC = L.foldl (\acc (y, z) -> substVarContext acc y z) (linearContext seq) yzs
            newChan = L.foldl (\acc (y, z) -> if acc == z then y else acc) (channel seq) yzs
            bindingSeq = BindingSequent { bindingTyVarContext = newTyVarCtx, bindingFnContext = newFnCtx, bindingUC = newUC, bindingLC = newLC, bindingChan = newChan, bindingTyVar = y }
            bodyProc = L.foldl (\acc (y, z) -> substVar acc z y) p yzs
        proof <- typeCheckProcessUnderSequent (seq { recursiveBindings = Data.Map.insert x (ys, bindingSeq) (recursiveBindings seq), goalProposition = a }) bodyProc
        return $ TyNuRightRule x zs proof
    Call x zs | Data.Map.member x (recursiveBindings seq) -> do
        y <- case goalProposition seq of TyVar y -> return y; e -> Left $ "Call error: not a TyVar proposition: " ++ propToS e
        let (ys, xSeq) = recursiveBindings seq ! x
        when (L.length zs /= L.length ys) (Left "Invalid number of arguments")
        let yzs = zip ys zs
            boundSeqRenamedTyVarContext = L.foldl (\acc (y, z) -> substVarTyVarContext acc z y) (bindingTyVarContext xSeq) yzs
            boundSeqRenamedFnContext = L.foldl (\acc (y, z) -> renameVarInFnCtx S.empty acc z y) (bindingFnContext xSeq) yzs
            boundSeqRenamedUCContext = L.foldl (\acc (y, z) -> substVarContext acc z y) (bindingUC xSeq) yzs
            boundSeqRenamedLCContext = L.foldl (\acc (y, z) -> substVarContext acc z y) (bindingLC xSeq) yzs
            boundSeqRenamedChannel = L.foldl (\curVar (y, z) -> if curVar == y then z else curVar) (bindingChan xSeq) yzs
        when (boundSeqRenamedTyVarContext /= tyVarContext seq) $ Left "Invalid tyvar contexts."
        when (boundSeqRenamedFnContext /= fnContext seq) $ Left "Invalid functional contexts."
        when (boundSeqRenamedUCContext /= unrestrictedContext seq) $ Left "Invalid unrestricted contexts."
        when (boundSeqRenamedLCContext /= linearContext seq) $ Left ("Invalid linear contexts:\n" ++ show boundSeqRenamedLCContext ++ "\n\n" ++ show (linearContext seq))
        when (boundSeqRenamedChannel /= channel seq) $ Left "Invalid channel."
        return $ TyVarRule (recursiveBindings seq) x zs
    e -> Left $ "Cannot determine how to type check: " ++ pToS e
        -- when (z /= channel seq) $ Left $ "Identity fail: Process channel " ++ z ++ " does not match goal " ++ channel seq
