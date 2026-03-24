module ECC.Kernel (FunctionalSequent(functionalContext,goalType,goalTerm)
    , FunctionalContext
    , FunctionalTerm(..)
    , FunctionalProof(..)
    , ftToS
    , ctxToList
    , functionalNames
    , getFunctionalContextNames
    , emptyContext
    , ctxLookup
    , ctxEitherLookup
    , ctxMember
    , ctxKeys
    , ctxDelete
    , extractProofFromTermUnderCtx
    , safeInsert
    , functionalFreeVariables
    , alphaConvert
    , functionalSubst
    , cumulativiyRelation
    , allConversionSteps
    , verifyFunctionalProofM
    , abstTermFunctional
    , functionalRename
    , getFunctionalProofNames
    , substVarFunctional
    , foldFunctionalProof
    , getFunctionalContextFreeNames
    , renameVarInFnCtx
    , renameVarInProof) where

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import Utils.Misc
import Data.Maybe (fromMaybe)
import Control.Monad (when, unless)

data FunctionalTerm = Type Integer
    | Prop
    | Var String
    | App FunctionalTerm FunctionalTerm
    | Lambda String FunctionalTerm FunctionalTerm
    | Pi String FunctionalTerm FunctionalTerm
    | Sigma String FunctionalTerm FunctionalTerm
    | Pair FunctionalTerm FunctionalTerm String FunctionalTerm FunctionalTerm -- (M,N):(Sigma x:A.B)
    | Proj1 FunctionalTerm
    | Proj2 FunctionalTerm
    | FHoleTerm
    deriving (Eq, Show, Read, Ord)

ftToS :: FunctionalTerm -> String
ftToS (Type i) = "Type " ++ show i
ftToS Prop = "Prop"
ftToS (Var x) = x
ftToS (App t1 t2) = "(" ++ ftToS t1 ++ " " ++ ftToS t2 ++ ")"
ftToS (Lambda x ty body) =
    "(\\" ++ x ++ " : " ++ ftToS ty ++ ". " ++ ftToS body ++ ")"
ftToS (Pi x ty body) =
    "[" ++ x ++ " : " ++ ftToS ty ++ ". " ++ ftToS body ++ "]"
ftToS FHoleTerm = "_"
ftToS (Sigma x t1 t2) = "(" ++ x ++ ":" ++ ftToS t1 ++ ") * " ++ ftToS t2
ftToS (Pair t1 t2 x ty1 ty2) = "(" ++ ftToS t1 ++ ", " ++ ftToS t2 ++ "):" ++ ftToS (Sigma x ty1 ty2)
ftToS (Proj1 t) = "proj1 " ++ ftToS t
ftToS (Proj2 t) = "proj2 " ++ ftToS t

{-| Get free variables in a term.

>>> functionalFreeVariables (App (App (Lambda "z" T (Var "z")) (Var "z")) (Lambda "x" (Var "A") (App (Var "y") (Pi "w" (Var "B") (Var "x"))))) 
fromList ["A","B","y","z"]
-}
functionalFreeVariables :: FunctionalTerm -> S.Set String
functionalFreeVariables (Type _) = S.empty
functionalFreeVariables Prop = S.empty
functionalFreeVariables (Var x) = S.singleton x
functionalFreeVariables (App t1 t2) = functionalFreeVariables t1 `S.union` functionalFreeVariables t2
functionalFreeVariables (Lambda x t1 t2) = functionalFreeVariables t1 `S.union` S.delete x (functionalFreeVariables t2) -- https://www.cs.yale.edu/flint/cs428/coq/doc/Reference-Manual006.html
functionalFreeVariables (Pi x t1 t2) = functionalFreeVariables t1 `S.union` S.delete x (functionalFreeVariables t2)
functionalFreeVariables (Sigma x t1 t2) = functionalFreeVariables t1 `S.union` S.delete x (functionalFreeVariables t2)
functionalFreeVariables (Pair t1 t2 x ty1 ty2) = functionalFreeVariables t1 `S.union` functionalFreeVariables t2 `S.union` functionalFreeVariables ty1 `S.union` S.delete x (functionalFreeVariables ty2)
functionalFreeVariables (Proj1 t) = functionalFreeVariables t
functionalFreeVariables (Proj2 t) = functionalFreeVariables t
functionalFreeVariables FHoleTerm = S.empty

{-| Get all names in a term bound and free. 

>>> functionalNames (Lambda "x" (Var "A") (App (Var "y") (Pi "w" (Var "B") (Var "x")))) 
fromList ["A","B","w","x","y"]
-}
functionalNames :: FunctionalTerm ->  S.Set String
functionalNames (Type _) = S.empty
functionalNames Prop = S.empty
functionalNames (Var x) = S.singleton x
functionalNames (App t1 t2) = functionalNames t1 `S.union` functionalNames t2
functionalNames (Lambda x t1 t2) = S.singleton x `S.union` functionalNames t1 `S.union` functionalNames t2 -- https://www.cs.yale.edu/flint/cs428/coq/doc/Reference-Manual006.html
functionalNames (Pi x t1 t2) = S.singleton x `S.union` functionalNames t1 `S.union` functionalNames t2
functionalNames (Sigma x t1 t2) = functionalNames t1 `S.union` functionalNames t2
functionalNames (Pair t1 t2 x ty1 ty2) = functionalNames t1 `S.union` functionalNames t2 `S.union` functionalNames ty1 `S.union` functionalNames ty2
functionalNames (Proj1 t) = functionalNames t
functionalNames (Proj2 t) = functionalNames t
functionalNames FHoleTerm = S.empty

{-| t{r/x} replace x with r in t. This is a naive replacement and not capture
avoiding. 

>>> functionalRename (Lambda "y" (Var "A") (Var "y")) "x" "y"
Lambda "x" (Var "A") (Var "x")

>>> functionalRename (Lambda "y" (Var "A") (Var "y")) "r" "x"
Lambda "y" (Var "A") (Var "y")
-}
functionalRename :: FunctionalTerm -> String -> String -> FunctionalTerm
functionalRename (Type i) r x = Type i
functionalRename Prop r x = Prop
functionalRename (Var y) r x = if x == y then Var r else Var y
functionalRename (App t1 t2) r x = App (functionalRename t1 r x) (functionalRename t2 r x)
functionalRename (Lambda y t1 t2) r x = if x == y then Lambda r (functionalRename t1 r x) (functionalRename t2 r x) else Lambda y (functionalRename t1 r x) (functionalRename t2 r x)
functionalRename (Pi y t1 t2) r x = if x == y then Pi r (functionalRename t1 r x) (functionalRename t2 r x) else Pi y (functionalRename t1 r x) (functionalRename t2 r x)
functionalRename (Sigma y t1 t2) r x = if x == y then Sigma r (functionalRename t1 r x) (functionalRename t2 r x) else Sigma y (functionalRename t1 r x) (functionalRename t2 r x)
functionalRename (Pair t1 t2 y ty1 ty2) r x = if x == y then Pair (functionalRename t1 r x) (functionalRename t2 r x) r (functionalRename ty1 r x) (functionalRename ty2 r x) else Pair (functionalRename t1 r x) (functionalRename t2 r x) y (functionalRename ty1 r x) (functionalRename ty2 r x)
functionalRename (Proj1 t) r x = Proj1 $ functionalRename t r x
functionalRename (Proj2 t) r x = Proj2 $ functionalRename t r x

{-| Convert a binding term to bind a fresh variable. Only works on lambda and pi
terms.

>>> alphaConvert (Lambda "y" (Var "A") (Var "y")) S.empty
Lambda "a" (Var "A") (Var "a")

>>> alphaConvert (Lambda "y" (Var "A") (Var "y")) (S.singleton "a")
Lambda "b" (Var "A") (Var "b")

>>> alphaConvert (Lambda "y" (Var "y") (Var "y")) (S.singleton "a")
Lambda "b" (Var "y") (Var "b")
-}
alphaConvert :: FunctionalTerm -> S.Set String -> FunctionalTerm
alphaConvert (Lambda x t1 t2) names =
    let
        z = getFreshName names
    in
        Lambda z t1 (functionalRename t2 z x)
alphaConvert (Pi x t1 t2) names =
    let
        z = getFreshName names
    in
        Pi z t1 (functionalRename t2 z x)
alphaConvert (Sigma x t1 t2) names =
    let
        z = getFreshName names
    in
        Sigma z t1 (functionalRename t2 z x)
alphaConvert (Pair t1 t2 x ty1 ty2) names =
    let
        z = getFreshName names
    in
        Pair t1 t2 z ty1 (functionalRename t2 z x)
alphaConvert t names = t

{-| B{N/x} replace x with n in b . Avoids capturing.

>>> functionalSubst (Var "x") (Var "y") "x"
y

>>> functionalSubst (App (Lambda ("x") (Var "y") (Var "x")) (Var "x")) (Var "z") "x"
((\x : y. x) z)

>>> functionalSubst (App (Pi ("x") (Var "y") (Var "x")) (Var "x")) (Var "z") "x"
([x : y. x] z)

>>> functionalSubst (Lambda "y" Prop (App (Var "x") (Var "y"))) (Var "y") "x"
(\a : Prop. (y a))

>>> functionalSubst (Sigma "x" (Var "x") (Var "x")) (Var "A") "x"
(x:A) * x

>>> functionalSubst (Pair (Var "x") (Var "x") "x" (Var "x") (Var "x")) (Var "A") "x"
(A, A):(x:A) * x

>>> functionalSubst (Proj1 (Var "x")) (Var "A") "x"
proj1 A

>>> functionalSubst (Proj2 (Var "x")) (Var "A") "x"
proj2 A
-}
functionalSubst :: FunctionalTerm -> FunctionalTerm -> String -> FunctionalTerm
functionalSubst b n x =
    let
        allNamesConsidered = (S.singleton x `S.union` functionalNames n `S.union` functionalNames b)
    in
        case b of
            (Type i) -> Type i
            Prop -> Prop
            FHoleTerm -> FHoleTerm
            Var y -> if y == x then n else Var y
            App t1 t2 -> App (functionalSubst t1 n x) (functionalSubst t2 n x)
            Lambda y t1 t2 -> if y == x
                then Lambda y (functionalSubst t1 n x) t2 -- y is not bound in t1.
                else if y `S.member` functionalFreeVariables n
                    then functionalSubst (alphaConvert b allNamesConsidered) n x
                    else Lambda y (functionalSubst t1 n x) (functionalSubst t2 n x)
            Pi y t1 t2 -> if y == x
                then Pi y (functionalSubst t1 n x) t2 -- y is not bound in t1.
                else if y `S.member` functionalFreeVariables n
                    then functionalSubst (alphaConvert b allNamesConsidered) n x
                    else Pi y (functionalSubst t1 n x) (functionalSubst t2 n x)
            Sigma y t1 t2 -> if y == x
                then Sigma y (functionalSubst t1 n x) t2 -- y is not bound in t1.
                else if y `S.member` functionalFreeVariables n
                    then functionalSubst (alphaConvert b allNamesConsidered) n x
                    else Sigma y (functionalSubst t1 n x) (functionalSubst t2 n x)
            Pair t1 t2 y ty1 ty2 -> if y == x
                then Pair (functionalSubst t1 n x) (functionalSubst t2 n x) y (functionalSubst ty1 n x) ty2 -- y is not bound in t1.
                else if y `S.member` functionalFreeVariables n
                    then functionalSubst (alphaConvert b allNamesConsidered) n x
                    else Pair (functionalSubst t1 n x) (functionalSubst t2 n x) y (functionalSubst ty1 n x) (functionalSubst ty2 n x)
            Proj1 t -> Proj1 (functionalSubst t n x)
            Proj2 t -> Proj2 (functionalSubst t n x)

data SafeCtx
data UnsafeCtx

{-| Make it so the TaggedFunctionalContext can only be constructed in a well-formed manner. -}
newtype TaggedFunctionalContext a = TaggedFunctionalContext { judgments::[(String, FunctionalTerm)] }
    deriving (Show, Eq, Ord, Read)

type FunctionalContext = TaggedFunctionalContext SafeCtx

fcToS :: TaggedFunctionalContext a -> String
fcToS (TaggedFunctionalContext j) = L.intercalate "," ((\(k,t) -> k ++ ":" ++ ftToS t) <$> j)

ctxDrop1 :: TaggedFunctionalContext a -> TaggedFunctionalContext a
ctxDrop1 (TaggedFunctionalContext c) = TaggedFunctionalContext { judgments = drop 1 c }

ctxTake1 :: TaggedFunctionalContext a -> [(String, FunctionalTerm)]
ctxTake1 (TaggedFunctionalContext c) = take 1 c

ctxToList :: TaggedFunctionalContext a -> [(String, FunctionalTerm)]
ctxToList (TaggedFunctionalContext c) = c

emptyContext :: TaggedFunctionalContext SafeCtx
emptyContext = TaggedFunctionalContext { judgments = [] }

unsafeInsert :: String -> FunctionalTerm -> TaggedFunctionalContext a -> TaggedFunctionalContext UnsafeCtx
unsafeInsert x t c = c { judgments= (x,t):judgments c }

ctxLookup :: String -> TaggedFunctionalContext a -> Maybe FunctionalTerm
ctxLookup x (TaggedFunctionalContext []) = Nothing
ctxLookup x (TaggedFunctionalContext ((h,t):rest)) | x == h = return t
ctxLookup x (TaggedFunctionalContext ((h,t):rest))  = ctxLookup x (TaggedFunctionalContext { judgments = rest })

ctxMember :: String -> TaggedFunctionalContext a -> Bool
ctxMember x ctx = case ctxLookup x ctx of Just _ -> True; Nothing -> False

ctxKeys :: TaggedFunctionalContext a -> [String]
ctxKeys ctx = fst <$> judgments ctx

ctxEitherLookup :: String -> TaggedFunctionalContext a -> Either String FunctionalTerm
ctxEitherLookup x c = case ctxLookup x c of
    Just res -> Right res
    Nothing -> Left $ "Could not find " ++ show x ++ " in " ++ fcToS c

getFunctionalContextNames :: TaggedFunctionalContext a -> S.Set String
getFunctionalContextNames c = S.fromList (fst <$> judgments c) `S.union` S.unions (functionalNames . snd <$> judgments c)

getFunctionalContextFreeNames :: TaggedFunctionalContext a -> S.Set String
getFunctionalContextFreeNames c = S.fromList (fst <$> judgments c) `S.union` S.unions (functionalFreeVariables . snd <$> judgments c)

ctxDelete :: String -> FunctionalContext -> Either String FunctionalContext
ctxDelete x ctx = 
    let
        beforeXJudgments = L.takeWhile (\(k,v) -> k /= x) $ judgments ctx
        afterXJudgments = L.drop 1 $ L.dropWhile (\(k,v) -> k /= x) $ judgments ctx
        freeVarsBeforeX = S.unions $ (\(k, v) -> functionalFreeVariables v) <$> beforeXJudgments
        newCtx = TaggedFunctionalContext $ beforeXJudgments ++ afterXJudgments
    in
        if x `S.member` freeVarsBeforeX then Left ("Judgments depend on " ++ x) else return newCtx

data FunctionalSequent = FunctionalSequent {
    functionalContext :: TaggedFunctionalContext SafeCtx,
    goalTerm :: FunctionalTerm,
    goalType :: FunctionalTerm
} deriving (Show, Eq, Ord, Read)

getFunctionalSequentNames :: FunctionalSequent -> S.Set String
getFunctionalSequentNames (FunctionalSequent fc gt gTy) = functionalNames gTy `S.union` functionalNames gt `S.union` getFunctionalContextNames fc

{-|
    The proof rules and validation here differ slightly from the original
    presentation of Luo's ECC. We aim to avoid verifying the validity of the
    context multiple times. The phantom type TaggedFunctionalContext SafeCtx indicates a valid context.
    
    -----------------
    G, x:A, G' |- x:A

    G|-A:K     G,x:A|-B:L
    ----------------- K,L are kinds.
    G|-Pi x:A.B : if L == Prop then Prop else max (Type 0, K, L)
-}
data FunctionalProof = CRule (TaggedFunctionalContext SafeCtx) -- \vdash Prop:Type_0
    | TRule Integer (TaggedFunctionalContext SafeCtx) -- \vdash Type_i : Type_(i+1)
    | VarRule String (TaggedFunctionalContext SafeCtx)
    | Pi1Rule String FunctionalProof
    | Pi2Rule String FunctionalProof FunctionalProof
    | LambdaRule String FunctionalProof
    | AppRule FunctionalProof FunctionalProof
    | SigmaRule String FunctionalProof FunctionalProof
    | PairRule String FunctionalProof FunctionalProof FunctionalProof
    | Proj1Rule FunctionalProof
    | Proj2Rule FunctionalProof
    | CumulativiyRule FunctionalProof FunctionalProof
    deriving (Eq, Show, Read)

subFunctionalProofs :: FunctionalProof -> [FunctionalProof]
subFunctionalProofs rule = case rule of
    Pi1Rule _ fp1               -> [fp1]
    Pi2Rule _ fp1 fp2           -> [fp1, fp2]
    SigmaRule _ fp1 fp2         -> [fp1, fp2]
    PairRule _ fp1 fp2 fp3      -> [fp1, fp2, fp3]
    CumulativiyRule fp1 fp2     -> [fp1, fp2]
    CRule{}                     -> []
    TRule{}                     -> []
    VarRule{}                   -> []
    LambdaRule _ fp             -> [fp]
    AppRule fp1 fp2             -> [fp1, fp2]
    Proj1Rule fp                -> [fp]
    Proj2Rule fp                -> [fp]

foldFunctionalProof :: ([a] -> a) -> FunctionalProof -> a
foldFunctionalProof fFunc rule = fFunc (map (foldFunctionalProof fFunc) (subFunctionalProofs rule))

functionalProofSize :: FunctionalProof -> Integer
functionalProofSize = foldFunctionalProof (\results -> 1 + sum results)

functionalProofDepth :: FunctionalProof -> Integer
functionalProofDepth = foldFunctionalProof (\results -> 1 + maximum (0 : results))

{-| Get all names used in a proof derivation. -}
getFunctionalProofNames :: FunctionalProof -> S.Set String
getFunctionalProofNames (CRule ctx) = getFunctionalContextNames ctx
getFunctionalProofNames (TRule i ctx) = getFunctionalContextNames ctx
getFunctionalProofNames (VarRule x ctx) = S.singleton x `S.union` getFunctionalContextNames ctx
getFunctionalProofNames (Pi1Rule x p) = S.singleton x `S.union` getFunctionalProofNames p
getFunctionalProofNames (Pi2Rule x p1 p2) = S.singleton x `S.union` getFunctionalProofNames p1 `S.union` getFunctionalProofNames p2
getFunctionalProofNames (LambdaRule x p) = S.singleton x `S.union` getFunctionalProofNames p
getFunctionalProofNames (AppRule p1 p2) = getFunctionalProofNames p1 `S.union` getFunctionalProofNames p2
getFunctionalProofNames (SigmaRule x p1 p2) = S.singleton x `S.union` getFunctionalProofNames p1 `S.union` getFunctionalProofNames p2
getFunctionalProofNames (PairRule x p1 p2 p3) = S.singleton x `S.union` getFunctionalProofNames p1 `S.union` getFunctionalProofNames p2 `S.union` getFunctionalProofNames p3
getFunctionalProofNames (Proj1Rule p) = getFunctionalProofNames p
getFunctionalProofNames (Proj2Rule p) = getFunctionalProofNames p
getFunctionalProofNames (CumulativiyRule p1 p2) = getFunctionalProofNames p1 `S.union` getFunctionalProofNames p2

getFunctionalProofFreeNames :: FunctionalProof -> S.Set String
getFunctionalProofFreeNames (CRule ctx) = getFunctionalContextFreeNames ctx
getFunctionalProofFreeNames (TRule i ctx) = getFunctionalContextFreeNames ctx
getFunctionalProofFreeNames (VarRule x ctx) = S.singleton x `S.union` getFunctionalContextFreeNames ctx
getFunctionalProofFreeNames (Pi1Rule x p) = S.delete x $ getFunctionalProofFreeNames p
getFunctionalProofFreeNames (Pi2Rule x p1 p2) = getFunctionalProofFreeNames p2 `S.union` S.delete x (getFunctionalProofFreeNames p2)
getFunctionalProofFreeNames (LambdaRule x p) = S.delete x $ getFunctionalProofFreeNames p
getFunctionalProofFreeNames (AppRule p1 p2) = getFunctionalProofFreeNames p1 `S.union` getFunctionalProofFreeNames p2
getFunctionalProofFreeNames (SigmaRule x p1 p2) = getFunctionalProofFreeNames p2 `S.union` S.delete x (getFunctionalProofFreeNames p2)
getFunctionalProofFreeNames (PairRule x p1 p2 p3) = getFunctionalProofFreeNames p1 `S.union` getFunctionalProofFreeNames p2 `S.union` S.delete x (getFunctionalProofFreeNames p3)
getFunctionalProofFreeNames (Proj1Rule p) = getFunctionalProofFreeNames p
getFunctionalProofFreeNames (Proj2Rule p) = getFunctionalProofFreeNames p
getFunctionalProofFreeNames (CumulativiyRule p1 p2) = getFunctionalProofFreeNames p1 `S.union` getFunctionalProofFreeNames p2

{-| renameVarInFnCtx ctx x y = ctx[x/y]. Rename y with x in ctx. Avoids capturing. -}
renameVarInFnCtx :: S.Set String -> FunctionalContext -> String -> String -> FunctionalContext
renameVarInFnCtx vars ctx x y =
    if not $ x `S.member` (getFunctionalContextFreeNames ctx `S.union` vars)
    then TaggedFunctionalContext { judgments = (\(y1, ty) -> (if y1 == y then x else y1, substVarFunctional ty x y)) <$> judgments ctx } -- x is not a free name in the context, and will not clash.
    else renameVarInFnCtx vars (renameVarInFnCtx vars ctx newFreshName x) x y -- x is free, so it must be renamed first.
    where
        newFreshName = getFreshName $ S.fromList [x, y] `S.union` getFunctionalContextNames ctx

{-| renameVarInProof p x y = P[x/y]. Rename y with x in proof P. Avoids capturing. -}
renameVarInProof :: S.Set String -> FunctionalProof -> String -> String -> FunctionalProof
renameVarInProof vars p x y =
    if not $ x `S.member` (getFunctionalProofFreeNames p `S.union` vars)
    then
    (let
        allNamesConsidered = S.fromList [x, y] `S.union` getFunctionalProofNames p
        freshName = getFreshName allNamesConsidered
    in
        case p of
            CRule c -> CRule $ renameVarInFnCtx vars c x y
            TRule i c -> TRule i $ renameVarInFnCtx vars c x y
            VarRule z c -> VarRule (if z == y then x else z) (renameVarInFnCtx vars c x y)
            Pi1Rule z p1 -> if y == z then Pi1Rule z p1 -- y is captured
                else if x == z then renameVarInProof vars (Pi1Rule freshName (renameVarInProof vars p1 freshName z)) x y -- x will get captured
                else Pi1Rule z $ renameVarInProof vars p x y
            Pi2Rule z p1 p2 -> if y == z then Pi2Rule z (renameVarInProof vars p1 x y) p2 -- y is captured
                else if x == z then renameVarInProof vars (Pi2Rule freshName p1 (renameVarInProof vars p2 freshName z)) x y -- x will get captured
                else Pi2Rule z (renameVarInProof vars p1 x y) (renameVarInProof vars p2 x y)
            LambdaRule z p1 -> if y == z then LambdaRule z p1 -- y is captured
                else if x == z then renameVarInProof vars (LambdaRule freshName (renameVarInProof vars p freshName z)) x y -- x will get captured
                else LambdaRule z $ renameVarInProof vars p x y
            AppRule p1 p2 -> AppRule (renameVarInProof vars p1 x y) (renameVarInProof vars p2 x y)
            SigmaRule z p1 p2 -> if y == z then SigmaRule z (renameVarInProof vars p1 x y) p2 -- y is captured
                else if x == z then renameVarInProof vars (SigmaRule freshName p1 (renameVarInProof vars p2 freshName z)) x y -- x will get captured
                else SigmaRule z (renameVarInProof vars p1 x y) (renameVarInProof vars p2 x y)
            PairRule z p1 p2 p3 -> if y == z then PairRule z (renameVarInProof vars p1 x y) (renameVarInProof vars p2 x y) p3 -- y is captured
                else if x == z then renameVarInProof vars (PairRule freshName p1 p2 (renameVarInProof vars p3 freshName z)) x y -- x will get captured
                else PairRule z (renameVarInProof vars p1 x y) (renameVarInProof vars p2 x y) (renameVarInProof vars p3 x y)
            Proj1Rule p1 -> Proj1Rule $ renameVarInProof vars p1 x y
            Proj2Rule p1 -> Proj2Rule $ renameVarInProof vars p1 x y
            CumulativiyRule p1 p2 -> CumulativiyRule (renameVarInProof vars p1 x y) (renameVarInProof vars p2 x y))
    else
    (let
        newFreshName = getFreshName $ S.fromList [x, y] `S.union` getFunctionalProofNames p
    in
        renameVarInProof vars (renameVarInProof vars p newFreshName x) x y)
{-| Take one beta reduction if possible. Nothing otherwise.
    Implements the non-reflexive non-symmetric conversion rules
    of the calculus of constructions.

>>> betaStep (App (Lambda "x" (Var "A") (Var "x")) (Var "z"))    
Just z

>>> betaStep (App (Var "f") (App (Lambda "x" (Var "A") (Var "x")) (Var "z")))
Just (f z)
-}
conversionStep :: FunctionalTerm -> Maybe FunctionalTerm
conversionStep (App (Lambda x a b) n) = Just $ functionalSubst b n x
conversionStep (Proj1 (Pair m n x a b)) = Just m
conversionStep (Proj2 (Pair m n x a b)) = Just n
conversionStep (App t1 t2) = case conversionStep t1 of
    Just res -> Just $ App res t2
    Nothing -> case conversionStep t2 of
        Just res -> Just $ App t1 res
        Nothing -> Nothing
conversionStep (Lambda x a b) = case conversionStep a of
    Just res -> Just $ Lambda x res b
    Nothing -> case conversionStep b of
        Just res -> Just $ Lambda x a res
        Nothing -> Nothing
conversionStep (Pi x a b) = case conversionStep a of
    Just res -> Just $ Pi x res b
    Nothing -> case conversionStep b of
        Just res -> Just $ Pi x a res
        Nothing -> Nothing
conversionStep (Sigma x a b) = case conversionStep a of
    Just res -> Just $ Sigma x res b
    Nothing -> case conversionStep b of
        Just res -> Just $ Sigma x a res
        Nothing -> Nothing
conversionStep (Pair m n x a b) = case conversionStep m of
    Just res -> Just $ Pair res n x a b
    Nothing -> case conversionStep n of
        Just res -> Just $ Pair m res x a b
        Nothing -> case conversionStep a of
            Just res -> Just $ Pair m n x res b
            Nothing -> case conversionStep b of
                Just res -> Just $ Pair m n x a res
                Nothing -> Nothing
conversionStep (Proj1 t) = Proj1 <$> conversionStep t
conversionStep (Proj2 t) = Proj2 <$> conversionStep t
conversionStep t = Nothing

{-| Get all conversions possible. Beta and Sigma

>>> allConversionSteps (Var "x")
[x]

>>> allConversionSteps (App (Lambda "x" (Var "A") (Var "x")) (Var "z"))    
[((\x : A. x) z),z]

>>> allConversionSteps (App (Var "f") (App (Lambda "x" (Var "A") (Var "x")) (Var "z")))
[(f ((\x : A. x) z)),(f z)]

>>> allConversionSteps (Proj1 (Pair (Var "x") (Var "y") "t" (Var "A") (Var "B")))
[proj1 (x, y):(tA) * B,x]

>>> allConversionSteps (Proj2 (Pair (Var "x") (Var "y") "t" (Var "A") (Var "B")))
[proj2 (x, y):(tA) * B,y]
-}
allConversionSteps :: FunctionalTerm -> [FunctionalTerm]
allConversionSteps t = t:maybe [] allConversionSteps (conversionStep t)

conversionRelation :: FunctionalTerm -> FunctionalTerm -> Bool
conversionRelation t1 t2 = not (null (allConversionSteps t1 `L.intersect` allConversionSteps t2))

{-| Checks that the cumulativity relation holds between two terms. t1 <= t2
>>> cumulativiyRelation Prop (Type 0)
True

>>> cumulativiyRelation (Type 0) Prop
False

>>> cumulativiyRelation (Var "z") (App (Lambda "x" (Var "A") (Var "x")) (Var "z"))
True

>>> cumulativiyRelation (Pi "x" (Type 1) (Type 2)) (Pi "x" (Type 1) (Type 3))
True

>>> cumulativiyRelation (Pi "x" (Type 1) (Type 2)) (Pi "x" (Type 2) (Type 3))
False

>>> cumulativiyRelation (Sigma "x" (Type 1) (Type 2)) (Sigma "x" (Type 1) (Type 3))
True

>>> cumulativiyRelation (Sigma "x" (Type 1) (Type 2)) (Sigma "x" (Type 2) (Type 3))
True
-}
cumulativiyRelation :: FunctionalTerm -> FunctionalTerm -> Bool
cumulativiyRelation Prop (Type i) = True
cumulativiyRelation (Type i) (Type j) = i <= j
cumulativiyRelation (Pi x1 a1 b1) (Pi x2 a2 b2) = x1 == x2
    && cumulativiyRelation b1 b2
    && conversionRelation a1 a2
cumulativiyRelation (Sigma x1 a1 b1) (Sigma x2 a2 b2) = x1 == x2
    && cumulativiyRelation b1 b2
    && cumulativiyRelation a1 a2
cumulativiyRelation t1 t2 = conversionRelation t1 t2

isTrueP t p = unless t $ Left ("Proof failed for " ++ show p)

{-| Extracts the proof corresponding to a term.

>>> extractProofFromTermUnderCtx (M.fromList []) (Type 1)
Right (TRule 1 FunctionalAxiom)

>>> extractProofFromTermUnderCtx (M.fromList [("x", Type 1)]) (Var "x")
Right (VarRule "x" (CRule "x" (TRule 1 FunctionalAxiom)))

>>> extractProofFromTermUnderCtx (M.fromList [("x", (Var "A")), ("A", Type 1)]) (Var "x")
Right (VarRule "x" (CRule "x" (VarRule "A" (CRule "A" (TRule 1 FunctionalAxiom)))))

>>> extractProofFromTermUnderCtx (M.fromList []) (Lambda "A" (Prop) (Lambda "x" (Var "A") (Var "x")))
Right (LambdaRule "A" (LambdaRule "x" (VarRule "x" (CRule "x" (VarRule "A" (CRule "A" FunctionalAxiom))))))

>>> extractProofFromTermUnderCtx (M.fromList []) (Lambda "A" (Type 1) (Lambda "x" (Var "A") (Var "x")))
Right (LambdaRule "A" (LambdaRule "x" (VarRule "x" (CRule "x" (VarRule "A" (CRule "A" (TRule 1 FunctionalAxiom)))))))

>>> extractProofFromTermUnderCtx (M.fromList []) (Lambda "A" (Type 1) (Lambda "x" (Var "A") (Var "x"))) >>= functionalConcl
Right (FunctionalSequent {functionalContext = fromList [], goalTerm = (\A : Type 1. (\x : A. x)), goalType = [A : Type 1. [x : A. A]]})

>>> functionalConcl (VarRule "A" (CRule "A" (TRule 2 FunctionalAxiom)))
Right (FunctionalSequent {functionalContext = fromList [("A",Type 2)], goalTerm = A, goalType = Type 2})

>>> extractProofFromTermUnderCtx (M.fromList []) (Lambda "x" (Type 1) (Lambda "x" (Var "x") (Var "x")))
Left "Could not find variables that are not free in the rest of the context."
-}
extractProofFromTermUnderCtx :: TaggedFunctionalContext SafeCtx -> FunctionalTerm -> Either String (FunctionalTerm, FunctionalProof)
extractProofFromTermUnderCtx ctx (Type i) = return $ (Type (i + 1), TRule i ctx)
extractProofFromTermUnderCtx ctx Prop = return (Type 0, CRule ctx)
extractProofFromTermUnderCtx ctx (Var x) = do
    ty <- ctxEitherLookup x ctx
    return $ (ty, VarRule x ctx)
extractProofFromTermUnderCtx ctx (Pi a ty t) = do
    newCtx <- safeInsert a ty ctx
    tP <- extractProofFromTermUnderCtx newCtx t
    tyP <- extractProofFromTermUnderCtx ctx ty
    let tPConcl = fst tP
        tyPConcl = fst tyP
    typeCheckedType <- (case (tPConcl, tyPConcl) of
            (Prop, Prop) -> return (Prop, Pi1Rule a (snd tP))
            (Prop, Type i) -> return (Prop, Pi1Rule a (snd tP))
            (Type i, Type j) -> return $ (Type (max i j), Pi2Rule a (snd tyP) (snd tP))
            (Type i, Prop) -> return $ (Type i, Pi2Rule a (snd tyP) (CumulativiyRule (snd tP) (TRule i ctx)))
            _ -> Left ("Pi type does not have types as expected. Got: " ++ ftToS ty ++ ":" ++ ftToS tyPConcl ++ " and " ++ ftToS t ++ ":" ++ ftToS tPConcl))
    return typeCheckedType
extractProofFromTermUnderCtx ctx (Lambda a ty t) = do
    newCtx <- safeInsert a ty ctx
    tP <- extractProofFromTermUnderCtx newCtx t
    return (Pi a ty (fst tP), LambdaRule a (snd tP))
extractProofFromTermUnderCtx ctx (App t1 t2) = do
    p1 <- extractProofFromTermUnderCtx ctx t1
    p2 <- extractProofFromTermUnderCtx ctx t2
    (x, a, b) <- case fst p1 of
        Pi x a b -> return (x, a, b)
        _ -> Left $ "Found invalid type for application expect a Pi type but got: " ++ ftToS (fst p1)
    return (functionalSubst b t2 x, AppRule (snd p1) (snd p2))
extractProofFromTermUnderCtx ctx (Sigma x a b) = do
    tyP <- extractProofFromTermUnderCtx ctx a
    newCtx <- safeInsert x a ctx
    tP <- extractProofFromTermUnderCtx newCtx b
    typeCheckedType <- case (fst tyP, fst tP) of
        (Type i, Type j) -> return $ Type (max i j)
        (Prop, Type j) -> return $ Type j
        (Type i, Prop) -> return $ Type i
        (Prop, Prop) -> return $ Type 0
        _ -> Left ("Sigma type does not have types as expected. Got: " ++ ftToS a ++ ":" ++ ftToS (fst tyP) ++ " and " ++ ftToS b ++ ":" ++ ftToS (fst tP))
    return (typeCheckedType, SigmaRule x (snd tyP) (snd tP))
extractProofFromTermUnderCtx ctx (Pair m n x a b) = do
    newCtx <- safeInsert x a ctx
    mProof <- extractProofFromTermUnderCtx ctx m
    nProof <- extractProofFromTermUnderCtx ctx n
    bProof <- extractProofFromTermUnderCtx newCtx b
    return (Sigma x a b, PairRule x (snd mProof) (snd nProof) (snd bProof))
extractProofFromTermUnderCtx ctx (Proj1 m) = do
    mProof <- extractProofFromTermUnderCtx ctx m
    (x, a, b) <- case fst mProof of
        Sigma x a b -> return (x, a, b)
        res -> Left $ "Found invalid type for application expect a Sigma type but got: " ++ ftToS (fst mProof)
    return (a, Proj1Rule (snd mProof))
extractProofFromTermUnderCtx ctx (Proj2 m) = do
    mProof <- extractProofFromTermUnderCtx ctx m
    (x, a, b) <- case fst mProof of
        Sigma x a b -> return (x, a, b)
        res -> Left $ "Found invalid type for application expect a Sigma type but got: " ++ ftToS (fst mProof)
    return (functionalSubst b (Proj1 m) x, Proj2Rule (snd mProof))

safeInsert :: String -> FunctionalTerm -> TaggedFunctionalContext SafeCtx -> Either String (TaggedFunctionalContext SafeCtx)
safeInsert x ty ctx = do
    (k, p) <- extractProofFromTermUnderCtx ctx ty
    concl <- verifyFunctionalProofM p
    case goalType concl of
        Type j -> return (TaggedFunctionalContext { judgments = (x,ty):judgments ctx })
        Prop -> return (TaggedFunctionalContext { judgments = (x,ty):judgments ctx })
        res -> Left $ ftToS ty ++ " is not a type! Extracted type is: " ++ ftToS res

{-|
>>> verifyFunctionalProofM simpleFunctionalProof
Just True
-}
verifyFunctionalProofM :: FunctionalProof -> Either String FunctionalSequent
verifyFunctionalProofM (CRule ctx) = return $ FunctionalSequent { functionalContext = ctx, goalTerm = Prop, goalType = Type 0 }
verifyFunctionalProofM (TRule i ctx) = return $ FunctionalSequent { functionalContext = ctx, goalTerm = Type i, goalType = Type (i + 1) }
verifyFunctionalProofM (VarRule x ctx) = do
    xTy <- ctxEitherLookup x ctx
    return $ FunctionalSequent { functionalContext = ctx, goalTerm = Var x, goalType = xTy }
verifyFunctionalProofM (Pi1Rule x p) = do
    seq <- verifyFunctionalProofM p
    ty <- case ctxTake1 (functionalContext seq) of
        [(x1, ty)] | x == x1 -> return ty
        [(x1, ty)] -> Left $ "End of context should have " ++ x ++ " but has " ++ x1
        [] -> Left $ "Context is empty but expected " ++ x
    case goalType seq of
        Prop -> return $ FunctionalSequent { functionalContext = ctxDrop1 (functionalContext seq), goalTerm = Pi x ty (goalTerm seq), goalType = Prop }
        _ -> Left "Invalid conclusion in derviation above Pi1Rule. Expected Prop."
verifyFunctionalProofM (Pi2Rule x p1 p2) = do
    seq1 <- verifyFunctionalProofM p1
    seq2 <- verifyFunctionalProofM p2
    xTy <- case ctxTake1 (functionalContext seq2) of
        [(x1, ty)] | x1 == x && ty == goalTerm seq1 -> return ty
        [(x1, ty)] -> Left $ "End of context should have " ++ x ++ " with type " ++ ftToS (goalTerm seq1) ++ " but has " ++ x1 ++ " with type " ++ ftToS ty
        [] -> Left $ "Context is empty but expected " ++ x
    fullTy <- case (goalType seq1, goalType seq2) of
        (Type i, Type j) -> return $ Type (max i j)
        (Prop, Type j) -> return $ Type j
        (Type i, Prop) -> return $ Type i
        (Prop, Prop) -> return $ Type 0
        r -> Left $ "Invalid kinds as the result types of the proof conclusions: " ++ show r
    seq1Extended <- safeInsert x (goalTerm seq1) (functionalContext seq1)
    unless (seq1Extended == functionalContext seq2) $ Left ("Contexts not equal: " ++ fcToS seq1Extended ++ " and " ++ fcToS (functionalContext seq2))
    unless (xTy == goalTerm seq1) $ Left (x ++ " does not have expected type: " ++ ftToS (goalTerm seq1) ++ " got " ++ ftToS xTy)
    return (FunctionalSequent { functionalContext = functionalContext seq1, goalTerm = Pi x (goalTerm seq1) (goalTerm seq2), goalType = fullTy })
verifyFunctionalProofM (LambdaRule x p) = do
    seq <- verifyFunctionalProofM p
    xTy <- case ctxTake1 (functionalContext seq) of
        [(x1, ty)] | x1 == x -> return ty
        [(x1, ty)] -> Left $ "End of context should have " ++ x ++ " but has " ++ x1
        [] -> Left $ "Context is empty but expected " ++ x
    return (FunctionalSequent { functionalContext = ctxDrop1 (functionalContext seq), goalTerm = Lambda x xTy (goalTerm seq), goalType = Pi x xTy (goalType seq) })
verifyFunctionalProofM (AppRule p1 p2) = do
    seq1 <- verifyFunctionalProofM p1
    seq2 <- verifyFunctionalProofM p2
    (x, a, b) <- case goalType seq1 of
            Pi x a b | a == goalType seq2 -> return (x, a, b)
            _ -> Left $ "Invalid goal type. Expected Pi type with argument type " ++ ftToS (goalType seq2) ++ " but got " ++ ftToS (goalType seq1)
    unless (functionalContext seq1 == functionalContext seq2) (Left ("Contexts not equal: " ++ fcToS (functionalContext seq1) ++ " and " ++ fcToS (functionalContext seq2)))
    return (FunctionalSequent { functionalContext = functionalContext seq1, goalTerm = App (goalTerm seq1) (goalTerm seq2), goalType = functionalSubst b (goalTerm seq2) x })
verifyFunctionalProofM (SigmaRule x p1 p2) = do
    seq1 <- verifyFunctionalProofM p1
    seq2 <- verifyFunctionalProofM p2
    xTy <- case ctxTake1 (functionalContext seq2) of
        [(x1, ty)] | x1 == x && ty == goalTerm seq1 -> return ty
        [(x1, ty)] -> Left $ "End of context should have " ++ x ++ " with type " ++ ftToS (goalTerm seq1) ++ " but has " ++ x1 ++ " with type " ++ ftToS ty
        [] -> Left $ "Context is empty but expected " ++ x
    resTy <- case (goalType seq1, goalType seq2) of
        (Type i, Type j) -> return $ Type (max i j)
        (Prop, Type j) -> return $ Type j
        (Type i, Prop) -> return $ Type i
        (Prop, Prop) -> return $ Type 0
        r -> Left $ "Invalid kinds as the result types of the proof conclusions: " ++ show r
    seq1Extended <- safeInsert x (goalTerm seq1) (functionalContext seq1)
    unless (seq1Extended == functionalContext seq2) $ Left ("Contexts not equal: " ++ fcToS seq1Extended ++ " and " ++ fcToS (functionalContext seq2))
    return (FunctionalSequent { functionalContext = functionalContext seq1, goalTerm = Sigma x (goalTerm seq1) (goalTerm seq2), goalType = resTy })
verifyFunctionalProofM (PairRule x p1 p2 p3) = do
    seq1 <- verifyFunctionalProofM p1
    seq2 <- verifyFunctionalProofM p2
    seq3 <- verifyFunctionalProofM p3
    case goalType seq3 of
        Type j -> return ()
        _ -> Left $ "Invalid conclusion in third proof for PairRule application. Expected Type_j. Got: " ++ ftToS (goalType seq3)
    xTy <- case ctxTake1 (functionalContext seq3) of
        [(x1, ty)] | x1 == x && goalType seq1 == ty -> return ty
        [(x1, ty)] -> Left $ "End of context should have " ++ x ++ " with type " ++ ftToS (goalType seq1) ++ " but has " ++ x1 ++ " with type " ++ ftToS ty
        [] -> Left $ "Context is empty but expected " ++ x
    let p2ExpectedTy = functionalSubst (goalTerm seq3) (goalTerm seq1) x
        p2ValidTy = goalType seq2 == p2ExpectedTy
    unless (p2ValidTy
        && xTy == goalType seq1
        && functionalContext seq1 == functionalContext seq2
        && functionalContext seq2 == ctxDrop1 (functionalContext seq3)) $ Left "Errors validating Pair rule."
    return (FunctionalSequent { functionalContext = functionalContext seq1, goalTerm = Pair (goalTerm seq1) (goalTerm seq2) x (goalType seq1) (goalTerm seq3), goalType = Sigma x (goalType seq1) (goalTerm seq3) })
verifyFunctionalProofM (Proj1Rule p) = do
    seq <- verifyFunctionalProofM p
    case goalType seq of
        Sigma x a b -> return (FunctionalSequent { functionalContext = functionalContext seq, goalTerm = Proj1 (goalTerm seq), goalType = a })
        _ -> Left $ "Invalid conclusion in derivation for Proj1Rule. Expected Sigma, but got: " ++ show (goalType seq)
verifyFunctionalProofM (Proj2Rule p) = do
    seq <- verifyFunctionalProofM p
    case goalType seq of
        Sigma x a b -> return (FunctionalSequent { functionalContext = functionalContext seq, goalTerm = Proj2 (goalTerm seq), goalType = functionalSubst b (Proj1 (goalTerm seq)) x })
        _ -> Left $ "Invalid conclusion in derivation for Proj2Rule. Expected Sigma, but got: " ++ show (goalType seq)
verifyFunctionalProofM (CumulativiyRule p1 p2) = do
    seq1 <- verifyFunctionalProofM p1
    seq2 <- verifyFunctionalProofM p2
    unless (functionalContext seq1 == functionalContext seq2) $ Left $ "Contexts not equal: " ++ fcToS (functionalContext seq1) ++ " and " ++ fcToS (functionalContext seq2)
    unless (cumulativiyRelation (goalType seq1) (goalTerm seq2)) $ Left $ "Cumulativity doesn't hold. Expected " ++ ftToS (goalType seq1) ++ " to be smaller or equal to " ++ ftToS (goalTerm seq2)
    return (FunctionalSequent { functionalContext = functionalContext seq1, goalTerm = goalTerm seq1, goalType = goalTerm seq2 })

verifyFunctionalProof :: FunctionalProof -> Bool
verifyFunctionalProof p =  case verifyFunctionalProofM p of
    Right _ -> True
    _ -> False

{-| P{x/u} replace free occurances of u with x in P. Avoids capturing.
>>> substVarFunctional (Lambda "x" (Var "y") (Var "x")) "z" "x"
Lambda "x" (Var "y") (Var "x")

>>> substVarFunctional (Lambda "x" (Var "y") (Var "x")) "x" "y"
Lambda "a" (Var "x") (Var "a")
-}
substVarFunctional :: FunctionalTerm -> String -> String -> FunctionalTerm
substVarFunctional t x = functionalSubst t (Var x)

{-| A{y/N} replace N with y in A. -}
abstTermFunctional :: FunctionalTerm -> String -> FunctionalTerm -> FunctionalTerm
abstTermFunctional a y n = if a == n then Var y else case a of
    App t1 t2 -> App (abstTermFunctional t1 y n) (abstTermFunctional t2 y n)
    Lambda x t1 t2 -> if x `S.member` functionalFreeVariables n then a -- n is no longer possible
        else if x == y then abstTermFunctional (alphaConvert (Lambda x t1 t2) (S.fromList [x, y] `S.union` functionalNames a `S.union` functionalNames n)) y n -- new var will be captured
        else Lambda x (abstTermFunctional t1 y n) (abstTermFunctional t2 y n)
    Pi x t1 t2 -> if x `S.member` functionalFreeVariables n then a
        else if x == y then abstTermFunctional (alphaConvert (Pi x t1 t2) (S.fromList [x, y] `S.union` functionalNames a `S.union` functionalNames n)) y n
        else Pi x (abstTermFunctional t1 y n) (abstTermFunctional t2 y n)
    Sigma x t1 t2 -> if x `S.member` functionalFreeVariables n then a
        else if x == y then abstTermFunctional (alphaConvert (Sigma x t1 t2) (S.fromList [x, y] `S.union` functionalNames a `S.union` functionalNames n)) y n
        else Sigma x (abstTermFunctional t1 y n) (abstTermFunctional t2 y n)
    Pair t1 t2 x ty1 ty2 -> if x `S.member` functionalFreeVariables n then a
        else if x == y then abstTermFunctional (alphaConvert (Pair t1 t2 x ty1 ty2) (S.fromList [x, y] `S.union` functionalNames a `S.union` functionalNames n)) y n
        else Pair (abstTermFunctional t1 y n) (abstTermFunctional t2 y n) x (abstTermFunctional ty1 y n) (abstTermFunctional ty2 y n)
    Proj1 t -> Proj1 (abstTermFunctional t y n)
    Proj2 t -> Proj2 (abstTermFunctional t y n)
    x -> x

implication :: String -> FunctionalTerm -> FunctionalTerm -> FunctionalTerm
implication sfx = Pi ("_" ++ sfx)

sigma :: String -> String -> FunctionalTerm -> FunctionalTerm -> FunctionalTerm
sigma sfx x a b = Pi "_c" Prop (implication sfx (Pi x a (implication sfx b (Var "_c"))) (Var "_c"))
