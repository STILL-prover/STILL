module FunctionalSystem where

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import Util
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
    deriving (Eq, Show, Read)

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

{-| B{N/x} replace x with n in b 

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

type FunctionalContext = M.Map String FunctionalTerm

getFunctionalContextNames :: FunctionalContext -> S.Set String
getFunctionalContextNames c = S.fromList (M.keys c) `S.union` S.unions (functionalNames <$> M.elems c)

data FunctionalSequent = FunctionalSequent {
    functionalContext :: FunctionalContext,
    goalTerm :: FunctionalTerm,
    goalType :: FunctionalTerm
} deriving (Show, Eq)

getFunctionalSequentNames :: FunctionalSequent -> S.Set String
getFunctionalSequentNames (FunctionalSequent fc gt gTy) = functionalNames gTy `S.union` functionalNames gt `S.union` getFunctionalContextNames fc

{-|
    The proof rules and validation here differ slightly from the original presentation of Luo's ECC.
    We aim to avoid deriving G |- A:Type i multiple times. The variable and pi rules are now.
    Luo's ECC has the property that there is always a derivation of G|-A:K above G,x:A|-x:A.
    
    G |- x:A
    -----------------
    G, x:A, G' |- x:A

    G|-A:K     G,x:A|-B:L
    ----------------- K,L are kinds. 
    G|-Pi x:A.B : if L == Prop then Prop else max (Type 0, K, L)
-}
data FunctionalProof = FunctionalAxiom FunctionalContext -- \vdash P:T
    | TRule Integer FunctionalProof -- \vdash Type_i : Type_(i+1)
    | VarRule String FunctionalProof
    | PiRule String FunctionalProof FunctionalProof
    | LambdaRule String FunctionalProof
    | AppRule FunctionalProof FunctionalProof
    | SigmaRule String FunctionalProof FunctionalProof
    | PairRule String FunctionalProof FunctionalProof FunctionalProof
    | Proj1Rule FunctionalProof
    | Proj2Rule FunctionalProof
    | CumulativiyRule FunctionalProof FunctionalProof
    -- | FHoleRule FunctionalContext FunctionalTerm FunctionalTerm
    deriving (Eq, Show, Read)

subFunctionalProofs :: FunctionalProof -> [FunctionalProof]
subFunctionalProofs rule = case rule of
    PiRule _ fp1 fp2          -> [fp1, fp2]
    SigmaRule _ fp1 fp2       -> [fp1, fp2]
    PairRule _ fp1 fp2 fp3    -> [fp1, fp2, fp3]
    CumulativiyRule fp1 fp2   -> [fp1, fp2]
    TRule _ fp                -> [fp]
    VarRule _ fp              -> [fp]
    LambdaRule _ fp           -> [fp]
    AppRule fp1 fp2           -> [fp1, fp2]
    Proj1Rule fp              -> [fp]
    Proj2Rule fp              -> [fp]
    FunctionalAxiom{}         -> []

foldFunctionalProof :: ([a] -> a) -> FunctionalProof -> a
foldFunctionalProof fFunc rule = fFunc (map (foldFunctionalProof fFunc) (subFunctionalProofs rule))

functionalProofSize :: FunctionalProof -> Integer
functionalProofSize = foldFunctionalProof (\results -> 1 + sum results)

functionalProofDepth :: FunctionalProof -> Integer
functionalProofDepth = foldFunctionalProof (\results -> 1 + maximum (0 : results))

{-| Get all names used in a proof derivation. -}
getFunctionalProofNames :: FunctionalProof -> S.Set String
getFunctionalProofNames (FunctionalAxiom ctx) = getFunctionalContextNames ctx
getFunctionalProofNames (TRule i p) = getFunctionalProofNames p
getFunctionalProofNames (VarRule x p) = S.singleton x `S.union` getFunctionalProofNames p
getFunctionalProofNames (PiRule x p1 p2) = S.singleton x `S.union` getFunctionalProofNames p1 `S.union` getFunctionalProofNames p2
getFunctionalProofNames (LambdaRule x p) = S.singleton x `S.union` getFunctionalProofNames p
getFunctionalProofNames (AppRule p1 p2) = getFunctionalProofNames p1 `S.union` getFunctionalProofNames p2
getFunctionalProofNames (SigmaRule x p1 p2) = S.singleton x `S.union` getFunctionalProofNames p1 `S.union` getFunctionalProofNames p2
getFunctionalProofNames (PairRule x p1 p2 p3) = S.singleton x `S.union` getFunctionalProofNames p1 `S.union` getFunctionalProofNames p2 `S.union` getFunctionalProofNames p3
getFunctionalProofNames (Proj1Rule p) = getFunctionalProofNames p
getFunctionalProofNames (Proj2Rule p) = getFunctionalProofNames p
getFunctionalProofNames (CumulativiyRule p1 p2) = getFunctionalProofNames p1 `S.union` getFunctionalProofNames p2

{-| renameVarInProof x y = P[x/y]. Rename y with x in proof P. -}
renameVarInFnProof :: S.Set String -> FunctionalProof -> String -> String -> FunctionalProof
renameVarInFnProof vars p x y = if x `S.member`(vars `S.union` getFunctionalProofNames p)
    then go p
    else renameVarInFnProof vars (renameVarInFnProof vars p newFreshName x) x y -- Rename x first, then y
    where
        newFreshName :: String
        newFreshName = getFreshName $ S.fromList [x, y] `S.union` getFunctionalProofNames p

        swap :: String -> String
        swap test = if test == y then x else test

        swapCtx :: FunctionalContext -> FunctionalContext
        swapCtx ctx = M.fromList $ (\(k, a) -> (swap k, substVarFunctional a x y)) <$> M.toList ctx

        go (FunctionalAxiom ctx) = FunctionalAxiom (swapCtx ctx)
        go (TRule i p) = TRule i (go p)
        go (VarRule x p) = VarRule (swap x) (go p)
        go (PiRule x p1 p2) = PiRule (swap x) (go p1) (go p2)
        go (LambdaRule x p) = LambdaRule (swap x) (go p)
        go (AppRule p1 p2) = AppRule (go p1) (go p2)
        go (SigmaRule x p1 p2) = SigmaRule (swap x) (go p1) (go p2)
        go (PairRule x p1 p2 p3) = PairRule (swap x) (go p1) (go p2) (go p3)
        go (Proj1Rule p) = Proj1Rule (go p)
        go (Proj2Rule p) = Proj2Rule (go p)
        go (CumulativiyRule p1 p2) = CumulativiyRule (go p1) (go p2)


simpleFunctionalProof :: FunctionalProof
simpleFunctionalProof = VarRule "x" $ VarRule "A" $ (FunctionalAxiom M.empty)
simpleFunctionalProof2 :: FunctionalProof
simpleFunctionalProof2 = VarRule "A" $ FunctionalAxiom M.empty
simpleFunctionalProof3 :: FunctionalProof
simpleFunctionalProof3 = FunctionalAxiom M.empty

functionalConcl :: FunctionalProof -> Either String FunctionalSequent
-- functionalConcl p | p `M.member` concls = Right (concls M.! p, concls)
functionalConcl (FunctionalAxiom ctx) = return $ (FunctionalSequent { functionalContext = ctx, goalTerm = Prop, goalType = Type 0 })
-- functionalConcl (CRule x p) concls = do
--     (pConcl, concls2) <- functionalConcl p concls
--     return (pConcl { functionalContext = M.insert x (goalTerm pConcl) $ functionalContext pConcl, goalTerm = Prop , goalType = Type 0 }, M.insert p pConcl concls2)
functionalConcl (TRule i p) = do
    pConcl <- functionalConcl p
    return (pConcl { goalTerm = Type i , goalType = Type (i + 1) })
functionalConcl (VarRule x p) = do
    pConcl <- functionalConcl p
    return (pConcl { functionalContext = M.insert x (goalTerm pConcl) (functionalContext pConcl), goalTerm = Var x, goalType = goalTerm pConcl })
-- functionalConcl (Pi1Rule x p) concls = do
--     (pConcl, concls2) <- functionalConcl p concls
--     xTy <- eitherLookup x (functionalContext pConcl)
--     return (pConcl { functionalContext = M.delete x $ functionalContext pConcl, goalTerm = Pi x xTy (goalTerm pConcl), goalType = Prop }, M.insert p pConcl concls2)
functionalConcl (PiRule x p1 p2) = do
    p1Concl <- functionalConcl p1
    p2Concl <- functionalConcl p2
    let newGoal = case (goalType p1Concl, goalType p2Concl) of
            (_, Prop) -> Prop
            (Type i, Type j) -> Type (max i j)
            (Type i, _) -> Type i
            (_, Type j) -> Type j
            (_, _) -> Type 0
    return (p1Concl { goalTerm = Pi x (goalTerm p1Concl) (goalTerm p2Concl), goalType = newGoal })
functionalConcl (LambdaRule x p) = do
    (pConcl) <- functionalConcl p
    xTy <- eitherLookup x (functionalContext pConcl)
    return (pConcl { functionalContext = M.delete x $ functionalContext pConcl, goalTerm = Lambda x xTy (goalTerm pConcl), goalType = Pi x xTy (goalType pConcl) })
functionalConcl (AppRule p1 p2) = do
    (p1Concl) <- functionalConcl p1
    (p2Concl) <- functionalConcl p2
    (varToReplace, termReplaceInside) <- (case goalType p1Concl of
        Pi x a b -> return (x, b)
        _ -> Left $ "Error in AppRule (" ++ show p1 ++ ")" ++ "(" ++ show p2 ++ ")")
    return $ (p2Concl { goalTerm = App (goalTerm p1Concl) (goalTerm p2Concl), goalType = functionalSubst termReplaceInside (goalTerm p2Concl) varToReplace })
functionalConcl (SigmaRule x p1 p2) = do
    (p1Concl) <- functionalConcl p1
    (p2Concl) <- functionalConcl p2
    xTy <- eitherLookup x $ functionalContext p2Concl
    let newGoal = case (goalType p1Concl, goalType p2Concl) of
            (Type i, Type j) -> Type (max i j)
            (Type i, _) -> Type i
            (_, Type j) -> Type j
            (_, _) -> Type 0
    return (p1Concl { goalTerm = Sigma x (goalTerm p1Concl) (goalTerm p2Concl), goalType = newGoal })
functionalConcl (PairRule x p1 p2 p3) = do
    (p1Concl) <- functionalConcl p1
    (p2Concl) <- functionalConcl p2
    (p3Concl) <- functionalConcl p3
    xTy <- eitherLookup x $ functionalContext p3Concl
    return (p1Concl { goalTerm = Pair (goalTerm p1Concl) (goalTerm p2Concl) x (goalType p1Concl) (goalTerm p3Concl), goalType = Sigma x (goalType p1Concl) (goalTerm p3Concl) })
functionalConcl (Proj1Rule p) = do
    (pConcl) <- functionalConcl p
    case goalType pConcl of
        Sigma x a b -> return $ (pConcl { goalTerm = Proj1 (goalTerm pConcl), goalType = a })
        _ -> Left "Expected Sigma type proof for Proj1 rule."
functionalConcl (Proj2Rule p) = do
    (pConcl) <- functionalConcl p
    case goalType pConcl of
        Sigma x a b -> return (pConcl { goalTerm = Proj2 (goalTerm pConcl), goalType = functionalSubst b (Proj1 (goalTerm pConcl)) x })
        _ -> Left "Expected Sigma type proof for Proj2 rule."
functionalConcl (CumulativiyRule p1 p2) = do
    (p1Concl) <- functionalConcl p1
    (p2Concl) <- functionalConcl p2
    return $ (p1Concl { goalType = goalTerm p2Concl })
-- functionalConcl (FHoleRule fc gt gTy) = return $ FunctionalSequent { functionalContext = fc, goalTerm = gt, goalType = gTy }

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



{-|
>>> verifyFunctionalProofM simpleFunctionalProof
Just True
-}
verifyFunctionalProofM :: FunctionalProof -> Either String (Bool)
-- verifyFunctionalProofM p av | p `M.member` av = return (True, av)
verifyFunctionalProofM (FunctionalAxiom ctx) = return True
-- verifyFunctionalProofM (CRule x p) av = do
--     (t, av2) <- verifyFunctionalProofM p av
--     isTrueP t p
--     (pConcl, av3) <- functionalConcl p av2
--     when (x `S.member` contextFreeVariables (functionalContext pConcl)) (Left $ x ++ " is a free variable in the context: " ++ show (functionalContext pConcl))
--     case goalType pConcl of
--         (Type i) -> return (True, M.insert p pConcl av3)
--         _ -> Left "Invalid conclusion in derivation above CRule. Expected Type_j."
verifyFunctionalProofM (TRule i p) = do
    (t) <- verifyFunctionalProofM p
    isTrueP t p
    (pConcl) <- functionalConcl p
    case goalType pConcl of
        (Type 0) -> return (i >= 0)
        _ -> Left "Invalid conclusion in derivation above TRule. Expected Type_0."
verifyFunctionalProofM (VarRule x p) = do
    t <- verifyFunctionalProofM p
    isTrueP t p
    seq <- functionalConcl p
    case goalType seq of
        Type i -> return True
        Prop -> return True
        _ -> Left "Invalid conclusion in derviation above VarRule. Expected a kind"
-- verifyFunctionalProofM (Pi1Rule x p) av = do
--     (t, av2) <- verifyFunctionalProofM p av
--     isTrueP t p
--     (seq, av3) <- functionalConcl p av2
--     case goalType seq of
--         Prop -> return (M.member x (functionalContext seq), M.insert p seq av3)
--         _ -> Left "Invalid conclusion in derviation above Pi1Rule. Expected Prop."
verifyFunctionalProofM (PiRule x p1 p2) = do
    (t1) <- verifyFunctionalProofM p1
    (t2) <- verifyFunctionalProofM p2
    isTrueP t1 p1
    isTrueP t2 p2
    (seq1) <- functionalConcl p1
    (seq2) <- functionalConcl p2
    xTy <- case M.lookup x $ functionalContext seq2 of
        Just res -> Right res
        Nothing -> Left $ "Could not find " ++ x ++ " in context of sequent: " ++ show seq2
    case (goalType seq1, goalType seq2) of
        (Type i, Type j) -> return ()
        (Prop, Type j) -> return ()
        (Type i, Prop) -> return ()
        (Prop, Prop) -> return ()
        r -> Left $ "Invalid kinds as the result types of the proof conclusions: " ++ show r
    unless (M.insert x xTy (functionalContext seq1) == functionalContext seq2) $ Left ("Contexts not equal: " ++ show (functionalContext seq1) ++ " and " ++ show (M.delete x (functionalContext seq2)))
    unless (xTy == goalTerm seq1) $ Left (x ++ " does not have expected type: " ++ show (goalTerm seq1) ++ " got " ++ show xTy)
    return (True)
verifyFunctionalProofM (LambdaRule x p) = do
    (t1) <- verifyFunctionalProofM p
    isTrueP t1 p
    (seq) <- functionalConcl p
    return (M.member x (functionalContext seq))
verifyFunctionalProofM (AppRule p1 p2) = do
    (t1) <- verifyFunctionalProofM p1
    (t2) <- verifyFunctionalProofM p2
    isTrueP t1 p1
    isTrueP t2 p2
    (seq1) <- functionalConcl p1
    (seq2) <- functionalConcl p2
    let validGoalTy = (case goalType seq1 of
            Pi x a b -> a == goalType seq2
            _ -> False)
    if validGoalTy then return (functionalContext seq1 == functionalContext seq2) else Left ("Not a valid goal type: " ++ show (goalType seq1) ++ " Should be equal to: " ++ show (goalType seq2) ++ " in SEQ: " ++ show seq1 ++ ("PROOF: " ++ show p1))
verifyFunctionalProofM (SigmaRule x p1 p2) = do
    (t1) <- verifyFunctionalProofM p1
    (t2) <- verifyFunctionalProofM p2
    isTrueP t1 p1
    isTrueP t2 p2
    (seq1) <- functionalConcl p1
    (seq2) <- functionalConcl p2
    xTy <- case M.lookup x $ functionalContext seq2 of
        Just res -> Right res
        Nothing -> Left $ "Could not find " ++ x ++ " in context of sequent: " ++ show seq2
    case (goalType seq1, goalType seq2) of
        (Type i, Type j) -> return ()
        (Prop, Type j) -> return ()
        (Type i, Prop) -> return ()
        (Prop, Prop) -> return ()
        r -> Left $ "Invalid kinds as the result types of the proof conclusions: " ++ show r
    return (functionalContext seq1 == M.delete x (functionalContext seq2)
            && xTy == goalTerm seq1)
verifyFunctionalProofM (PairRule x p1 p2 p3) = do
    (t1) <- verifyFunctionalProofM p1
    (t2) <- verifyFunctionalProofM p2
    (t3) <- verifyFunctionalProofM p3
    isTrueP t1 p1
    isTrueP t2 p2
    isTrueP t3 p3
    (seq1) <- functionalConcl p1
    (seq2) <- functionalConcl p2
    (seq3) <- functionalConcl p3
    _ <- case goalType seq3 of
        Type j -> return ()
        _ -> Left "Invalid conclusion in third proof for PairRule application. Expected Type_j."
    xTy <- case M.lookup x (functionalContext seq3) of
        Just res -> return res
        _ -> Left $ "Could not find " ++ x ++ " in context of sequent: " ++ show seq3
    let p2ExpectedTy = functionalSubst (goalTerm seq3) (goalTerm seq1) x
        p2ValidTy = goalType seq2 == p2ExpectedTy
    return (p2ValidTy
        && xTy == goalType seq1
        && functionalContext seq1 == functionalContext seq2
        && functionalContext seq2 == M.delete x (functionalContext seq3))
verifyFunctionalProofM (Proj1Rule p) = do
    (t) <- verifyFunctionalProofM p
    isTrueP t p
    (seq) <- functionalConcl p
    case goalType seq of
        Sigma x a b -> return (True)
        _ -> Left $ "Invalid conclusion in derivation for Proj1Rule. Expected Sigma, but got: " ++ show (goalType seq)
verifyFunctionalProofM (Proj2Rule p) = do
    (t) <- verifyFunctionalProofM p
    isTrueP t p
    (seq) <- functionalConcl p
    case goalType seq of
        Sigma x a b -> return (True)
        _ -> Left $ "Invalid conclusion in derivation for Proj2Rule. Expected Sigma, but got: " ++ show (goalType seq)
verifyFunctionalProofM (CumulativiyRule p1 p2) = do
    (t1) <- verifyFunctionalProofM p1
    (t2) <- verifyFunctionalProofM p2
    isTrueP t1 p1
    isTrueP t2 p2
    (seq1) <- functionalConcl p1
    (seq2) <- functionalConcl p2
    return (cumulativiyRelation (goalType seq1) (goalTerm seq2))
-- verifyFunctionalProofM (FHoleRule fc gt gTy) av = return (False, av)
        
verifyFunctionalProof :: FunctionalProof -> Bool
verifyFunctionalProof p =  case verifyFunctionalProofM p of
    Right (True) -> True
    _ -> False

extractFunctionalTerm :: FunctionalProof -> Maybe FunctionalTerm
extractFunctionalTerm t = case (verifyFunctionalProofM t) of
    (Right (True)) -> case functionalConcl t of
            Right (seq) -> return $ goalTerm seq
            _ -> Nothing
    _ -> Nothing

{-| Initialize the first depth of dependencies in the context.
Not really used or tested, but might be useful in the future.-}
initializeDeps :: FunctionalContext -> [(String, S.Set String)]
initializeDeps ctx = (\(x, a) -> (x, functionalFreeVariables a)) <$> M.toList ctx

{-| Get the dependencies for the type of a variable in a context.
Not really used or tested, but might be useful in the future.

>>> assignDeps "x" (M.fromList [("x", Prop)])
fromList []

>>> assignDeps "x" (M.fromList [("y", Var "Z"), ("x", (Var "y"))])
fromList ["Z","y"]
-}
assignDeps :: String -> FunctionalContext -> S.Set String
assignDeps x ctx = case M.lookup x ctx of
    Just res -> let
        curDeps = functionalFreeVariables res
        nextDeps = S.unions (S.map (\v -> assignDeps v ctx) (curDeps))
        in curDeps `S.union` nextDeps
    Nothing -> S.empty

{-| Orders a context by dependencies. Front will depend on most things. Back will depend on least things.
>>> orderCtxDep ([("B", Type 0), ("y", (Var "B")), ("x", (Var "A")), ("A", Prop)])
[("y",B),("B",Type 0),("x",A),("A",Prop)]
-}
orderCtxDep :: FunctionalContext -> [(String, FunctionalTerm)]
orderCtxDep ctx = let
    deps = M.mapWithKey (\k v -> assignDeps k ctx) ctx
    in [] -- TODO

contextFreeVariables :: FunctionalContext -> S.Set String
contextFreeVariables ctx = S.unions $ M.map functionalFreeVariables ctx

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
extractProofFromTermUnderCtx :: FunctionalContext -> FunctionalTerm -> Either String FunctionalProof
extractProofFromTermUnderCtx ctx (Type i) = TRule i <$> extractProofFromTermUnderCtx ctx Prop
extractProofFromTermUnderCtx ctx Prop = return (FunctionalAxiom ctx)
extractProofFromTermUnderCtx ctx (Var x) = do
    ty <- case M.lookup x ctx of
        Just res -> Right res
        Nothing -> Left $ "Could not find " ++ x ++ " in context: " ++ show ctx
    VarRule x <$> extractProofFromTermUnderCtx (M.delete x ctx) ty
extractProofFromTermUnderCtx ctx (Pi a ty t) = do
    tP <- extractProofFromTermUnderCtx (M.insert a ty ctx) t
    tyP <- extractProofFromTermUnderCtx ctx ty
    (tPConcl) <- functionalConcl tP
    return $ PiRule a tyP tP
extractProofFromTermUnderCtx ctx (Lambda a ty t) = do
    tP <- extractProofFromTermUnderCtx (M.insert a ty ctx) t
    return $ LambdaRule a tP
extractProofFromTermUnderCtx ctx (App t1 t2) = do
    p1 <- extractProofFromTermUnderCtx ctx t1
    p2 <- extractProofFromTermUnderCtx ctx t2
    return (AppRule p1 p2)
extractProofFromTermUnderCtx ctx (Sigma x a b) = do
    tyP <- extractProofFromTermUnderCtx ctx a
    tP <- extractProofFromTermUnderCtx (M.insert x a ctx) b
    return $ SigmaRule x tyP tP
extractProofFromTermUnderCtx ctx (Pair m n x a b) = do
    mProof <- extractProofFromTermUnderCtx ctx m
    nProof <- extractProofFromTermUnderCtx ctx n
    bProof <- extractProofFromTermUnderCtx (M.insert x a ctx) b
    return $ PairRule x mProof nProof bProof
extractProofFromTermUnderCtx ctx (Proj1 m) = do
    mProof <- extractProofFromTermUnderCtx ctx m
    return $ Proj1Rule mProof
extractProofFromTermUnderCtx ctx (Proj2 m) = do
    mProof <- extractProofFromTermUnderCtx ctx m
    return $ Proj2Rule mProof
-- extractProofFromTermUnderCtx ctx FHoleTerm = return $ FHoleRule ctx FHoleTerm FHoleTerm

{-| Orders the functional context by terms dependent on ones later in the list.

>>> orderFunctionalContext (M.fromList [("nat", Type 1), ("one", (Var "nat")), ("two", (Var "one"))]) []
NOW [("two",Var "one"),("one",Var "nat"),("nat",Type 1)]
-}
orderFunctionalContext :: FunctionalContext -> [(String, FunctionalTerm)] -> [(String, FunctionalTerm)]
orderFunctionalContext fc acc =
    let
        fvs = contextFreeVariables fc
        nextItemsMap = M.filterWithKey (\k v -> not (k `S.member` fvs)) fc
        newCtx = M.difference fc nextItemsMap
        nextItems = M.toList nextItemsMap
    in
        if fc == M.empty then acc else orderFunctionalContext newCtx (acc ++ nextItems)

{-| P{x/u} replace free occurances of u with x in P.
>>> substVarFunctional (Lambda "x" (Var "y") (Var "x")) "z" "x"
Lambda "x" (Var "y") (Var "x")

>>> substVarFunctional (Lambda "x" (Var "y") (Var "x")) "x" "y"
Lambda "a" (Var "x") (Var "a")
-}
substVarFunctional :: FunctionalTerm -> String -> String -> FunctionalTerm
substVarFunctional t x = functionalSubst t (Var x)

implication :: String -> FunctionalTerm -> FunctionalTerm -> FunctionalTerm
implication sfx = Pi ("_" ++ sfx)

sigma :: String -> String -> FunctionalTerm -> FunctionalTerm -> FunctionalTerm
sigma sfx x a b = Pi "_c" Prop (implication sfx (Pi x a (implication sfx b (Var "_c"))) (Var "_c"))
