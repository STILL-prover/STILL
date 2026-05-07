module Utils.ParTranslation where

import SessionTypes.Kernel (Process(..), Proposition(..), Sequent(..))
import ECC.Kernel (ftToS)
import qualified Data.List as L
import Data.Char (toUpper, toLower)

capitaliseName :: String -> String
capitaliseName []     = []
capitaliseName (c:cs) = toUpper c : cs

-- | Translate a proven STILL theorem to a par language module.
translateToPar :: String -> Process -> Sequent -> String
translateToPar thmName proc seq =
    let capName = capitaliseName thmName
        goal    = goalProposition seq
        tvars   = L.nub (freeTyVars goal)
        tyBase  = propToPar goal
        ty      = if null tvars then tyBase
                  else "<" ++ L.intercalate ", " tvars ++ "> " ++ tyBase
    in  "module " ++ capName ++ "\n\n" ++
        "def " ++ capName ++ " : " ++ ty ++ " = chan " ++ mainCh ++ " {\n" ++
        goTop tvars 1 mainCh proc ++ "\n}\n"
  where mainCh = channel seq

-- | Like 'go', but for the outermost level: prefixes type parameters onto the
-- first Receive on the main channel using Par's combined "z<a0, b0>[x]" syntax.
goTop :: [String] -> Int -> String -> Process -> String
goTop [] n mc p = go n mc p
goTop tvars n mc (Receive x y p) | x == mc =
    ind n ++ mc ++ "<" ++ L.intercalate ", " tvars ++ ">[" ++ y ++ "]\n"
    ++ go n mc p
goTop tvars n mc p = go n mc p

-- | Collect free session type variables from a proposition.
freeTyVars :: Proposition -> [String]
freeTyVars Unit              = []
freeTyVars (TyVar x)         = [parTyVar x]
freeTyVars (Lift _)          = []
freeTyVars (Implication a b) = freeTyVars a ++ freeTyVars b
freeTyVars (Tensor a b)      = freeTyVars a ++ freeTyVars b
freeTyVars (With a b)        = freeTyVars a ++ freeTyVars b
freeTyVars (Plus a b)        = freeTyVars a ++ freeTyVars b
freeTyVars (Replication a)   = freeTyVars a
freeTyVars (Forall2 x a)     = filter (/= x) (freeTyVars a)
freeTyVars (TyNu x a)        = filter (/= x) (freeTyVars a)
freeTyVars (Forall _ _ a)    = freeTyVars a
freeTyVars (Exists _ _ a)    = freeTyVars a
freeTyVars (Exists2 _ a)     = freeTyVars a

-- | Map a STILL type variable name to a Par type parameter name.
-- Lowercases and appends "0" to avoid clashing with process channel variable names.
parTyVar :: String -> String
parTyVar x = map toLower x ++ "0"

-- | Translate a STILL proposition to a Par session type annotation.
propToPar :: Proposition -> String
propToPar Unit             = "!"
propToPar (TyVar x)        = parTyVar x
propToPar (Lift t)         = ftToS t
propToPar (Implication a b) = "[" ++ propToPar a ++ "] " ++ propToPar b
propToPar (Tensor a b)     = "(" ++ propToPar a ++ ") " ++ propToPar b
propToPar (With a b)       = "choice { .inl => " ++ propToPar a ++ " .inr => " ++ propToPar b ++ " }"
propToPar (Plus a b)       = "either { .inl " ++ propToPar a ++ " .inr " ++ propToPar b ++ " }"
propToPar (Replication a)  = "!" ++ propToPar a
propToPar (Forall2 x a)    = "<" ++ x ++ "> " ++ propToPar a
propToPar (TyNu x a)       = propToPar a
propToPar _                = "/* unsupported */"

-- | Recursively translate a pi-calculus process to par process syntax.
-- mc = name of the currently active goal channel (used to emit mc! for Halt).
go :: Int -> String -> Process -> String
go n mc Halt                    = ind n ++ mc ++ "!"
go n mc (Link x y)
    | y == mc   = ind n ++ mc ++ " <> " ++ x
    | otherwise = ind n ++ x  ++ " <> " ++ y
go n mc (LiftTerm x t)         = ind n ++ x ++ " <> " ++ ftToS t
go n mc HoleTerm               = ind n ++ "_ // hole"
go n mc (Call x zs)            = ind n ++ "loop // " ++ x ++ "(" ++ joinArgs zs ++ ")"

-- Sequential prefix cases
go n mc (Send x v p)           = ind n ++ x ++ "(" ++ v ++ ")\n"            ++ go n mc p
go n mc (SendTerm x t p)       = ind n ++ x ++ "(" ++ ftToS t ++ ")\n"      ++ go n mc p
go n mc (SendType x _ty p)     = ind n ++ x ++ "(/* type */)\n"               ++ go n mc p
go n mc (Receive x y p)        = ind n ++ x ++ "[" ++ y ++ "]\n"            ++ go n mc p
go n mc (SendInl x p)          = ind n ++ x ++ ".inl\n"                     ++ go n mc p
go n mc (SendInr x p)          = ind n ++ x ++ ".inr\n"                     ++ go n mc p

-- Replicated receive (!A server): loops offering a .next branch or .close
go n mc (ReplicateReceive x y p) =
    ind n ++ x ++ ".begin.case {\n" ++
    ind (n+1) ++ ".next[" ++ y ++ "] =>\n" ++
    go (n+2) mc p ++ "\n" ++
    ind (n+2) ++ x ++ ".loop,\n" ++
    ind (n+1) ++ ".close => " ++ x ++ "!\n" ++
    ind n ++ "}"

-- Branch matching (With-right / Plus-left)
go n mc (Case x p q) =
    ind n ++ x ++ ".case {\n" ++
    ind (n+1) ++ ".inl =>\n" ++ go (n+2) mc p ++ ",\n" ++
    ind (n+1) ++ ".inr =>\n" ++ go (n+2) mc q ++ "\n" ++
    ind n ++ "}"

-- Tensor-right / Implies-left: Nu x _ (Send z x (ParallelComposition p1 p2))
-- p1 provides x (runs inside chan x), z(x) sends x on z, p2 continues.
go n mc (Nu x _ (Send z y (ParallelComposition p1 p2)))
    | x == y =
    ind n ++ "let " ++ x ++ " = chan " ++ x ++ " {\n" ++
    go (n+1) x p1 ++ "\n" ++
    ind n ++ "}\n" ++
    ind n ++ z ++ "(" ++ x ++ ")\n" ++
    go n mc p2

-- Cut: Nu x _ (ParallelComposition p1 p2)
-- p1 is the provider of x (runs inside chan x), p2 is the consumer.
go n mc (Nu x _ (ParallelComposition p1 p2)) =
    ind n ++ "let " ++ x ++ " = chan " ++ x ++ " {\n" ++
    go (n+1) x p1 ++ "\n" ++
    ind n ++ "}\n" ++
    go n mc p2

-- General Nu without parallel (e.g. CopyRule: Nu y (Send u y P))
go n mc (Nu x _ty p) =
    ind n ++ "// nu " ++ x ++ "\n" ++
    go n mc p

-- Standalone parallel (should not arise from proof extraction, but handled safely)
go n mc (ParallelComposition p q) =
    go n mc p ++ "\n" ++ go n mc q

-- Corecursion (νX.A introduction)
go n mc (Corec x ys p zs) =
    ind n ++ "// corec " ++ x ++ "(" ++ joinArgs ys ++ ") with (" ++ joinArgs zs ++ ")\n" ++
    ind n ++ "begin {\n" ++
    go (n+1) mc p ++ "\n" ++
    ind n ++ "}"

ind :: Int -> String
ind n = replicate (n * 2) ' '

joinArgs :: [String] -> String
joinArgs = L.intercalate ", "
