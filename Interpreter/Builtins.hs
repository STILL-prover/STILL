module Interpreter.Builtins (applyBuiltin1, applyBuiltin2, builtinType) where

import ECC.Kernel (FunctionalTerm(..))

-- | One-argument builtin reductions. Called only when the argument is in
-- normal form (i.e. conversionStep arg == Nothing).
applyBuiltin1 :: String -> FunctionalTerm -> Maybe FunctionalTerm
applyBuiltin1 "show"   (IntLit n)    = Just (StringLit (show n))
applyBuiltin1 "show"   (StringLit s) = Just (StringLit (show s))
applyBuiltin1 "strlen" (StringLit s) = Just (IntLit (fromIntegral (length s)))
applyBuiltin1 "neg"    (IntLit n)    = Just (IntLit (negate n))
applyBuiltin1 _        _             = Nothing

-- | Two-argument builtin reductions. Called only when both arguments are in
-- normal form.
applyBuiltin2 :: String -> FunctionalTerm -> FunctionalTerm -> Maybe FunctionalTerm
applyBuiltin2 "add"    (IntLit m)    (IntLit n)    = Just (IntLit (m + n))
applyBuiltin2 "sub"    (IntLit m)    (IntLit n)    = Just (IntLit (m - n))
applyBuiltin2 "mul"    (IntLit m)    (IntLit n)    = Just (IntLit (m * n))
applyBuiltin2 "div"    (IntLit m)    (IntLit n)
    | n /= 0                                       = Just (IntLit (m `div` n))
applyBuiltin2 "mod"    (IntLit m)    (IntLit n)
    | n /= 0                                       = Just (IntLit (m `mod` n))
applyBuiltin2 "eq"     (IntLit m)    (IntLit n)    = Just (IntLit (if m == n then 1 else 0))
applyBuiltin2 "eq"     (StringLit a) (StringLit b) = Just (IntLit (if a == b then 1 else 0))
applyBuiltin2 "lt"     (IntLit m)    (IntLit n)    = Just (IntLit (if m < n  then 1 else 0))
applyBuiltin2 "le"     (IntLit m)    (IntLit n)    = Just (IntLit (if m <= n then 1 else 0))
applyBuiltin2 "concat" (StringLit a) (StringLit b) = Just (StringLit (a ++ b))
applyBuiltin2 _        _             _             = Nothing

-- | The functional type ascribed to each builtin constant. Used by
-- extractProofFromTermUnderCtx to type-check BuiltinFn applications.
builtinType :: String -> Maybe FunctionalTerm
builtinType "add"    = Just $ Pi "_a" IntTy (Pi "_b" IntTy IntTy)
builtinType "sub"    = Just $ Pi "_a" IntTy (Pi "_b" IntTy IntTy)
builtinType "mul"    = Just $ Pi "_a" IntTy (Pi "_b" IntTy IntTy)
builtinType "div"    = Just $ Pi "_a" IntTy (Pi "_b" IntTy IntTy)
builtinType "mod"    = Just $ Pi "_a" IntTy (Pi "_b" IntTy IntTy)
builtinType "eq"     = Just $ Pi "_a" IntTy (Pi "_b" IntTy IntTy)
builtinType "lt"     = Just $ Pi "_a" IntTy (Pi "_b" IntTy IntTy)
builtinType "le"     = Just $ Pi "_a" IntTy (Pi "_b" IntTy IntTy)
builtinType "show"   = Just $ Pi "_a" IntTy StringTy
builtinType "strlen" = Just $ Pi "_a" StringTy IntTy
builtinType "concat" = Just $ Pi "_a" StringTy (Pi "_b" StringTy StringTy)
builtinType "neg"    = Just $ Pi "_a" IntTy IntTy
builtinType _        = Nothing
