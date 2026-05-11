module Tests.ECC.AlphaConvertSpec (run) where

import Tests.Harness
import ECC.Kernel
import qualified Data.Set as S
import Data.IORef

run :: IORef TestState -> IO ()
run ref = group ref "ECC.alphaConvert + functionalRename + substVarFunctional" $ do

    -- functionalRename: naive (not capture-avoiding) rename
    assert ref "rename y->x in Lambda y A y = Lambda x A x"
        (alphaEquivalent
            (functionalRename (Lambda "y" (Var "A") (Var "y")) "x" "y")
            (Lambda "x" (Var "A") (Var "x")))

    assert ref "rename y->r in term not containing y is identity"
        (alphaEquivalent
            (functionalRename (Lambda "y" (Var "A") (Var "y")) "r" "x")
            (Lambda "y" (Var "A") (Var "y")))

    assert ref "rename x->y in Var x = Var y"
        (alphaEquivalent
            (functionalRename (Var "x") "y" "x")
            (Var "y"))

    assert ref "rename x->y in Lambda x A (Var x) = Lambda y A (Var y)"
        (alphaEquivalent
            (functionalRename (Lambda "x" (Var "A") (Var "x")) "y" "x")
            (Lambda "y" (Var "A") (Var "y")))

    assert ref "rename x->y in Pi x A x = Pi y A y"
        (alphaEquivalent
            (functionalRename (Pi "x" (Var "A") (Var "x")) "y" "x")
            (Pi "y" (Var "A") (Var "y")))

    -- alphaConvert: picks a fresh name from alphabetical sequence
    assert ref "alphaConvert (Lambda y A y) {} = Lambda a A a"
        (alphaEquivalent
            (alphaConvert (Lambda "y" (Var "A") (Var "y")) S.empty)
            (Lambda "a" (Var "A") (Var "a")))

    assert ref "alphaConvert (Lambda y A y) {a} = Lambda b A b"
        (alphaEquivalent
            (alphaConvert (Lambda "y" (Var "A") (Var "y")) (S.singleton "a"))
            (Lambda "b" (Var "A") (Var "b")))

    -- alphaConvert on Pi
    assert ref "alphaConvert (Pi y A y) {} = Pi a A a"
        (alphaEquivalent
            (alphaConvert (Pi "y" (Var "A") (Var "y")) S.empty)
            (Pi "a" (Var "A") (Var "a")))

    -- alphaConvert preserves free vars in type position
    assert ref "alphaConvert (Lambda y y y) {a}: type still has Var y (free)"
        (let result = alphaConvert (Lambda "y" (Var "y") (Var "y")) (S.singleton "a")
         in case result of
                Lambda z (Var ty) (Var body) ->
                    ty == "y"   -- original free "y" in type position is preserved
                    && body == z  -- body now uses fresh binder name
                    && z /= "y"   -- the binder was renamed
                _ -> False)

    -- alphaConvert on non-binder term is identity
    assert ref "alphaConvert (Var x) {} = Var x (no-op on non-binder)"
        (alphaEquivalent
            (alphaConvert (Var "x") S.empty)
            (Var "x"))

    -- substVarFunctional: replaces a var name with another var name
    assert ref "substVarFunctional (Lambda x y x) z y = Lambda x z x"
        (alphaEquivalent
            (substVarFunctional (Lambda "x" (Var "y") (Var "x")) "z" "y")
            (Lambda "x" (Var "z") (Var "x")))

    -- substVarFunctional capture avoidance
    assert ref "substVarFunctional (Lambda x y x) x y avoids capture (renames binder)"
        (let result = substVarFunctional (Lambda "x" (Var "y") (Var "x")) "x" "y"
         in case result of
                Lambda binder (Var ty) _ ->
                    binder /= "x"  -- binder was renamed to avoid capturing x
                    && ty == "x"   -- type now contains the substituted x
                _ -> False)
