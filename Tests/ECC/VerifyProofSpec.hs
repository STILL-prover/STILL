module Tests.ECC.VerifyProofSpec (run) where

import Tests.Harness
import ECC.Kernel
import Data.IORef

run :: IORef TestState -> IO ()
run ref = group ref "ECC.verifyFunctionalProofM + extractProofFromTermUnderCtx" $ do

    -- CRule: |- Prop : Type 0
    assertRight ref "CRule emptyContext proves Prop : Type 0"
        (verifyFunctionalProofM (CRule emptyContext))

    -- TRule: |- Type i : Type (i+1)
    assertRight ref "TRule 0 emptyContext proves Type 0 : Type 1"
        (verifyFunctionalProofM (TRule 0 emptyContext))
    assertRight ref "TRule 2 emptyContext proves Type 2 : Type 3"
        (verifyFunctionalProofM (TRule 2 emptyContext))

    -- IntTy, StringTy
    assertRight ref "IntTyRule emptyContext proves Int : Type 0"
        (verifyFunctionalProofM (IntTyRule emptyContext))
    assertRight ref "StringTyRule emptyContext proves String : Type 0"
        (verifyFunctionalProofM (StringTyRule emptyContext))

    -- IntLit, StringLit
    assertRight ref "IntLitRule 42 emptyContext proves 42 : Int"
        (verifyFunctionalProofM (IntLitRule 42 emptyContext))
    assertRight ref "StringLitRule 'hi' emptyContext proves 'hi' : String"
        (verifyFunctionalProofM (StringLitRule "hi" emptyContext))

    -- BuiltinFn
    assertRight ref "BuiltinFnRule 'add' emptyContext proves #add : Int -> Int -> Int"
        (verifyFunctionalProofM (BuiltinFnRule "add" emptyContext))
    assertRight ref "BuiltinFnRule 'mul' emptyContext proves #mul"
        (verifyFunctionalProofM (BuiltinFnRule "mul" emptyContext))
    assertRight ref "BuiltinFnRule 'show' emptyContext proves #show"
        (verifyFunctionalProofM (BuiltinFnRule "show" emptyContext))
    assertLeft ref "BuiltinFnRule 'nonexistent' fails"
        (verifyFunctionalProofM (BuiltinFnRule "nonexistent" emptyContext))

    -- VarRule: requires the variable to be in context
    case safeInsert "x" (Type 1) emptyContext of
        Left err -> assert ref ("safeInsert x:Type1 failed: " ++ err) False
        Right ctx -> do
            assertRight ref "VarRule x in context with x:Type1 succeeds"
                (verifyFunctionalProofM (VarRule "x" ctx))
            assertLeft ref "VarRule y (absent) in context with x:Type1 fails"
                (verifyFunctionalProofM (VarRule "y" ctx))

    -- safeInsert validates the type
    assertRight ref "safeInsert 'x' (Type 0) emptyContext succeeds"
        (safeInsert "x" (Type 0) emptyContext)
    assertRight ref "safeInsert 'x' Prop emptyContext succeeds"
        (safeInsert "x" Prop emptyContext)
    assertRight ref "safeInsert 'x' IntTy emptyContext succeeds"
        (safeInsert "x" IntTy emptyContext)

    -- AppRule: function must have Pi type; TRule proves Type not Pi → fails
    assertLeft ref "AppRule (TRule 0 ctx) (CRule ctx) fails (non-Pi function type)"
        (verifyFunctionalProofM (AppRule (TRule 0 emptyContext) (CRule emptyContext)))

    -- extractProofFromTermUnderCtx round-trips
    assertRight ref "extract Type 1"
        (extractProofFromTermUnderCtx emptyContext (Type 1))

    assertRight ref "extract Prop"
        (extractProofFromTermUnderCtx emptyContext Prop)

    assertRight ref "extract IntTy"
        (extractProofFromTermUnderCtx emptyContext IntTy)

    assertRight ref "extract IntLit 5"
        (extractProofFromTermUnderCtx emptyContext (IntLit 5))

    assertRight ref "extract BuiltinFn add"
        (extractProofFromTermUnderCtx emptyContext (BuiltinFn "add"))

    -- Lambda A:Type1.A  (identity on types)
    let idTy = Lambda "A" (Type 1) (Var "A")
    assertRight ref "extract Lambda A:Type1.A"
        (extractProofFromTermUnderCtx emptyContext idTy)

    -- Lambda A:Type1. Lambda x:A. x  (polymorphic identity)
    let polyId = Lambda "A" (Type 1) (Lambda "x" (Var "A") (Var "x"))
    assertRight ref "extract polymorphic identity Lambda A:Type1.Lambda x:A.x"
        (extractProofFromTermUnderCtx emptyContext polyId)

    -- Pi A:Type1. Type1
    assertRight ref "extract Pi A:Type1.Type1"
        (extractProofFromTermUnderCtx emptyContext (Pi "A" (Type 1) (Type 1)))

    -- Sigma x:Type0. Type0
    assertRight ref "extract Sigma x:Type0.Type0"
        (extractProofFromTermUnderCtx emptyContext (Sigma "x" (Type 0) (Type 0)))

    -- Note: safeInsert does NOT reject shadowed binders — it prepends without uniqueness check.
    -- Lambda x:Type1. Lambda x:(Var x). Var x extracts successfully (inner x shadows outer).
    let shadowedBinder = Lambda "x" (Type 1) (Lambda "x" (Var "x") (Var "x"))
    assertRight ref "extract Lambda x:Type1.Lambda x:Var x.Var x (shadowed binder: inner shadows outer)"
        (extractProofFromTermUnderCtx emptyContext shadowedBinder)

    -- Negative: variable not in context
    assertLeft ref "extract Var 'notInCtx' fails when variable absent"
        (extractProofFromTermUnderCtx emptyContext (Var "notInCtx"))

    -- Negative: applying a non-function
    assertLeft ref "extract App (IntLit 5) (IntLit 3) fails (non-Pi type)"
        (extractProofFromTermUnderCtx emptyContext (App (IntLit 5) (IntLit 3)))

    -- Verify that extracted proof is self-consistent
    case extractProofFromTermUnderCtx emptyContext polyId of
        Left err -> assert ref ("extract polyId failed: " ++ err) False
        Right (_, proof) ->
            assertRight ref "proof from polyId verifies"
                (verifyFunctionalProofM proof)
