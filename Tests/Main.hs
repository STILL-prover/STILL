module Main where

import Tests.Harness
import qualified Tests.ECC.AlphaEquivSpec       as EAlpha
import qualified Tests.ECC.FreeVarsSpec          as EFree
import qualified Tests.ECC.SubstSpec             as ESubst
import qualified Tests.ECC.AlphaConvertSpec      as EConvert
import qualified Tests.ECC.ConversionSpec        as EConv
import qualified Tests.ECC.VerifyProofSpec       as EVerify
import qualified Tests.SessionTypes.AlphaEquivSpec as SAlpha
import qualified Tests.SessionTypes.FreeNamesSpec  as SFree
import qualified Tests.SessionTypes.SubstSpec      as SSubst
import qualified Tests.SessionTypes.TypeCheckSpec  as SCheck
import qualified Tests.SessionTypes.WellFormedSpec as SWellFormed
import qualified Tests.SessionTypes.CommittedVarsSpec as SCommitted
import qualified Tests.Parser.FTermSpec            as PFTerm
import qualified Tests.Parser.PropositionSpec      as PProp
import qualified Tests.Parser.ProcessSpec          as PProc
import qualified Tests.Integration.Scripts         as IScripts

main :: IO ()
main = do
    ref <- newTestState

    EAlpha.run ref
    EFree.run ref
    ESubst.run ref
    EConvert.run ref
    EConv.run ref
    EVerify.run ref

    SAlpha.run ref
    SFree.run ref
    SSubst.run ref
    SCheck.run ref
    SWellFormed.run ref
    SCommitted.run ref

    PFTerm.run ref
    PProp.run ref
    PProc.run ref

    IScripts.run ref

    finish ref
