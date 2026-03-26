module Parser.CmdParsers where

import Text.Parsec
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Language (emptyDef)
import Control.Monad.Identity (Identity)
import SessionTypes.Tactics
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as S
import Parser.TermParsers (proposition, fTerm, process)
import Data.Functor ((<&>))
import ECC.Tactics (FunctionalTactic, _FAx, _FVarA, _FVar, _FRepeat, _FAlt, _FThen, _FPi1, _FPi2, _FLambda, _FApp, _FSigma, _FPair, _FProj1, _FProj2, _FCumulativity, _FSimp, _FExactKnown, _FExact, _FSkip)
import Utils.Display (printCommands)
import SessionTypes.Kernel (Proposition)
import ECC.Kernel (FunctionalTerm)
import Data.Char (isSpace)

data Range = Range {
    rangeStart :: SourcePos,
    rangeEnd :: SourcePos
}

data CommandSpan a = CommandSpan {
    spanRange :: Range,
    spanText :: String,
    spanValue :: a
}

data Command = CmdHelp
    | CmdPrintTheorems
    | CmdExtract String
    | CmdSTypeDecl String Proposition
    | CmdAssumption String FunctionalTerm
    | CmdProcessAssumption String Proposition
    | CmdSTypeAssumption String
    | CmdTheorem String [Proposition] Proposition
    | CmdApply Tactic
    | CmdDefer
    | CmdDone

evalCommand :: Command -> ProofState -> ProofState
evalCommand CmdHelp s = s { outputs = printCommands : outputs s }
evalCommand CmdPrintTheorems s = _PrintTheorems s
evalCommand (CmdExtract tName) s = _Extract s tName
evalCommand (CmdSTypeDecl i ty) s = _STypeDecl i ty s
evalCommand (CmdAssumption resI resTy) s = _FAssumption resI resTy s
evalCommand (CmdProcessAssumption resI resTy) s = _PAssumption resI resTy s
evalCommand (CmdSTypeAssumption resI) s = _STypeAssumption resI s
evalCommand (CmdTheorem tName props p) s = _Theorem s props tName p
evalCommand (CmdApply t) s = _Apply s t
evalCommand CmdDefer s = _Defer s
evalCommand CmdDone s = _Done s

-- ==========================================
-- Parser Entry Points
-- ==========================================

parseFileSpans :: String -> String -> Either ParseError (String, [String], [CommandSpan Command])
parseFileSpans fileName content = parse parseFileStructureSpanned fileName content

parseFileStructureSpanned :: Parser (String, [String], [CommandSpan Command])
parseFileStructureSpanned = do
    whiteSpace
    reserved "module"
    moduleName <- identifier
    imps <- option [] parseImports
    reserved "begin"
    cmds <- many cmd
    optional (reserved "end")
    eof
    return (moduleName, imps, cmds)

trimRight :: String -> String
trimRight = reverse . dropWhile isSpace . reverse

withSpan :: Parser a -> Parser (CommandSpan a)
withSpan p = do
    startPos <- getPosition
    startInput <- getInput
    x <- p
    endPos <- getPosition
    endInput <- getInput
    let consumedLen = length startInput - length endInput
        consumed = trimRight (take consumedLen startInput)
    return $ CommandSpan { spanRange = Range startPos endPos, spanText = consumed, spanValue = x }

cmd :: Parser (CommandSpan Command)
cmd = withSpan cmdCore

parseStringCommandSpan :: String -> Either ParseError (CommandSpan Command)
parseStringCommandSpan = parse (whiteSpace >> cmd <* eof) ""

-- Parses a full file: Optional Module Header -> Imports -> Commands
parseFile :: String -> String -> Either ParseError ([String], [ProofState -> ProofState])
parseFile fileName content = parse parseFileStructure fileName content

parseFileStructure :: Parser ([String], [ProofState -> ProofState])
parseFileStructure = do
    whiteSpace
    -- Optional: "module Name where"
    reserved "module"
    moduleName <- identifier
    imps <- option [] parseImports
    reserved "begin"

    -- Body: List of commands
    cmds <- many cmdCore
    eof
    return (imps, (\s -> (s { curModuleName = moduleName })):(evalCommand <$> cmds))

-- Single command parser for REPL
parseStringCommand :: String -> Either ParseError (ProofState -> ProofState)
parseStringCommand s = do
  sp <- parseStringCommandSpan s
  pure (evalCommand (spanValue sp))

-- ==========================================
-- 2. Command Parsers
-- ==========================================

cmdCore :: Parser Command
cmdCore = parseTheorem
  <|> parseTypeDec
  <|> try parseProcessAssumption
  <|> try parseSTypeAssumption
  <|> parseAssumption
  <|> parseProvingCommand
  <|> parseDone
  <|> parseHelp
  <|> parsePrintTheorems
  <|> parseExtract

parseHelp :: Parser Command
parseHelp = do
    reserved "help"
    return CmdHelp

parsePrintTheorems :: Parser Command
parsePrintTheorems = do
    reserved "print_theorems"
    return CmdPrintTheorems

parseExtract :: Parser Command
parseExtract = do
    reserved "extract"
    tName <- identifier
    return $ CmdExtract tName

parseImports :: Parser [String]
parseImports = do
    reserved "imports"
    sepBy identifier whiteSpace

parseTypeDec :: Parser Command
parseTypeDec = do
    reserved "stype"
    i <- identifier
    reservedOp "="
    ty <- quotes proposition
    return (CmdSTypeDecl i ty)

parseAssumption :: Parser Command
parseAssumption = do
    reserved "assume"
    resI <- identifier
    reserved "is"
    resTy <- quotes fTerm
    return (CmdAssumption resI resTy)

parseProcessAssumption :: Parser Command
parseProcessAssumption = do
    reserved "assume"
    reserved "process"
    resI <- identifier
    reserved "is"
    resTy <- quotes proposition
    return (CmdProcessAssumption resI resTy)

parseSTypeAssumption :: Parser Command
parseSTypeAssumption = do
    reserved "assume"
    resI <- identifier
    reserved "is"
    reserved "stype"
    return (CmdSTypeAssumption resI)

parseTheorem :: Parser Command
parseTheorem = do
    reserved "theorem"
    tName <- identifier
    props <- option [] (reserved "consumes" >> sepBy (quotes proposition) whiteSpace)
    reservedOp ":"
    p <- quotes proposition
    return (CmdTheorem tName props p)

parseProvingCommand :: Parser Command
parseProvingCommand = parseApply
    <|> parseDefer

parseApply :: Parser Command
parseApply = do
    reserved "apply"
    t <- parseTacticExpression
    return (CmdApply t)

parseDefer = do
    reserved "defer"
    return CmdDefer

parseDone :: Parser Command
parseDone = do
    reserved "done"
    return CmdDone

-- ==========================================
-- 3. Tactic Parsers
-- ==========================================

parseTacticExpression :: Parser (Tactic)
parseTacticExpression = Ex.buildExpressionParser table parseTacticAtom
  where
    table = [[Ex.Postfix (do { reservedOp "+"; return _Repeat})],
        [Ex.Infix (do {reservedOp "<|>"; return _Alt}) Ex.AssocLeft],
        [Ex.Infix (do { reservedOp ";"; return _Then }) Ex.AssocLeft]]

parseTacticAtom :: Parser (Tactic)
parseTacticAtom = parens parseTacticExpression
    <|> parseSimpleTactics
    <|> parseSingleStringArgTactics
    <|> parseCopyTac
    <|> parseForall2L
    <|> parseExists2R
    <|> parseCut
    <|> parseCutRepl
    <|> parseNuR
    <|> parseTyVar
    <|> parseByProc
    <|> (_FTac <$> parseFunctionalTacticsExpression)

parseFunctionalTacticsExpression :: Parser (FunctionalTactic)
parseFunctionalTacticsExpression = Ex.buildExpressionParser table parseFunctionalTacticAtom
  where
    table = [[Ex.Postfix (do { reservedOp "+"; return _FRepeat})],
        [Ex.Infix (do {reservedOp "<|>"; return _FAlt}) Ex.AssocLeft],
        [Ex.Infix (do { reservedOp ";"; return _FThen }) Ex.AssocLeft]]

parseFunctionalTacticAtom :: Parser (FunctionalTactic)
parseFunctionalTacticAtom = parens parseFunctionalTacticsExpression
    <|> parseSimpleFunctionalTactics
    <|> parseSingleStringArgFunctionalTactics
    <|> parsePi1
    <|> parsePi2
    <|> parseApp
    <|> parseSigma
    <|> parsePair
    <|> parseProj1
    <|> parseProj2
    <|> parseCummulativity
    <|> parseSimp
    <|> parseExact

parseSimpleTactics :: Parser (Tactic)
parseSimpleTactics = choice $ (\(name, func) -> reserved name >> return func) <$> simpleTactics

parseSimpleFunctionalTactics :: Parser (FunctionalTactic)
parseSimpleFunctionalTactics = choice $ (\(name, func) -> reserved name >> return func) <$> simpleFunctionalTactics

parseSingleStringArgTactics :: Parser (Tactic)
parseSingleStringArgTactics = choice $ (\(name, f) -> (reserved name >> identifier) <&> f) <$> singleStringArgTactics

parseSingleStringArgFunctionalTactics :: Parser (FunctionalTactic)
parseSingleStringArgFunctionalTactics = choice $ (\(name, f) -> (reserved name >> identifier) <&> f) <$> singleStringArgFunctionalTactics

simpleTactics :: [(String, Tactic)]
simpleTactics =
    [ ("IdA", idATac)
    , ("LiftLA", functionalTermLeftTacA)
    , ("ImpliesR", impliesRightTac)
    , ("ImpliesLA", impliesLeftTacA)
    , ("UnitR", unitRightTac)
    , ("UnitLA", unitLeftTacA)
    , ("BangR", replicationRightTac)
    , ("BangLA", replicationLeftTacA)
    , ("WithR", withRightTac)
    , ("WithL1A", withLeft1TacA)
    , ("WithL2A", withLeft2TacA)
    , ("TensorR", tensorRightTac)
    , ("TensorLA", tensorLeftTacA)
    , ("PlusR1", plusRight1Tac)
    , ("PlusR2", plusRight2Tac)
    , ("PlusLA", plusLeftTacA)
    , ("ForallR", forallRightTac)
    , ("ExistsR", _ExistsR)
    , ("ExistsLA", existsLeftTacA)
    , ("Forall2R", forallRight2Tac)
    , ("Exists2LA", existsLeft2TacA)
    , ("ForallLA", _ForallLA)
    , ("FTermR", _FTermR)
    , ("FTermLA", _FTermLA)
    , ("NuLA", nuLeftTacA)
    , ("Intros", _Intros)
    , ("Skip", _Skip)
    ]

singleStringArgTactics :: [(String, String -> Tactic)]
singleStringArgTactics =
    [ ("Id", _Id)
    , ("TensorL", tensorLeftTac S.empty)
    , ("ImpliesL", impliesLeftTac S.empty)
    , ("UnitL", unitLeftTac S.empty)
    , ("LiftL", functionalTermLeftTac S.empty)
    , ("BangL", replicationLeftTac S.empty)
    , ("WithL1", withLeft1Tac S.empty)
    , ("WithL2", withLeft2Tac S.empty)
    , ("PlusL", plusLeftTac S.empty)
    , ("NuL", nuLeftTac S.empty)
    , ("ExistsL", existsLeftTac S.empty)
    , ("Exists2L", existsLeft2Tac S.empty)
    , ("ForallL", _ForallL)
    , ("FTermL", _FTermL)
    , ("Weaken", _Weaken)
    , ("CutTheorem", cutLinearTheoremTac)
    , ("CutProc", cutProcessAssumptionTac)
    ]

simpleFunctionalTactics :: [(String, FunctionalTactic)]
simpleFunctionalTactics = [("Ax", _FAx)
    --, ("WF", _FWF)
    , ("VarA", _FVarA)
    , ("Lambda", _FLambda)
    , ("FSkip", _FSkip)]

singleStringArgFunctionalTactics :: [(String, String -> FunctionalTactic)]
singleStringArgFunctionalTactics = [("Var", _FVar)]

parseCopyTac :: Parser (Tactic)
parseCopyTac = do
    reserved "Copy"
    a <- identifier
    b <- optionMaybe identifier
    return (_Copy a b)

parseForall2L :: Parser (Tactic)
parseForall2L = do
    reserved "Forall2L"
    a <- identifier
    b <- quotes proposition
    return (_Forall2L a b)

parseExists2R :: Parser (Tactic)
parseExists2R = do
    reserved "Exists2R"
    b <- quotes proposition
    return (_Exists2R b)

parseCut :: Parser (Tactic)
parseCut = do
    reserved "Cut"
    b <- quotes proposition
    return (_Cut b)

parseCutRepl :: Parser (Tactic)
parseCutRepl = do
    reserved "CutRepl"
    b <- quotes proposition
    return (_CutRepl b)

parseNuR :: Parser (Tactic)
parseNuR = do
    reserved "NuR"
    a <- identifier
    bs <- parens $ commaSep identifier
    cs <- parens $ commaSep identifier
    return (_NuR a bs cs)

parseTyVar :: Parser (Tactic)
parseTyVar = do
    reserved "TyVar"
    a <- identifier
    bs <- parens $ commaSep identifier
    return (_TyVar a bs)

parseByProc = do
    reserved "ExactPi"
    byProcessTac <$> quotes process

-- ==========================================
-- Complex functional tactics
-- ==========================================

parsePi1 :: Parser (FunctionalTactic)
parsePi1 = do
    reserved "PiProp"
    a <- optionMaybe $ quotes fTerm
    return (_FPi1 a)

parsePi2 :: Parser (FunctionalTactic)
parsePi2 = do
    reserved "Pi"
    a <- optionMaybe $ quotes fTerm
    return (_FPi2 a)

parseApp :: Parser (FunctionalTactic)
parseApp = do
    reserved "App"
    a <- identifier
    b <- quotes fTerm
    c <- optionMaybe $ quotes fTerm
    return (_FApp a b c)

parseSigma :: Parser (FunctionalTactic)
parseSigma = do
    reserved "Sigma"
    a <- optionMaybe $ quotes fTerm
    return (_FSigma a)

parsePair :: Parser (FunctionalTactic)
parsePair = do
    reserved "Pair"
    a <- optionMaybe $ quotes fTerm
    b <- optionMaybe $ quotes fTerm
    _FPair a b <$> integer

parseProj1 :: Parser (FunctionalTactic)
parseProj1 = do
    reserved "Proj1"
    a <- identifier
    _FProj1 a <$> quotes fTerm

parseProj2 :: Parser (FunctionalTactic)
parseProj2 = do
    reserved "Proj2"
    a <- identifier
    b <- quotes fTerm
    _FProj2 a b <$> optionMaybe (quotes fTerm)

parseCummulativity :: Parser (FunctionalTactic)
parseCummulativity = do
    reserved "Cummulativity"
    a <- quotes fTerm
    _FCumulativity a <$> integer

parseSimp :: Parser (FunctionalTactic)
parseSimp = do
    reserved "Simp"
    i <- optionMaybe integer
    return $ case i of Nothing -> _FSimp 100; Just n -> _FSimp n

parseExact :: Parser (FunctionalTactic)
parseExact = do
    reserved "Exact"
    a <- optionMaybe $ quotes fTerm
    return $ maybe _FExactKnown _FExact a

-- ==========================================
-- Lexer
-- ==========================================

lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser style
  where
    ops = [":", "\"", ";", "+", "<|>"]
    names = ["module", "imports", "begin", "end", "theorem", "done", "defer", "prefer", "apply", "help", "print_theorems", "consumes", "extract", "assume", "process"] ++ (fst <$> simpleTactics)
    style = emptyDef
        { Tok.commentLine = "--"
        , Tok.commentStart = "{-"
        , Tok.commentEnd = "-}"
        , Tok.reservedOpNames = ops
        , Tok.opLetter = oneOf "|>"
        , Tok.reservedNames = names
        , Tok.identStart = letter
        , Tok.identLetter = alphaNum <|> char '_' <|> char '\''
        }

integer    = Tok.integer lexer
identifier = Tok.identifier lexer
parens     = Tok.parens lexer
reserved   = Tok.reserved lexer
reservedOp = Tok.reservedOp lexer
whiteSpace = Tok.whiteSpace lexer
braces     = Tok.braces lexer
quotes     = between (reservedOp "\"") (reservedOp "\"")
commaSep   = Tok.commaSep lexer
