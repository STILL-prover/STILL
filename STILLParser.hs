module STILLParser where

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
import PropParser (proposition, fTerm)
import Data.Functor ((<&>))
import ECC.Tactics (FunctionalTactic, _FAx, _FVarA, _FVar, _FRepeat, _FAlt, _FThen, _FPi, _FLambda, _FApp, _FSigma, _FPair, _FProj1, _FProj2, _FCumulativity, _FSimp, _FExactKnown, _FExact, _FSkip)
import DisplayUtil (printCommands)

-- ==========================================
-- 1. Parser Entry Points
-- ==========================================

-- Parses a full file: Optional Module Header -> Imports -> Commands
parseFile :: String -> String -> Either ParseError ([String], [ProofState Identity -> ProofState Identity])
parseFile fileName content = parse parseFileStructure fileName content

parseFileStructure :: Parser ([String], [ProofState Identity -> ProofState Identity])
parseFileStructure = do
    whiteSpace
    -- Optional: "module Name where"
    reserved "module"
    moduleName <- identifier
    imps <- option [] parseImports
    reserved "begin"

    -- Body: List of commands
    cmds <- many cmd
    eof
    return (imps, (\s -> (s { curModuleName = moduleName })):cmds)

-- Single command parser for REPL
parseStringCommand :: String -> Either ParseError (ProofState Identity -> ProofState Identity)
parseStringCommand = parse (whiteSpace >> cmd <* eof) ""

-- ==========================================
-- 2. Command Parsers
-- ==========================================

cmd :: Parser (ProofState Identity -> ProofState Identity)
cmd = parseTheorem
  <|> parseTypeDec
  <|> try (parseProcessAssumption)
  <|> parseAssumption
  <|> parseProvingCommand
  <|> parseDone
  <|> parseHelp
  <|> parsePrintTheorems
  <|> parseExtract

parseHelp :: Parser (ProofState Identity -> ProofState Identity)
parseHelp = do
    reserved "help"
    return (\s -> s { outputs = printCommands:outputs s})

parsePrintTheorems :: Parser (ProofState Identity -> ProofState Identity)
parsePrintTheorems = do
    reserved "print_theorems"
    return _PrintTheorems

parseExtract :: Parser (ProofState Identity -> ProofState Identity)
parseExtract = do
    reserved "extract"
    tName <- identifier
    return (\s -> _Extract s tName)

parseImports :: Parser [String]
parseImports = do
    reserved "imports"
    sepBy identifier whiteSpace

parseTypeDec :: Parser (ProofState Identity -> ProofState Identity)
parseTypeDec = do
    reserved "stype"
    i <- identifier
    reservedOp "="
    ty <- quotes proposition
    return (_STypeDecl i ty)

parseAssumption :: Parser (ProofState Identity -> ProofState Identity)
parseAssumption = do
    reserved "assume"
    resI <- identifier
    reserved "is"
    resTy <- quotes fTerm
    return (_FAssumption resI resTy)

parseProcessAssumption :: Parser (ProofState Identity -> ProofState Identity)
parseProcessAssumption = do
    reserved "assume"
    reserved "process"
    resI <- identifier
    reserved "is"
    resTy <- quotes proposition
    return (_PAssumption resI resTy)

parseTheorem :: Parser (ProofState Identity -> ProofState Identity)
parseTheorem = do
    reserved "theorem"
    tName <- identifier
    props <- option [] (reserved "consumes" >> sepBy (quotes proposition) whiteSpace)
    reservedOp ":"
    p <- quotes proposition
    return (\s -> _Theorem s props tName p)

parseProvingCommand :: Parser (ProofState Identity -> ProofState Identity)
parseProvingCommand = parseApply
    <|> parseDefer

parseApply :: Parser (ProofState Identity -> ProofState Identity)
parseApply = do
    reserved "apply"
    t <- parseTacticExpression
    return (`_Apply` t)

parseDefer = do
    reserved "defer"
    return _Defer

parseDone :: Parser (ProofState Identity -> ProofState Identity)
parseDone = do
    reserved "done"
    return _Done

-- ==========================================
-- 3. Tactic Parsers
-- ==========================================

parseTacticExpression :: Parser (Tactic Identity)
parseTacticExpression = Ex.buildExpressionParser table parseTacticAtom
  where
    table = [[Ex.Postfix (do { reservedOp "+"; return _Repeat})],
        [Ex.Infix (do {reservedOp "<|>"; return _Alt}) Ex.AssocLeft],
        [Ex.Infix (do { reservedOp ";"; return _Then }) Ex.AssocLeft]]

parseTacticAtom :: Parser (Tactic Identity)
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
    <|> (_FTac <$> parseFunctionalTacticsExpression)

parseFunctionalTacticsExpression :: Parser (FunctionalTactic Identity)
parseFunctionalTacticsExpression = Ex.buildExpressionParser table parseFunctionalTacticAtom
  where
    table = [[Ex.Postfix (do { reservedOp "+"; return _FRepeat})],
        [Ex.Infix (do {reservedOp "<|>"; return _FAlt}) Ex.AssocLeft],
        [Ex.Infix (do { reservedOp ";"; return _FThen }) Ex.AssocLeft]]

parseFunctionalTacticAtom :: Parser (FunctionalTactic Identity)
parseFunctionalTacticAtom = parens parseFunctionalTacticsExpression
    <|> parseSimpleFunctionalTactics
    <|> parseSingleStringArgFunctionalTactics
    <|> parsePi
    <|> parseApp
    <|> parseSigma
    <|> parsePair
    <|> parseProj1
    <|> parseProj2
    <|> parseCummulativity
    <|> parseSimp
    <|> parseExact

parseSimpleTactics :: Parser (Tactic Identity)
parseSimpleTactics = choice $ (\(name, func) -> reserved name >> return func) <$> simpleTactics

parseSimpleFunctionalTactics :: Parser (FunctionalTactic Identity)
parseSimpleFunctionalTactics = choice $ (\(name, func) -> reserved name >> return func) <$> simpleFunctionalTactics

parseSingleStringArgTactics :: Parser (Tactic Identity)
parseSingleStringArgTactics = choice $ (\(name, f) -> (reserved name >> identifier) <&> f) <$> singleStringArgTactics

parseSingleStringArgFunctionalTactics :: Parser (FunctionalTactic Identity)
parseSingleStringArgFunctionalTactics = choice $ (\(name, f) -> (reserved name >> identifier) <&> f) <$> singleStringArgFunctionalTactics

simpleTactics :: [(String, Tactic Identity)]
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

singleStringArgTactics :: [(String, String -> Tactic Identity)]
singleStringArgTactics =
    [ ("Id", _Id)
    , ("TensorL", tensorLeftTac)
    , ("ImpliesL", impliesLeftTac)
    , ("UnitL", unitLeftTac)
    , ("LiftL", functionalTermLeftTac)
    , ("BangL", replicationLeftTac)
    , ("WithL1", withLeft1Tac)
    , ("WithL2", withLeft2Tac)
    , ("PlusL", plusLeftTac)
    , ("NuL", nuLeftTac)
    , ("ExistsL", existsLeftTac)
    , ("Exists2L", existsLeft2Tac)
    , ("ForallL", _ForallL)
    , ("FTermL", _FTermL)
    , ("Weaken", _Weaken)
    , ("CutTheorem", cutLinearTheoremTac)
    , ("CutProc", cutProcessAssumptionTac)
    ]

simpleFunctionalTactics :: [(String, FunctionalTactic Identity)]
simpleFunctionalTactics = [("Ax", _FAx)
    --, ("WF", _FWF)
    , ("VarA", _FVarA)
    , ("Lambda", _FLambda)
    , ("FSkip", _FSkip)]

singleStringArgFunctionalTactics :: [(String, String -> FunctionalTactic Identity)]
singleStringArgFunctionalTactics = [("Var", _FVar)]

parseCopyTac :: Parser (Tactic Identity)
parseCopyTac = do
    reserved "Copy"
    a <- identifier
    b <- optionMaybe identifier
    return (_Copy a b)

parseForall2L :: Parser (Tactic Identity)
parseForall2L = do
    reserved "Forall2L"
    a <- identifier
    b <- quotes proposition
    return (_Forall2L a b)

parseExists2R :: Parser (Tactic Identity)
parseExists2R = do
    reserved "Exists2R"
    b <- quotes proposition
    return (_Exists2R b)

parseCut :: Parser (Tactic Identity)
parseCut = do
    reserved "Cut"
    b <- quotes proposition
    return (_Cut b)

parseCutRepl :: Parser (Tactic Identity)
parseCutRepl = do
    reserved "CutRepl"
    b <- quotes proposition
    return (_CutRepl b)

parseNuR :: Parser (Tactic Identity)
parseNuR = do
    reserved "NuR"
    a <- identifier
    bs <- parens $ sepBy identifier (reservedOp ",")
    cs <- parens $ sepBy identifier (reservedOp ",")
    return (_NuR a bs cs)

parseTyVar :: Parser (Tactic Identity)
parseTyVar = do
    reserved "TyVar"
    a <- identifier
    bs <- parens $ sepBy identifier (reservedOp ",")
    return (_TyVar a bs)

-- ==========================================
-- Complex functional tactics
-- ==========================================

parsePi :: Parser (FunctionalTactic Identity)
parsePi = do
    reserved "Pi"
    a <- optionMaybe $ quotes fTerm
    return (_FPi a)

parseApp :: Parser (FunctionalTactic Identity)
parseApp = do
    reserved "App"
    a <- identifier
    b <- quotes fTerm
    c <- optionMaybe $ quotes fTerm
    return (_FApp a b c)

parseSigma :: Parser (FunctionalTactic Identity)
parseSigma = do
    reserved "Sigma"
    a <- optionMaybe $ quotes fTerm
    return (_FSigma a)

parsePair :: Parser (FunctionalTactic Identity)
parsePair = do
    reserved "Pair"
    a <- optionMaybe $ quotes fTerm
    b <- optionMaybe $ quotes fTerm
    _FPair a b <$> integer

parseProj1 :: Parser (FunctionalTactic Identity)
parseProj1 = do
    reserved "Proj1"
    a <- identifier
    _FProj1 a <$> quotes fTerm

parseProj2 :: Parser (FunctionalTactic Identity)
parseProj2 = do
    reserved "Proj2"
    a <- identifier
    b <- quotes fTerm
    _FProj2 a b <$> optionMaybe (quotes fTerm)

parseCummulativity :: Parser (FunctionalTactic Identity)
parseCummulativity = do
    reserved "Cummulativity"
    a <- quotes fTerm
    _FCumulativity a <$> integer

parseSimp :: Parser (FunctionalTactic Identity)
parseSimp = do
    reserved "Simp"
    i <- optionMaybe integer
    return $ case i of Nothing -> _FSimp 100; Just n -> _FSimp n

parseExact :: Parser (FunctionalTactic Identity)
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
