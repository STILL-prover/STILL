module STILLParser where

import Text.Parsec
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Language (emptyDef)
import Control.Monad.Identity (Identity)
import Tactics
import Data.List
import Data.Map
import PropParser (proposition)

simpleTactics :: [(String, Tactic Identity)]
simpleTactics = [("TensorR", _TensorR),
    ("ImpliesR", _ImpliesR),
    ("TensorLA", _TensorLA)]

lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser style
  where
    ops = [":", "\""]
    names = ["module", "imports", "begin", "end", "theorem", "done", "defer", "prefer", "apply"] ++ (fst <$> simpleTactics)
    style = emptyDef
        { Tok.commentLine = "--"
        , Tok.commentStart = "{-"
        , Tok.commentEnd = "-}"
        , Tok.reservedOpNames = ops
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
quotes = between (reservedOp "\"") (reservedOp "\"")

-- -----------------------------------------------------------------------------
-- 3. FunctionalTerm Parser
-- -----------------------------------------------------------------------------

-- Entry point for parsing commands
cmd :: Parser (ProofState Identity -> ProofState Identity)
cmd = Ex.buildExpressionParser table commandAtom
  where
    table = []--[[Ex.Infix (return App) Ex.AssocLeft]]

commandAtom :: Parser (ProofState Identity -> ProofState Identity)
commandAtom = parseModule
    --    <|> parsePropKind
    --    <|> parseHole
    --    <|> parseLambda
    --    <|> parsePi
    --    <|> parseSigma
    --    <|> parsePairOrProj -- Handles Pairs, Proj1, Proj2, Var
    --    <|> (Var <$> identifier)

parseModule :: Parser (ProofState Identity -> ProofState Identity)
parseModule = do
    reserved "module"
    mName <- identifier
    modules <- option [] parseImports
    reserved "begin"
    ts <- many parseTheorem
    return (\s -> s { curModuleName = mName, theorems = empty, openGoalStack = [], subgoals = empty, outputs = "Starting module":outputs s })

parseImports :: Parser [String]
parseImports = do
    reserved "imports"
    sepBy identifier whiteSpace

parseTheorem :: Parser (ProofState Identity -> ProofState Identity)
parseTheorem = do
    reserved "theorem"
    tName <- identifier
    reservedOp ":"
    p <- quotes proposition
    many parseProvingCommand
    return (\s -> _Theorem s tName p)

parseProvingCommand :: Parser (ProofState Identity -> ProofState Identity)
parseProvingCommand = parseApply

parseApply :: Parser (ProofState Identity -> ProofState Identity)
parseApply = do
    reserved "apply"
    parseTactic

parseSimpleTactics :: Parser (ProofState Identity -> ProofState Identity)
parseSimpleTactics = choice $ (\et -> reserved (fst et) >> return (\s -> _Apply s (snd et))) <$> simpleTactics

parseTactic :: Parser (ProofState Identity -> ProofState Identity)
parseTactic = parseSimpleTactics

-- -----------------------------------------------------------------------------
-- Parsing String Functions
-- -----------------------------------------------------------------------------

parseStringCommand :: String -> Either ParseError (ProofState Identity -> ProofState Identity)
parseStringCommand = parse (whiteSpace >> cmd <* eof) ""

-- parseStringModuleHeader :: String -> Either ParseError [String]
-- parseStringModuleHeader = parse (whiteSpace >> parseModule <* eof) ""