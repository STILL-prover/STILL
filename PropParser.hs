module PropParser where

import Text.Parsec
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Language (emptyDef)
import LinearLogic (Proposition(..))
import FunctionalSystem (FunctionalTerm(..))

lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser style
  where
    ops = ["->", ":", ".", ",", "=>", "-o", "*", "&", "+", "!", "_", "$"]
    names = ["Type", "Prop", "fst", "snd", 
             "lambda", "Pi", "Sigma", 
             "Unit", "1", "lift", 
             "forall", "exists", "forall2", "exists2", "nu", "stype"]
    style = emptyDef
        { Tok.commentLine = "--"
        , Tok.commentStart = "{-"
        , Tok.commentEnd = "-}"
        , Tok.reservedOpNames = ops
        , Tok.opLetter = oneOf ">o"
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

-- -----------------------------------------------------------------------------
-- 3. FunctionalTerm Parser
-- -----------------------------------------------------------------------------

-- Entry point for Functional Terms
fTerm :: Parser FunctionalTerm
fTerm = Ex.buildExpressionParser table termAtom
  where
    table = [[Ex.Infix (return App) Ex.AssocLeft]]

termAtom :: Parser FunctionalTerm
termAtom = parens fTerm
       <|> parseType
       <|> parsePropKind
       <|> parseHole
       <|> parseLambda
       <|> parsePi
       <|> parseSigma
       <|> parsePairOrProj -- Handles Pairs, Proj1, Proj2, Var
       <|> (Var <$> identifier)

-- Parses "Type 0", "Type 1", etc.
parseType :: Parser FunctionalTerm
parseType = do
    reserved "Type"
    n <- integer
    return (Type n)

-- Parses "Prop"
parsePropKind :: Parser FunctionalTerm
parsePropKind = reserved "Prop" >> return Prop

-- Parses "_"
parseHole :: Parser FunctionalTerm
parseHole = reservedOp "_" >> return FHoleTerm

-- Parses "\x : A . M" or "lambda x : A . M"
parseLambda :: Parser FunctionalTerm
parseLambda = do
    (reservedOp "\\" <|> reserved "lambda")
    v <- identifier
    reservedOp ":"
    ty <- fTerm
    reservedOp "."
    body <- fTerm
    return (Lambda v ty body)

-- Parses "Pi x : A . B"
parsePi :: Parser FunctionalTerm
parsePi = do
    reserved "Pi"
    v <- identifier
    reservedOp ":"
    ty <- fTerm
    reservedOp "."
    body <- fTerm
    return (Pi v ty body)

-- Parses "Sigma x : A . B"
parseSigma :: Parser FunctionalTerm
parseSigma = do
    reserved "Sigma"
    v <- identifier
    reservedOp ":"
    ty <- fTerm
    reservedOp "."
    body <- fTerm
    return (Sigma v ty body)

-- Handles Pairs and Projections
-- Syntax for Pair: (M, N) : Sigma x:A.B
-- Syntax for Proj: fst M, snd M
parsePairOrProj :: Parser FunctionalTerm
parsePairOrProj = try parseAnnotatedPair <|> parseProjections
  where
    parseProjections = do
        op <- (reserved "fst" >> return Proj1) <|> (reserved "snd" >> return Proj2)
        t <- termAtom
        return (op t)

    parseAnnotatedPair = do
        -- Parses: (M, N) : Sigma x:A.B
        -- Note: We assume parens are handled by the caller or explicit here for the pair structure
        reservedOp "("
        m <- fTerm
        reservedOp ","
        n <- fTerm
        reservedOp ")"
        reservedOp ":" 
        reserved "Sigma"
        x <- identifier
        reservedOp ":"
        a <- fTerm
        reservedOp "."
        b <- fTerm
        return (Pair m n x a b)

-- -----------------------------------------------------------------------------
-- 4. Proposition Parser
-- -----------------------------------------------------------------------------

proposition :: Parser Proposition
proposition = Ex.buildExpressionParser table propAtom
  where
    table = [ [Ex.Prefix (reservedOp "!" >> return Replication)]
            , [Ex.Infix (reservedOp "*" >> return Tensor) Ex.AssocLeft]
            , [Ex.Infix (reservedOp "&" >> return With) Ex.AssocLeft]
            , [Ex.Infix (reservedOp "+" >> return Plus) Ex.AssocLeft]
            , [Ex.Infix (reservedOp "-o" >> return Implication) Ex.AssocRight]
            ]

propAtom :: Parser Proposition
propAtom = parens proposition
       <|> (reserved "Unit" >> return Unit)
       <|> (reserved "1" >> return Unit)
       <|> try parseLift
       <|> parseQuantifiers
       <|> (TyVar <$> identifier)

-- Parses { M } as Lift M
-- parseLift :: Parser Proposition
-- parseLift = do
--     t <- braces fTerm
--     return (Lift t)

parseLift :: Parser Proposition
parseLift = do
    reservedOp "$"
    t <- fTerm
    return (Lift t)

-- Handles forall, exists, forall2, exists2, nu
parseQuantifiers :: Parser Proposition
parseQuantifiers = (try parseForall2) <|> (try parseExists2) <|> parseForall <|> parseExists <|> parseNu

-- forall x : A . P
parseForall :: Parser Proposition
parseForall = do
    reserved "forall"
    v <- identifier
    reservedOp ":"
    ty <- fTerm
    reservedOp "."
    p <- proposition
    return (Forall v ty p)

-- exists x : A . P
parseExists :: Parser Proposition
parseExists = do
    reserved "exists"
    v <- identifier
    reservedOp ":"
    ty <- fTerm
    reservedOp "."
    p <- proposition
    return (Exists v ty p)

-- forall2 X . P (Polymorphism over propositions)
parseForall2 :: Parser Proposition
parseForall2 = do
    reserved "forall"
    v <- identifier
    reservedOp ":"
    reserved "stype"
    reservedOp "."
    p <- proposition
    return (Forall2 v p)

-- exists2 X . P
parseExists2 :: Parser Proposition
parseExists2 = do
    reserved "exists"
    v <- identifier
    reservedOp ":"
    reserved "stype"
    reservedOp "."
    p <- proposition
    return (Exists2 v p)

-- nu X . P
parseNu :: Parser Proposition
parseNu = do
    reserved "nu"
    v <- identifier
    reservedOp "."
    p <- proposition
    return (TyNu v p)

-- -----------------------------------------------------------------------------
-- 5. Helper Functions
-- -----------------------------------------------------------------------------

parseStringTerm :: String -> Either ParseError FunctionalTerm
parseStringTerm = parse (whiteSpace >> fTerm <* eof) ""

parseStringProp :: String -> Either ParseError Proposition
parseStringProp = parse (whiteSpace >> proposition <* eof) ""