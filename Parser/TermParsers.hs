module Parser.TermParsers where

import Text.Parsec
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Language (emptyDef)
import SessionTypes.Kernel (Proposition(..), Process (..))
import ECC.Kernel (FunctionalTerm(..))

lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser style
  where
    ops = ["->", ":", ".", ",", "=>", "-o", "*", "&", "+", "!", "_", "$", "\\"]
    names = ["Type", "Prop", "fst", "snd", 
             "Pi", "Sigma", 
             "Unit", "1", "lift", 
             "forall", "exists", "forall2", "exists2", "nu", "stype", "lambda"]
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

commaSep :: Parser a -> Parser [a]
commaSep = Tok.commaSep lexer

-- -----------------------------------------------------------------------------
-- Process Parser
-- -----------------------------------------------------------------------------

process :: Parser Process
process = Ex.buildExpressionParser table processTerm
  where
    -- Parallel composition is the only infix operator here, binding loosely
    table = [[Ex.Infix (reservedOp "|" >> return ParallelComposition) Ex.AssocRight]]

-- Atomic process terms or prefix constructs
processTerm :: Parser Process
processTerm = try (parens process)
          <|> parseHalt
          -- <|> parseHole
          <|> parseProcessNu
          <|> parseLink
          <|> parseProcessLift
          <|> parseCorec
          <|> parseCall
          <|> parseReplicate
          <|> parseAction -- Handles Send, Receive, Select, Case
          <|> try parseCallImplicit -- Fallback for "X(args)" without 'call' keyword if desired

parseHalt :: Parser Process
parseHalt = (reserved "stop" <|> reserved "0") >> return Halt

-- parseHole :: Parser Process
-- parseHole = reservedOp "_" >> return HoleTerm

-- [ x <-> y ]
parseLink :: Parser Process
parseLink = do
    reservedOp "["
    x <- identifier
    reservedOp "<->" <|> reservedOp "Link"
    y <- identifier
    reservedOp "]"
    return (Link x y)

-- nu x : A . P
parseProcessNu :: Parser Process
parseProcessNu = do
    (x, prop) <- parens (do 
        reserved "nu"
        x <- identifier
        reservedOp ":"
        prop <- proposition
        return (x, prop))
    p <- process
    return (Nu x prop p)

-- lift $M
parseProcessLift :: Parser Process
parseProcessLift = do
    reservedOp "["
    -- Expect a term. We use $ to clearly mark entrance into FunctionalTerm 
    -- if it's not a parenthesized term, but fTerm handles parens.
    -- We allow optional $ for clarity: lift $M
    --optional (reservedOp "$")
    z <- identifier
    reservedOp "<-"
    t <- fTerm
    reservedOp "]"
    return (LiftTerm z t)
    
-- Call X(a, b)
parseCall :: Parser Process
parseCall = do
    reserved "call"
    x <- identifier
    args <- parens (commaSep identifier)
    return (Call x args)

parseCallImplicit :: Parser Process
parseCallImplicit = do
    -- X(a,b)
    x <- identifier
    args <- parens (commaSep identifier)
    return (Call x args)

-- corec X(a, b) . P
parseCorec :: Parser Process
parseCorec = do
    reserved "corec"
    name <- identifier
    args <- parens (commaSep identifier)
    reservedOp "."
    p <- process
    -- The Corec type has a second [String] at the end. 
    -- We check if there are trailing arguments or default to empty.
    finalArgs <- option [] (parens (commaSep identifier))
    return (Corec name args p finalArgs)

-- ! x(y) . P
parseReplicate :: Parser Process
parseReplicate = do
    reservedOp "!"
    x <- identifier
    -- Expect input syntax immediately after
    args <- parens identifier
    reservedOp "."
    p <- process
    return (ReplicateReceive x args p)

-- Handles actions starting with an identifier:
-- Send, Receive, Selection, Case
parseAction :: Parser Process
parseAction = do
    subj <- identifier
    parseContinuation subj

parseContinuation :: String -> Parser Process
parseContinuation subj = 
        try (parseOutput subj)
    <|> try (parseInput subj)
    <|> try (parseSelectionOrCase subj)

-- x[...]
parseOutput :: String -> Parser Process
parseOutput subj = do
    reservedOp "["
    res <- parseSendBody
    reservedOp "]"
    reservedOp "."
    p <- process
    return (res subj p)
  where
    parseSendBody = try parseSendType <|> try parseSendTerm <|> parseSendName

    -- [ stype A ]
    parseSendType = do
        reserved "stype"
        prop <- proposition
        return (\s p -> SendType s prop p)

    -- < $M >
    parseSendTerm = do
        reservedOp "$"
        t <- fTerm
        return (\s p -> SendTerm s t p)

    -- < y >
    parseSendName = do
        y <- identifier
        return (\s p -> Send s y p)

-- x(y).P
parseInput :: String -> Parser Process
parseInput subj = do
    y <- parens identifier
    reservedOp "."
    p <- process
    return (Receive subj y p)

-- x.inl, x.inr, x.case
parseSelectionOrCase :: String -> Parser Process
parseSelectionOrCase subj = do
    reservedOp "."
    (do
        reserved "inl"
        reservedOp ";"
        p <- process
        return (SendInl subj p)
     ) <|> (do
        reserved "inr"
        reservedOp ";"
        p <- process
        return (SendInr subj p)
     ) <|> (do
        reserved "case"
        (p, q) <- parens pairProcess
        return (Case subj p q)
     )

pairProcess :: Parser (Process, Process)
pairProcess = do
    reserved "inl"
    reservedOp ":"
    p <- process
    reservedOp ","
    reserved "inr"
    reservedOp ":"
    q <- process
    return (p, q)

-- -----------------------------------------------------------------------------
-- FunctionalTerm Parser
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
    Tok.lexeme lexer (oneOf "$")
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

parseStringProcess :: String -> Either ParseError Process
parseStringProcess = parse (whiteSpace >> process <* eof) ""
