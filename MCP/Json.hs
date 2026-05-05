module MCP.Json where

import Data.Char (chr, digitToInt, ord)
import Data.List (intercalate)
import Numeric (showHex)
import Text.Parsec hiding (spaces)
import Text.Parsec qualified as P
import Text.Read (readMaybe)

data Json
  = JNull
  | JBool Bool
  | JNum Int
  | JStr String
  | JArr [Json]
  | JObj [(String, Json)]
  deriving (Eq)

type JParser a = Parsec String () a

-- ==========================================
-- Rendering
-- ==========================================

renderJson :: Json -> String
renderJson JNull = "null"
renderJson (JBool True) = "true"
renderJson (JBool False) = "false"
renderJson (JNum n) = show n
renderJson (JStr s) = "\"" ++ jsonEscape s ++ "\""
renderJson (JArr xs) = "[" ++ intercalate "," (map renderJson xs) ++ "]"
renderJson (JObj kvs) = "{" ++ intercalate "," (map renderPair kvs) ++ "}"
  where
    renderPair (k, v) = "\"" ++ jsonEscape k ++ "\":" ++ renderJson v

jsonEscape :: String -> String
jsonEscape = concatMap escChar
  where
    escChar '"' = "\\\""
    escChar '\\' = "\\\\"
    escChar '\n' = "\\n"
    escChar '\r' = "\\r"
    escChar '\t' = "\\t"
    escChar '\b' = "\\b"
    escChar '\f' = "\\f"
    escChar c
      | ord c < 0x20 || ord c == 0x7F =
          "\\u" ++ pad4 (showHex (ord c) "")
      | otherwise = [c]
    pad4 s = replicate (4 - length s) '0' ++ s

-- ==========================================
-- Parsing
-- ==========================================

decodeJson :: String -> Either String Json
decodeJson s = case parse (ws *> jsonValue <* eof) "<json>" s of
  Left e -> Left (show e)
  Right v -> Right v

ws :: JParser ()
ws = P.spaces

lexeme :: JParser a -> JParser a
lexeme p = p <* ws

jsonValue :: JParser Json
jsonValue = ws *> (try jsonNull <|> try jsonBool <|> jsonNum <|> jsonStr <|> jsonArr <|> jsonObj)

jsonNull :: JParser Json
jsonNull = lexeme (string "null") >> return JNull

jsonBool :: JParser Json
jsonBool =
  lexeme $
    (string "true" >> return (JBool True))
      <|> (string "false" >> return (JBool False))

jsonNum :: JParser Json
jsonNum = lexeme $ do
  neg <- option "" (string "-")
  d <- digit
  ds <- many digit
  notFollowedBy (oneOf ".eE")
  let s = neg ++ (d : ds)
  case readMaybe s :: Maybe Int of
    Just n -> return (JNum n)
    Nothing -> fail ("Not a valid integer: " ++ s)

jsonStr :: JParser Json
jsonStr = JStr <$> jsonStringLit

jsonStringLit :: JParser String
jsonStringLit = lexeme $ char '"' *> many jsonChar <* char '"'

jsonChar :: JParser Char
jsonChar = jsonEscaped <|> satisfy (\c -> c /= '"' && c /= '\\')
  where
    jsonEscaped =
      char '\\'
        *> choice
          [ char '"' >> return '"',
            char '\\' >> return '\\',
            char '/' >> return '/',
            char 'b' >> return '\b',
            char 'f' >> return '\f',
            char 'n' >> return '\n',
            char 'r' >> return '\r',
            char 't' >> return '\t',
            char 'u' >> hexUnicode
          ]
    hexUnicode = do
      ds <- count 4 hexDigit
      return . chr $ foldl (\acc d -> acc * 16 + digitToInt d) 0 ds

jsonArr :: JParser Json
jsonArr = lexeme $ do
  char '['
  ws
  xs <- jsonValue `sepBy` (ws *> char ',' <* ws)
  ws
  char ']'
  return (JArr xs)

jsonObj :: JParser Json
jsonObj = lexeme $ do
  char '{'
  ws
  kvs <- jsonPair `sepBy` (ws *> char ',' <* ws)
  ws
  char '}'
  return (JObj kvs)

jsonPair :: JParser (String, Json)
jsonPair = do
  ws
  k <- jsonStringLit
  ws
  char ':'
  v <- jsonValue
  return (k, v)

-- ==========================================
-- Accessors
-- ==========================================

lookupKey :: String -> Json -> Maybe Json
lookupKey k (JObj kvs) = lookup k kvs
lookupKey _ _ = Nothing

getString :: Json -> Maybe String
getString (JStr s) = Just s
getString _ = Nothing

getInt :: Json -> Maybe Int
getInt (JNum n) = Just n
getInt _ = Nothing

getBool :: Json -> Maybe Bool
getBool (JBool b) = Just b
getBool _ = Nothing
