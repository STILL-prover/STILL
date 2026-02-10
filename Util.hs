module Util where

import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Map as M

letters :: [String]
letters = (: []) <$> ['a'..'z']

numbers :: [Integer]
numbers = [1..]

{-| 
>>> take 10 . drop 26 $ namesInOrder
["a1","b1","c1","d1","e1","f1","g1","h1","i1","j1"]
-}
namesInOrder :: [String]
namesInOrder = letters ++ [a ++ show i | i <- numbers, a <- letters]

getFreshName :: S.Set String -> String
getFreshName takenNames = head $ L.dropWhile (`S.member` takenNames) namesInOrder

justTrue :: Bool -> Maybe Bool
justTrue False = Nothing
justTrue True = Just True

eitherLookup :: forall k a. (Ord k, Show k, Show a) => k -> M.Map k a -> Either String a
eitherLookup k m = case M.lookup k m of
    Just res -> Right res
    Nothing -> Left $ "Could not find " ++ show k ++ " in " ++ show m

expr [] ex = ex
expr (h1:h2:rest) "" = expr rest (h1 ++ " * " ++ h2)
expr (h1:h2:rest) ex = expr rest (h1 ++ " * ( " ++ ex ++ " ) * " ++ h2)
expr a ex = ex

expr2 [] ex = ex
expr2 (h1:[]) ex = ex
expr2 (h1:h2:rest) ex = expr2 (h2:rest) $ ex ++ " -o (" ++ (h1 ++ " -o " ++ h2) ++ ")" 