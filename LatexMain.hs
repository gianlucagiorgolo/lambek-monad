module Main where

import Latex
import TP
import System.Environment
import Parsers
import DataTypes
import Data.List

main = do
	(lexFile : sentence : _) <- getArgs
	lexContents <- readFile lexFile
	(Right lex) <- return $ parseLexicon lexContents
	sequent <- return $ parseSequent sentence lex
	ps <- return $ evaluateState (toDecoratedWithConstants (fromRight sequent) >>= \(ds,m) -> TP.proofs ds >>= \p -> return $ replaceWithConstants p m) startState
	ps <- return $ nubByShortest (lambdaTermLength . term . snd . getVal) (\x y -> simplifiedEquivalentDecoratedSequent (getVal x) (getVal y)) $ map sanitizeVars ps
	mapM_ (\p -> putStrLn (proof2latex p) >> putStrLn "") ps

fromLeft :: Either a b -> a
fromLeft (Left a) = a

fromRight :: Either a b -> b
fromRight (Right b) = b
fromRight _ = error "right from left"

lambdaTermLength :: LambdaTerm -> Int
lambdaTermLength (V _) = 1
lambdaTermLength (C _) = 1
lambdaTermLength (Lambda x t) = lambdaTermLength x + lambdaTermLength t
lambdaTermLength (App f x) = lambdaTermLength f + lambdaTermLength x
lambdaTermLength (Eta _ t) = 1 + lambdaTermLength t
lambdaTermLength (Bind _ m k) = lambdaTermLength m + lambdaTermLength k
lambdaTermLength (Pair a b) = lambdaTermLength a + lambdaTermLength b
lambdaTermLength (FirstProjection a) = 1 + lambdaTermLength a
lambdaTermLength (SecondProjection a) = 1 + lambdaTermLength a


nubByShortest :: Eq a => (a -> Int) ->
                 (a -> a -> Bool) ->
                 [a] ->
                 [a]
nubByShortest len eq l = aux l [] where
    aux [] acc = acc
    aux (a : as) acc =
       case find (eq a) acc of
         Nothing -> aux as (a : acc)
         Just a' -> case len a < len a' of
                        False -> aux as acc
                        True -> aux as (a : delete a' acc)
