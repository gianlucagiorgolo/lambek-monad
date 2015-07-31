module Evaluator where

import BrokenLanguage.Haskell.Interpreter
import System.Directory
import DataTypes
import System.FilePath
import Paths_lambek_monad

-- | @eval model term@ evaluates the lambda term given the model module
evaluate :: String -> String -> LambdaTerm -> IO String
evaluate model modelPrefFile term = do
  prefix <- getDataFileName modelPrefFile >>= \fn -> readFile fn
  tmpDir <- getTemporaryDirectory
  modFile <- return $ joinPath [tmpDir, "Model.hs"]
  writeFile modFile $ prefix ++ model
  r <- runInterpreter $ do
        loadModules [modFile]
        setTopLevelModules ["Model"]
        eval (toHaskell term)
  case r of
    Left err -> return $ show err
    Right s -> return s

-- |Translates a lambda term into an Haskell expression. The output is not meant to be pretty. We could have used Language.Haskell.Syntax but it seems overkill for our purposes
toHaskell :: LambdaTerm -> String
toHaskell (V i) = "__v" ++ show i ++ "__"
toHaskell (C s) = s
toHaskell (Lambda x t) = "(\\ " ++ toHaskell x ++ " -> " ++ toHaskell t ++ ")"
toHaskell (App f x) = "(" ++ toHaskell f ++ " " ++ toHaskell x ++ ")"
toHaskell (Pair t u) = "(" ++ toHaskell t ++ "," ++ toHaskell u ++ ")"
toHaskell (FirstProjection p) = "(fst " ++ toHaskell p ++ ")"
toHaskell (SecondProjection p) = "(snd " ++ toHaskell p ++ ")"
toHaskell (Eta ty t) = "(unit_" ++ ty ++ " " ++ toHaskell t ++ ")"
toHaskell (Bind ty m k) = "(bind_" ++ ty ++ " " ++ toHaskell m ++ " " ++ toHaskell k ++ ")"
