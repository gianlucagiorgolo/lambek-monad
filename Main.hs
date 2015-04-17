{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Control.Applicative (optional, (<$>))
import Control.Monad.IO.Class
import           Data.List
import           Data.Maybe          (fromMaybe, isJust, fromJust)
import           Data.Monoid
import Data.Either
import           Data.Text           (Text)
import           Data.Text.Lazy      (unpack)
import           Data.Char
import           DataTypes
import           Happstack.Lite
import           Parsers
import           Paths_lambek_monad
import           Text.XHtml.Strict
import           TP
import           XHTML
import Evaluator

-- for development
import System.Exit

data Resources = Resources { lexicon   :: String
                           , css_style :: Html
                           , proofs    :: [BinTree DecoratedSequent]
                           , sentence  :: String
                           , model     :: String
                           , readings  :: [String]
                           , error_msg :: Maybe String }

main = do
  res <- loadResources
  serve Nothing (homePage res)

loadResources = do
  lexFile <- getDataFileName "data/def_lexicon"
  cssFile <- getDataFileName "data/style.css"
  modelFile <- getDataFileName "data/def_model"
  lex <- readFile lexFile -- >> \s -> return $ parseLexicon s
  m <- readFile modelFile
  css <- readFile cssFile >>= \s -> return $ primHtml s
  return $ Resources lex css [] "John does not believe Hesperus is Phosphorus => <p>s" m [] Nothing

pageTemplate :: Resources -> Html
pageTemplate res = header << style << css_style res +++
                   body << inputAreaTemplate res +++
                           hr +++
                           proofsAreaTemplate res

inputAreaTemplate :: Resources -> Html
inputAreaTemplate res = cont << (lexiconForm res +++
                                 modelForm res +++
                                 sentenceForm res) where
  cont = form ! [ theclass "input"
                , action "/"
                , enctype "multipart/form-data"
                , Text.XHtml.Strict.method "POST" ]

lexiconForm :: Resources -> Html
lexiconForm res = h1 (primHtml "Lexicon") +++
                  textarea ! [ theclass "mono_textarea"
                             , name "lexicon"
                             , rows "20"
                             , cols "80" ] << primHtml (Main.lexicon res)

sentenceForm :: Resources -> Html
sentenceForm res =
  h1 (primHtml "Sentence to parse") +++
  textarea ! [ theclass "mono_textarea"
             , thetype "text"
             , name "sentence"
             , rows "1"
             , cols "80"] << primHtml (sentence res) +++
  input ! [ thetype "submit"
          , name "submit"
          , theclass "mybutton"
          , value "Parse" ]

modelForm :: Resources -> Html
modelForm res = h1 (primHtml "Model") +++
                textarea ! [ theclass "mono_textarea"
                           , name "model"
                           , rows "20"
                           , cols "80" ] << primHtml (model res)

proofsAreaTemplate :: Resources -> Html
proofsAreaTemplate res | isJust (error_msg res) = (h1 << primHtml "Error:") +++ primHtml (fromJust $ error_msg res)
                       | otherwise = proofsTitle +++ ps where
  proofsTitle = h3 << (primHtml $ (show $ length $ Main.proofs res) ++ " proof(s) for \"" ++ (cleanUpSentence $ sentence res) ++"\"" )
  ps = mconcat $ map f $ zip (Main.proofs res) (readings res)
  cleanUpSentence s = reverse $ dropWhile isSpace $ reverse $ takeWhile (/= '=') s
  f (p,i) = thediv ! [theclass "proof"] << (lterm p +++ reading i +++ proof p) where
    proof = proof2html
    lterm p = h3 << (lambda2html . betaReduce . monadReduce . etaReduce . term . snd . getVal) p
    reading i = thediv ! [ theclass "model_evaluation_result" ] << thecode << primHtml i


homePage :: Resources -> ServerPart Response
homePage res = msum [ viewForm, processForm, dir "quit" quit ]
   where
     quit = liftIO exitSuccess
     viewForm :: ServerPart Response
     viewForm =
         do Happstack.Lite.method GET
            ok $ toResponse $ pageTemplate res

     processForm :: ServerPart Response
     processForm =
         do Happstack.Lite.method [GET,POST]
            raw_lex <- lookText "lexicon"
            sent <- lookText "sentence"
            m <- lookText "model"
            lex <- return $ parseLexicon $ unpack raw_lex
            seq <- return $ parseSequent (unpack sent) lex
            if isLeft seq then
              ok $ toResponse $ pageTemplate res{ Main.lexicon = unpack raw_lex, Main.proofs = [], sentence= unpack sent, model = unpack m, readings = [], error_msg = Just $ fromLeft seq}
              else do
            ps <- return $ evaluateState (toDecoratedWithConstants (fromRight seq) >>= \(ds,m) -> TP.proofs ds >>= \p -> return $ replaceWithConstants p m) startState
            ps <- return $ nubByShortest (lambdaTermLength . term . snd . getVal) (\x y -> simplifiedEquivalentDecoratedSequent (getVal x) (getVal y)) $ map sanitizeVars ps
            rs <- mapM (\p -> liftIO $ evaluate (unpack m) (term $ snd $ getVal p)) ps
            ok $ toResponse $ pageTemplate res{ Main.lexicon = unpack raw_lex, Main.proofs = ps, sentence= unpack sent, model = unpack m, readings = rs}


fromLeft :: Either a b -> a
fromLeft (Left a) = a

fromRight :: Either a b -> b
fromRight (Right b) = b

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
