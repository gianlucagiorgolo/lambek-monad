{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Control.Applicative (optional, (<$>))
import           Data.List
import           Data.Maybe          (fromMaybe)
import           Data.Monoid
import           Data.Text           (Text)
import           Data.Text.Lazy      (unpack)
import           DataTypes
import           Happstack.Lite
import           Parsers
import           Paths_lambek_cg
import           Text.XHtml.Strict
import           TP
import           XHTML

data Resources = Resources { lexicon   :: String
                           , css_style :: Html
                           , proofs    :: [BinTree DecoratedSequent]
                           , sentence  :: String }

main = do
  res <- loadResources
  serve Nothing (homePage res)

loadResources = do
  lexFile <- getDataFileName "data/def_lexicon"
  cssFile <- getDataFileName "data/style.css"
  lex <- readFile lexFile -- >> \s -> return $ parseLexicon s
  css <- readFile cssFile >>= \s -> return $ primHtml s
  return $ Resources lex css [] "John doesnt_believe Hesperus is Phosphorus => <>s"

pageTemplate :: Resources -> Html
pageTemplate res = header << style << css_style res +++
                   body << inputAreaTemplate res +++
                           proofsAreaTemplate res

inputAreaTemplate :: Resources -> Html
inputAreaTemplate res = cont << (lex +++ sent) where
  cont = form ! [ theclass "input"
                , action "/"
                , enctype "multipart/form-data"
                , Text.XHtml.Strict.method "POST" ]
  lex = h1 (primHtml "Lexicon") +++
        textarea ! [ theclass "mono_textarea"
                   , name "lexicon"
                   , rows "20"
                   , cols "80" ] << primHtml (Main.lexicon res)
  sent = h1 (primHtml "Lexicon") +++
         input ! [ theclass "mono_textarea"
                 , thetype "text"
                 , name "sentence"
                 , value (sentence res)
                 , size "80"] +++
         input ! [ thetype "submit"
                 , name "submit"
                 , value "Parse" ]

proofsAreaTemplate :: Resources -> Html
proofsAreaTemplate res = proofsTitle +++ ps where
  proofsTitle = h1 << (primHtml $ (show $ length $ Main.proofs res) ++ " proof(s)")
  ps = mconcat $ map proof2html $ Main.proofs res

homePage :: Resources -> ServerPart Response
homePage res = msum [ viewForm, processForm ]
   where
     viewForm :: ServerPart Response
     viewForm =
         do Happstack.Lite.method GET
            ok $ toResponse $ pageTemplate res

     processForm :: ServerPart Response
     processForm =
         do Happstack.Lite.method [GET,POST]
            raw_lex <- lookText "lexicon"
            sent <- lookText "sentence"
            lex <- return $ parseLexicon $ unpack raw_lex
            seq <- return $ parseSequent (unpack sent) lex
            ps <- return $ evaluateState (toDecoratedWithConstants seq >>= \(ds,m) -> TP.proofs ds >>= \p -> return $ replaceWithConstants p m) startState
            ps <- return $ nubByShortest (lambdaTermLength . term . snd . getVal) (\x y -> simplifiedEquivalentDecoratedSequent (getVal x) (getVal y)) $ map sanitizeVars ps
            ok $ toResponse $ pageTemplate res{ Main.lexicon = unpack raw_lex, Main.proofs = ps, sentence= unpack sent}


lambdaTermLength :: LambdaTerm -> Int
lambdaTermLength (V _) = 1
lambdaTermLength (C _) = 1
lambdaTermLength (Lambda x t) = lambdaTermLength x + lambdaTermLength t
lambdaTermLength (App f x) = lambdaTermLength f + lambdaTermLength x
lambdaTermLength (Eta t) = 1 + lambdaTermLength t
lambdaTermLength (Bind m k) = lambdaTermLength m + lambdaTermLength k
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
