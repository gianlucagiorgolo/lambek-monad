{-# LANGUAGE OverloadedStrings #-}

module Main where

import System.Environment
import Control.Applicative ((<$>), optional)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text.Lazy (unpack)
import Happstack.Lite
-- import Text.Blaze.Html5 (Html, (!), a, form, input, p, toHtml, label)
-- import Text.Blaze.Html5.Attributes (action, enctype, href, name, size, type_, value)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Text.XHtml
import DataTypes
import XHTML
import Parsers
import TP
import Data.Monoid
import Data.List


main = do
  (lexFile : _) <- getArgs
  s <- readFile lexFile
  lex <- return $ parseLexicon s
  serve Nothing (myApp lex)

myApp :: Lexicon -> ServerPart Response
myApp lex = msum
   [ homePage lex ]

template :: Text -> H.Html -> Response
template title body = toResponse $
         H.html $ do
             H.head $ do
               H.title (H.toHtml title)
             H.body $ do
               body
               
homePage :: Lexicon -> ServerPart Response
homePage lex = msum [ viewForm, processForm ]
   where
     viewForm :: ServerPart Response
     viewForm =
         do Happstack.Lite.method GET
            ok $ template "Glue TP" $
               H.form H.! A.action "/" H.! A.enctype "multipart/form-data" H.! A.method "POST" $ do
                 H.label H.! A.for "msg" $ "Sequent to prove: "
                 H.input H.! A.size "150" H.! A.type_ "text" H.! A.id "msg" H.! A.name "msg"
                 H.input H.! A.type_ "submit" H.! A.value "Prove"

     processForm :: ServerPart Response
     processForm =
         do Happstack.Lite.method [GET,POST]
            res <- lookText "msg"
            ok $ toResponse $ 
              printProofsWithConstants (parseSequent (unpack res) lex)

css_script = "em{font-weight:bold;} div{margin: 20px auto; width: 100%;} td {white-space: nowrap; text-align: center; vertical-align: bottom; padding-left: 5px; padding-right: 5px; font-family: \"Palatino Linotype\", \"Book Antiqua\", Palatino, serif; font-style: italic;} .title{ font-family: \"Lucida Sans Unicode\", \"Lucida Grande\", sans-serif; color: #5E5E5E;font-size: 17px; background-color: #FFFFFF; letter-spacing: 5.8pt;word-spacing: 3pt; line-height: 1.2; padding: 21px;} .verbatim{font-family:\"Lucida Console\", Monaco, monospace}"



printProofs s = pproofs $ (evaluateState (toDecorated s >>= \ds -> proofs ds) startState)

printProofsWithConstants s = pproofs $ (evaluateState (toDecoratedWithConstants s >>= \(ds,m) -> proofs ds >>= \p -> return $ replaceWithConstants p m) startState)

pproofs ps =
  let ps' = nubByShortest (lambdaTermLength . term . snd . getVal) (\x y -> simplifiedEquivalentDecoratedSequent (getVal x) (getVal y)) $ map sanitizeVars ps
  in case ps' of
    [] -> pageTemplate (length ps') $ p << toHtml ("Not a theorem" :: String)
    _ -> pageTemplate (length ps') $ mconcat $ map (\x -> thediv << proof2html x) ps'

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

pageTemplate :: Int -> Html -> Html
pageTemplate l h = 
   header << style << primHtml css_script +++
   body << (thediv << (h1 << toHtml ((show l) ++ " proof(s)" :: String)) ! [theclass "title"] +++ h +++ seqForm) where
    seqForm =  form ! [action "/", enctype "multipart/form-data", Text.XHtml.method "POST"] <<
                 ((label ! [thefor "msg"] << toHtml ("Sequent to prove: " :: String)) +++
                  input ! [size "150", thetype "text", Text.XHtml.identifier "msg", name "msg"] +++
                  input ! [thetype "submit", value "Prove"])

nubByShortest :: Eq a => (a -> Int) -> 
                 (a -> a -> Bool) ->
                 [a] -> 
                 [a]
nubByShortest len eq l = aux l [] where
    aux [] acc = acc
    aux (a : as) acc = 
       case find (\x -> eq a x) acc of
         Nothing -> aux as (a : acc)
         Just a' -> case len a < len a' of
                        False -> aux as acc
                        True -> aux as (a : delete a' acc)