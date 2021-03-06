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
import System.Environment
import           DataTypes
import           Happstack.Lite
import           Parsers
import           Paths_lambek_monad
import           Text.XHtml.Strict
import           TP
import           XHTML
import Evaluator

import Control.Concurrent
import Control.Concurrent.MVar

-- for development
import System.Exit

data Resources = Resources { lexicon   :: String
                           , css_style :: Html
                           , proofs    :: [BinTree DecoratedSequent]
                           , sentence  :: String
                           , model     :: String
                           , readings  :: [String]
                           , error_msg :: Maybe String
                           , baseDir   :: String
                           , day       :: String
                           , dayNotes  :: String
                           , modelPref :: String }

day1Example = "John loves Mary => s"
day2Example = "JLH COMMA the bluesman from Tennessee appeared_in TBB => <ci>s"
day3Example = "John does not believe Hesperus is Phosphorus => <p>s"
day4Example = "Spain will_beat Germany and Nigeria will_beat Canada => <pr>s"
day5Example = "Nigeria will_beat motherfucking Canada => <ci><pr>s"

main = do
  args <- getArgs
  p <- return $ case args of
                  [] -> 8000
                  (p : _) -> read p
  serve (Just defaultServerConfig{port = p}) homePage

loadResources :: String -> String -> String -> String -> String -> String -> String -> IO Resources
loadResources lexiconFile modelFile baseDir example day notesFile modelPrefFile = do
  lexFile <- getDataFileName lexiconFile
  cssFile <- getDataFileName "data/style.css"
  modelFile <- getDataFileName modelFile
  notesFile <- getDataFileName notesFile
  lex <- readFile lexFile -- >> \s -> return $ parseLexicon s
  m <- readFile modelFile
  css <- readFile cssFile >>= \s -> return $ primHtml s
  notes <- readFile notesFile
  return $ Resources lex css [] example m [] Nothing baseDir day notes modelPrefFile

pageTemplate :: Resources -> Html
pageTemplate res = header << style << css_style res +++
                   body << navigation +++
                           titleArea res +++
                           notesArea res +++
                           inputAreaTemplate res +++
                           hr +++
                           proofsAreaTemplate res

titleArea res = h1 (primHtml $ day res)

inputAreaTemplate :: Resources -> Html
inputAreaTemplate res = cont << (lexiconForm res +++
                                 modelForm res +++
                                 sentenceForm res) where
  cont = form ! [ theclass "input"
                , action "." -- (baseDir res)
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

notesArea :: Resources -> Html
notesArea res =
  h1 (primHtml "Notes") +++
  thediv ! [ theclass "notesArea" ] << primHtml (dayNotes res)

modelForm :: Resources -> Html
modelForm res = h1 (primHtml "Model") +++
                textarea ! [ theclass "mono_textarea"
                           , name "model"
                           , rows "20"
                           , cols "80" ] << primHtml (model res)

proofsAreaTemplate :: Resources -> Html
proofsAreaTemplate res | isJust (error_msg res) = (h1 << primHtml "Error:") +++ pre << primHtml (fromJust $ error_msg res)
                       | otherwise = proofsTitle +++ ps where
  proofsTitle = h3 << (primHtml $ (show $ length $ Main.proofs res) ++ " proof(s) for \"" ++ (cleanUpSentence $ sentence res) ++"\"" )
  ps = mconcat $ map f $ zip3 (Main.proofs res) (readings res) [1..]
  cleanUpSentence s = reverse $ dropWhile isSpace $ reverse $ takeWhile (/= '=') s
  f (p,i,n) = thediv ! [ theclass "proofgroup" ] << (h3 ! [ theclass "prooftitle" ] << (primHtml $ "Proof " ++ show n)) +++ (lterm p +++ reading i +++ proof p) where
    proof p = thediv ! [ theclass "proof" ] << proof2html p
    lterm p = thediv ! [ theclass "reading" ] << paragraph << (lambda2html . betaReduce . monadReduce . etaReduce . term . snd . getVal) p
    reading i = thediv ! [ theclass "model_evaluation_result" ] << pre << primHtml i

navigation :: Html
navigation =
          thediv ! [Text.XHtml.Strict.identifier "navcontainer"] <<
          ulist << (li << anchor ! [href "../day1/"] << primHtml "Day 1" +++
                    li << anchor ! [href "../day2/"] << primHtml "Day 2" +++
                    li << anchor ! [href "../day3/"] << primHtml "Day 3" +++
                    li << anchor ! [href "../day4/"] << primHtml "Day 4" +++
                    li << anchor ! [href "../day5/"] << primHtml "Day 5")

homePage :: ServerPart Response
homePage = msum [ dir "day1" day1
                , dir "day2" day2
                , dir "day3" day3
                , dir "day4" day4
                , dir "day5" day5
                , day1 ]
   where

     day lexiconFile modelFile baseDir example day notesFile modelPrefFile= do
          res <- liftIO $ loadResources lexiconFile modelFile baseDir example day notesFile modelPrefFile
          msum [viewForm res, processForm res]

     day1 = day "data/day1_lexicon" "data/day1_model" "day1/" day1Example "Day 1" "data/day1_notes.html" "data/model_prefix"
     day2 = day "data/day2_lexicon" "data/day2_model" "day2/" day2Example "Day 2" "data/day2_notes.html" "data/model_prefix"
     day3 = day "data/day3_lexicon" "data/day3_model" "day3/" day3Example "Day 3" "data/day3_notes.html" "data/model_prefix"
     day4 = day "data/day4_lexicon" "data/day4_model" "day4/" day4Example "Day 4" "data/day4_notes.html" "data/model_prefix_with_db"
     day5 = day "data/day5_lexicon" "data/day5_model" "day5/" day5Example "Day 5" "data/day5_notes.html" "data/model_prefix_with_db"

     viewForm :: Resources -> ServerPart Response
     viewForm res =
         do Happstack.Lite.method GET
            ok $ toResponse $ pageTemplate res

     processForm :: Resources -> ServerPart Response
     processForm res =
         do Happstack.Lite.method [GET,POST]
            raw_lex <- lookText "lexicon"
            sent <- lookText "sentence"
            m <- lookText "model"
            lex <- return $ parseLexicon $ unpack raw_lex
            -- we verify the lexicon
            if Main.isLeft lex then
              ok $ toResponse $ pageTemplate res{ Main.lexicon = unpack raw_lex, Main.proofs = [], sentence= unpack sent, model = unpack m, readings = [], error_msg = Just $ fromLeft lex}
              else do
            seq <- return $ parseSequent (unpack sent) $ fromRight lex
            -- we verify the sequent
            if Main.isLeft seq then
              ok $ toResponse $ pageTemplate res{ Main.lexicon = unpack raw_lex, Main.proofs = [], sentence= unpack sent, model = unpack m, readings = [], error_msg = Just $ fromLeft seq}
              else do
            ps <- return $ evaluateState (toDecoratedWithConstants (fromRight seq) >>= \(ds,m) -> TP.proofs ds >>= \p -> return $ replaceWithConstants p m) startState
            ps <- return $ nubByShortest (lambdaTermLength . term . snd . getVal) (\x y -> simplifiedEquivalentDecoratedSequent (getVal x) (getVal y)) $ map sanitizeVars ps
            rs <- mapM (\p -> liftIO $ performEvaluation (unpack m) (modelPref res) (term $ snd $ getVal p)) ps
            ok $ toResponse $ pageTemplate res{ Main.lexicon = unpack raw_lex, Main.proofs = ps, sentence= unpack sent, model = unpack m, readings = rs}


-- |This function performs the evaluation in a different thread, hopefully overcoming the problems with hint
performEvaluation :: String -> String -> LambdaTerm -> IO String
performEvaluation model modelPrefFile term = do
  storage <- newEmptyMVar
  forkIO $ do
    s <- evaluate model modelPrefFile term
    putMVar storage s
  readMVar storage

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


isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False
