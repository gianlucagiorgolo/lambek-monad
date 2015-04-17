{
module Parsers where

import Control.Monad.State
import qualified Data.Map as Map
import Data.Either

import Tokenizer
import qualified DataTypes as DT
}

%name formula Formula
%name lambdaTerm LambdaTerm
%name lexicon Lexicon
%name sequent Sequent
%tokentype { Token }
%error { parseError }
%monad { State ParserState }

%token
    sep { Sep }
    diamond { Diamond $$ }
    fullstop { Fullstop }
    comma { Comma }
    backslash { Backslash }
    forwardslash { Forwardslash }
    openpar { OpenPar }
    closedpar { ClosedPar }
    openangle { OpenAngle }
    closedangle { ClosedAngle }
    arrow { Arrow }
    asterisk { Asterisk }
    var { Var $$ }
    const { Const $$ }
    eta { Eta $$ }
    bind { Bind $$ }
    p1 { P1 }
    p2 { P2 }
    turnstyle { Turnstyle }

%right forwardslash backslash
%right asterisk
%nonassoc diamond

%%

Formula : openpar Formula closedpar { $2 }
        | diamond Formula { DT.M $1 $2 }
        | Formula asterisk Formula { DT.P $1 $3 }
        | Formula forwardslash Formula { DT.RI $3 $1 }
        | Formula backslash Formula { DT.LI $1 $3 }
        | var { DT.Var $1 }
        | const { DT.Atom $1 }

LambdaTerm : backslash var arrow LambdaTerm {% getVarId $2 >>= \i -> return (DT.Lambda (DT.V i) $4) }
           | openangle LambdaTerm comma LambdaTerm closedangle { DT.Pair $2 $4 }
           | p1 openpar LambdaTerm closedpar { DT.FirstProjection $3 }
           | p2 openpar LambdaTerm closedpar { DT.SecondProjection $3 }
           | eta openpar LambdaTerm closedpar { DT.Eta $1 $3 }
           | form { $1 }

form : applications { $1 }
     | binds { $1 }


applications : applications atom { DT.App $1 $2 }
             | atom { $1 }

binds : binds bind atom { DT.Bind $2 $1 $3 }
      | atom { $1 }

atom : openpar LambdaTerm closedpar {$2}
     | var {% getVarId $1 >>= \i -> return (DT.V i) }
     | const { DT.C $1 }

Lexicon : Lexicon Entry { $2 : $1 }
        | Entry { [$1] }

Entry : word sep Formula sep LambdaTerm fullstop { ($1,($3,$5)) }

word : const { $1 }
     | var { $1 }

Sequent : words turnstyle Formula { (reverse $1, $3) }

words : words word { $2 : $1 }
      | word { [$1] }

{

data ParserState = ParserState { bindings :: Map.Map String Int
                               , counter :: Int }

initialState = ParserState Map.empty 0

getVarId :: String -> State ParserState Int
getVarId s = do
  st <- get
  case Map.lookup s (bindings st) of
     Nothing -> do
        i <- return $ counter st
        put $ ParserState (Map.insert s i $ bindings st) (i+1)
        return i
     Just i -> return i

parseError :: [Token] -> a
parseError toks = error $ "Parse error: " ++ show toks

parseFormula s = evalState (formula $ tokenize s) initialState

parseLambdaTerm s = evalState (lambdaTerm $ tokenize s) initialState

parseLexicon s = evalState (lexicon $ tokenize s) initialState

parseSequent :: String -> DT.Lexicon -> Either String ([(DT.LambdaTerm, DT.Formula)], DT.Formula)
parseSequent s lex = res where
   (ws,rhs) = evalState (sequent $ tokenize s) initialState
   lhs = map f ws
   res = if null (lefts lhs) then Right (rights lhs, rhs)
          else Left $ "These words are not defined in the lexicon: " ++ show (lefts lhs)
   f w = case lookup w lex of
           Nothing -> Left $ w
           Just (form,term) -> Right (term,form)

}
