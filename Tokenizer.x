{
module Tokenizer where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$upper = [A-Z]
$lower = [a-z]

tokens :-
  $white+      ;
  "::"         { \_ -> Sep }
  "eta"        { \_ -> Eta }
  "p1"         { \_ -> P1 }
  "p2"         { \_ -> P2 }
  ":*:"        { \_ -> Bind }
  "=>"         { \_ -> Turnstyle }
  "<>"         { \_ -> Diamond }
  "."          { \_ -> Fullstop }
  ","          { \_ -> Comma }
  \\           { \_ -> Backslash }
  "/"          { \_ -> Forwardslash }
  "("          { \_ -> OpenPar }
  ")"          { \_ -> ClosedPar }
  "<"          { \_ -> OpenAngle }
  ">"          { \_ -> ClosedAngle }
  "->"         { \_ -> Arrow }
  "*"          { \_ -> Asterisk }
  $upper [$alpha $digit \_ \-]* {\s -> Var s}
  $lower [$alpha $digit \_ \-]* {\s -> Const s}

{

data Token = Sep
           | Diamond
           | Fullstop
           | Comma
           | Backslash
           | Forwardslash
           | OpenPar
           | ClosedPar
           | OpenAngle
           | ClosedAngle
           | Arrow
           | Asterisk
           | Eta
           | Turnstyle
           | Bind
           | P1
           | P2
           | Var String
           | Const String deriving (Eq,Show)

tokenize = alexScanTokens

}
