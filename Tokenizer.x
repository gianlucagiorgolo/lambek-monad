{
module Tokenizer where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$upper = [A-Z]
$lower = [a-z]

tokens :-
  $white+                               ;
  "::"                                  { \_ -> Sep }
  "eta^" $lower [$alpha $digit \_ \-]*  { \s -> Eta (drop 4 s) }
  "eta"                                 { \_ -> Eta ""}
  "p1"                                  { \_ -> P1 }
  "p2"                                  { \_ -> P2 }
  ":*:^" $lower [$alpha $digit \_ \-]*  { \s -> Bind (drop 4 s) }
  ":*:"                                 { \_ -> Bind ""}
  "=>"                                  { \_ -> Turnstyle }
  "<>"                                  { \_ -> Diamond "" }
  "<" $lower [$alpha $digit \_ \-]* ">" {\s -> Diamond (chopFrontAndBack s) }
  "."                                   { \_ -> Fullstop }
  ","                                   { \_ -> Comma }
  \\                                    { \_ -> Backslash }
  "/"                                   { \_ -> Forwardslash }
  "("                                   { \_ -> OpenPar }
  ")"                                   { \_ -> ClosedPar }
  "["                                   { \_ -> OpenAngle }
  "]"                                   { \_ -> ClosedAngle }
  "->"                                  { \_ -> Arrow }
  "*"                                   { \_ -> Asterisk }
  $upper [$alpha $digit \_ \-]*         {\s -> Var s}
  $lower [$alpha $digit \_ \-]*         {\s -> Const s}

{

data Token = Sep
           | Diamond String
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
           | Eta String
           | Turnstyle
           | Bind String
           | P1
           | P2
           | Var String
           | Const String deriving (Eq,Show)

chopFrontAndBack = reverse . tail . reverse . tail

tokenize = alexScanTokens

}
