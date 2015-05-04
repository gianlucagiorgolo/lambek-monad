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
  "#".*                                 ;
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
           | Const String deriving (Eq)

instance Show Token where
  show Sep = "::"
  show (Diamond s) = "<" ++ s ++ ">"
  show Fullstop = "."
  show Comma = ","
  show Backslash = "\\"
  show Forwardslash = "/"
  show OpenPar = "("
  show ClosedPar = ")"
  show OpenAngle = "["
  show ClosedAngle = "]"
  show Arrow = "->"
  show Asterisk = "*"
  show (Eta "") = "eta"
  show (Eta s) = "eta^" ++ s
  show Turnstyle = "=>"
  show (Bind "") = ":*:"
  show (Bind s) = ":*:^" ++ s
  show P1 = "p1"
  show P2 = "p2"
  show (Var s) = s
  show (Const s) = s

toHtml :: Token -> String
toHtml (Diamond s) = "&lt;" ++ s ++ "&gt;"
toHtml t = show t

chopFrontAndBack = reverse . tail . reverse . tail

tokenize :: String -> Either String [Token]
tokenize str = go ('\n',[],str)
  where go inp@(_,_bs,str) =
          case alexScan inp 0 of
                AlexEOF -> Right []
                AlexError inp' -> Left $ "I encountered an error while I was trying to tokenize this stuff:\n" ++ str
                AlexSkip  inp' len     -> go inp'
                AlexToken inp' len act -> do
                  h <- return $ act (take len str)
                  t <- go inp'
                  return $ h : t

}
