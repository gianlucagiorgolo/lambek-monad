module Latex where

import Data.List
import DataTypes
import Data.Monoid
import TP

type Latex = String

proof2latex :: BinTree DecoratedSequent -> Latex
proof2latex t = aux t where
    aux (Leaf lab s) =
        "\\RightLabel{$" ++ lab2latex lab ++ "$}" ++
        "\\AxiomC{$" ++ decoratedSeq2latex s ++ "$}"
    aux (Unary lab s t) =
        aux t ++
        "\\RightLabel{$" ++ lab2latex lab ++ "$}" ++
        "\\UnaryInfC{$" ++ decoratedSeq2latex s ++ "$}"
    aux (Branch lab l s r) =
        aux l ++
        aux r ++
        "\\RightLabel{$" ++ lab2latex lab ++ "$}" ++
        "\\BinaryInfC{$" ++ decoratedSeq2latex s ++ "$}"

lab2latex :: Label -> Latex
lab2latex Id = "id"
lab2latex LImplL = "\\backslash L"
lab2latex LImplR = "\\backslash R"
lab2latex RImplL = "/ L"
lab2latex RImplR = "/ R"
lab2latex (MonL t) = "\\lozenge L_{" ++ t ++ "}"
lab2latex (MonR t) = "\\lozenge R_{" ++ t ++ "}"
lab2latex TensL = "\\otimes L"
lab2latex TensR = "\\otimes R"

lambda2latex :: LambdaTerm -> Latex
lambda2latex (C c) = c
lambda2latex (V n) | n < length sanevars && n >= 0 =
		   sanevars !! n
                   | otherwise = "v" ++ show n
lambda2latex (Lambda x b) =
	"\\lambda " ++
	lambda2latex x ++
	"." ++
	lambda2latex b
lambda2latex (Eta t f) =
	"\\eta_{" ++ t ++  "}(" ++
	lambda2latex f ++
	")"
lambda2latex (App f@(Lambda _ _) a) =
	"(" ++
	lambda2latex f ++
	")(" ++
	lambda2latex a ++
	")"
lambda2latex (App f@(Bind _ _ _) a) =
	"(" ++
	lambda2latex f ++
	")(" ++
	lambda2latex a ++
	")"
lambda2latex (App f a) =
	lambda2latex f ++
	"(" ++
	lambda2latex a ++
	")"
lambda2latex (Bind t m k) =
	lambda2latex m ++
	" \\star_{" ++ t ++ "} " ++
	lambda2latex k
lambda2latex (Pair a b) =
        "\\langle" ++
        lambda2latex a ++
        "," ++
        lambda2latex b ++
        "\\rangle"
lambda2latex (FirstProjection a) =
        "\\pi_1(" ++
        lambda2latex a ++
        ")"
lambda2latex (SecondProjection a) =
        "\\pi_2(" ++
        lambda2latex a ++
        ")"

decoratedSeq2latex :: DecoratedSequent -> Latex
decoratedSeq2latex (gamma,c) = mconcat left ++ " \\vdash " ++ f c where
    left = intersperse ", " $ map f gamma
    f (DF _ lt f) = lambda2latex (betaReduce $ monadReduce $ etaReduce $ lt) ++ " : " ++ formula2latex f

formula2latex :: Formula -> Latex
formula2latex (Atom a) = a
formula2latex (Var x) = x
formula2latex (M _ (Atom a)) = "\\lozenge " ++ a
formula2latex (M _ (Var x)) = "\\lozenge " ++ x
formula2latex (M _ f) = "\\lozenge(" ++ formula2latex f ++ ")"
formula2latex (P (Atom a) f) = a ++ " \\otimes " ++ formula2latex f
formula2latex (P (Var a) f) = a ++ " \\otimes " ++ formula2latex f
formula2latex (P d@(M _ _) f) = formula2latex d ++ " \\otimes " ++ formula2latex f
formula2latex (P a b) = "(" ++ formula2latex a ++ ") \\otimes " ++ formula2latex b
formula2latex (LI f g) = parentheses	f (formula2latex f) ++ " \\backslash " ++ parentheses g (formula2latex g)
formula2latex (RI f g) = parentheses	g (formula2latex g) ++ " / " ++ parentheses f (formula2latex f)

parentheses :: Formula -> Latex -> Latex
parentheses (RI _ _) h = "(" ++ h ++ ")"
parentheses (LI _ _) h = "(" ++ h ++ ")"
parentheses _ h = h
