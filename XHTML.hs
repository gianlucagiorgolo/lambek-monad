module XHTML where

import Text.XHtml
import Data.List
import DataTypes
import Data.Monoid
import TP

proof2html :: BinTree DecoratedSequent -> Html 
proof2html (Leaf lab s) = 
		table << ((tr << "") +++ 
			  (tr << ((td << hr) +++ (td << lab2html lab))) +++
			  (tr << td << decoratedSeq2html s))
proof2html (Unary lab s t) = 
		table << ((tr << td << proof2html t) +++
			  (tr << ((td << hr) +++ (td << lab2html lab))) +++
			  (tr << td << decoratedSeq2html s))
proof2html (Branch lab l s r) = 
		table << ((tr << ((td << proof2html l) +++
			    	  (td << proof2html r))) +++
  			  (tr << ((td << hr) ! [intAttr "colspan" 2] +++
				  (td << lab2html lab))) +++
			  (tr << (td << decoratedSeq2html s) ! [intAttr "colspan" 2]))

lab2html :: Label -> Html
lab2html Id = toHtml "id"
lab2html LImplL = primHtml "\\ L"
lab2html LImplR = primHtml "\\ R"
lab2html RImplL = primHtml "/ L"
lab2html RImplR = primHtml "/ R"
lab2html MonL = primHtml "&loz;L"
lab2html MonR = primHtml "&loz;R"
lab2html TensL = primHtml "&otimes;L"
lab2html TensR = primHtml "&otimes;R"

lambda2html :: LambdaTerm -> Html
lambda2html (C c) = bold << c
lambda2html (V n) | n < length sanevars && n >= 0 = 
		   toHtml $ sanevars !! n
                  | otherwise = toHtml $ "v" ++ show n
lambda2html (Lambda x b) = 
	primHtml "&lambda;" +++
	lambda2html x +++
	toHtml "." +++
	lambda2html b
lambda2html (Eta f) =
	primHtml "&eta;(" +++
	lambda2html f +++
	toHtml ")"
lambda2html (App f@(Lambda _ _) a) =
	toHtml "(" +++
	lambda2html f +++
	toHtml ")(" +++
	lambda2html a +++
	toHtml ")"
lambda2html (App f@(Bind _ _) a) = 
	toHtml "(" +++
	lambda2html f +++
	toHtml ")(" +++
	lambda2html a +++
	toHtml ")"
lambda2html (App f a) = 
	lambda2html f +++
	toHtml "(" +++
	lambda2html a +++
	toHtml ")"
lambda2html (Bind m k) = 
	lambda2html m +++
	primHtml " &lowast; " +++
	lambda2html k
lambda2html (Pair a b) = 
        primHtml "&lt;" +++
        lambda2html a +++
        toHtml "," +++
        lambda2html b +++
        primHtml "&gt;"
lambda2html (FirstProjection a) = 
        primHtml "&pi;1(" +++
        lambda2html a +++
        toHtml ")"
lambda2html (SecondProjection a) = 
        primHtml "&pi;2(" +++
        lambda2html a +++
        toHtml ")"

decoratedSeq2html :: DecoratedSequent -> Html
decoratedSeq2html (gamma,c) = mconcat left +++ toHtml " => " +++ f c where
    left = intersperse (toHtml ", ") $ map f gamma
    f (DF _ lt f) = lambda2html (betaReduce $ monadReduce $ etaReduce $ lt) +++ toHtml " : " +++ formula2html f

-- |Texifies a formula (now with smart parentheses!)
formula2html :: Formula -> Html
formula2html (Atom a) = toHtml a
formula2html (Var x) = toHtml x
formula2html (M (Atom a)) = primHtml "&loz;" +++ a
formula2html (M (Var x)) = primHtml "&loz;" +++ x
formula2html (M f) = primHtml "&loz;(" +++ formula2html f +++ toHtml ")"
formula2html (P (Atom a) f) = a +++ primHtml " &otimes; " +++ formula2html f
formula2html (P (Var a) f) = a +++ primHtml " &otimes; " +++ formula2html f
formula2html (P d@(M _) f) = formula2html d +++ primHtml " &otimes; " +++ formula2html f
formula2html (P a b) = toHtml "(" +++ formula2html a +++ primHtml ") &otimes; " +++ formula2html b
formula2html (LI (Atom a) f) = a +++ primHtml " \\ " +++ formula2html f
formula2html (LI (Var a) f) = a +++ primHtml " \\ " +++ formula2html f
formula2html (LI d@(M _) f) = formula2html d +++ primHtml " \\ " +++ formula2html f
formula2html (LI f g) = 
		toHtml "(" +++
		formula2html f +++
		primHtml ") \\ " +++
		formula2html g
formula2html (RI (Atom a) f) = formula2html f +++ primHtml " / " +++ a
formula2html (RI (Var a) f) = formula2html f +++ primHtml " / " +++ a
formula2html (RI d@(M _) f) = formula2html f +++ primHtml " / " +++ formula2html d
formula2html (RI f g) = 
		toHtml "(" +++
		formula2html g +++
		primHtml ") / " +++
		formula2html f

