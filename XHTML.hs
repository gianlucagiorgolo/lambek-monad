module XHTML where

import Text.XHtml.Strict
import Data.List
import DataTypes
import Data.Monoid
import TP

proof2html :: BinTree DecoratedSequent -> Html
proof2html t = aux t where
		reading t = h4 << lambda2html (term $ snd $ getVal t)
		aux (Leaf lab s) =
				table << ((tr << "") +++
					  (tr << ((td << hr) +++ (td << lab2html lab))) +++
					  (tr << td << decoratedSeq2html s))
		aux (Unary lab s t) =
				table << ((tr << td << aux t) +++
					  (tr << ((td << hr) +++ (td << lab2html lab))) +++
					  (tr << td << decoratedSeq2html s))
		aux (Branch lab l s r) =
				table << ((tr << ((td << aux l) +++
					    	  (td << aux r))) +++
		  			  (tr << ((td << hr) ! [intAttr "colspan" 2] +++
						  (td << lab2html lab))) +++
					  (tr << (td << decoratedSeq2html s) ! [intAttr "colspan" 2]))

lab2html :: Label -> Html
lab2html Id = toHtml "id"
lab2html LImplL = primHtml "\\ L"
lab2html LImplR = primHtml "\\ R"
lab2html RImplL = primHtml "/ L"
lab2html RImplR = primHtml "/ R"
lab2html (MonL t) = primHtml "&loz;L" +++ (Text.XHtml.Strict.sub $ primHtml t)
lab2html (MonR t) = primHtml "&loz;R" +++ (Text.XHtml.Strict.sub $ primHtml t)
lab2html TensL = primHtml "&otimes;L"
lab2html TensR = primHtml "&otimes;R"

lambda2html :: LambdaTerm -> Html
lambda2html (C c) = thespan ! [ theclass "constant" ] << c
lambda2html (V n) | n < length sanevars && n >= 0 =
		   toHtml $ sanevars !! n
                  | otherwise = toHtml $ "v" ++ show n
lambda2html (Lambda x b) =
	primHtml "&lambda;" +++
	lambda2html x +++
	toHtml "." +++
	lambda2html b
lambda2html (Eta t f) =
	primHtml "&eta;" +++ (Text.XHtml.Strict.sub $ primHtml t) +++ primHtml "(" +++
	lambda2html f +++
	toHtml ")"
lambda2html (App f@(Lambda _ _) a) =
	toHtml "(" +++
	lambda2html f +++
	toHtml ")(" +++
	lambda2html a +++
	toHtml ")"
lambda2html (App f@(Bind _ _ _) a) =
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
lambda2html (Bind t m k) =
	lambda2html m +++
	primHtml " &lowast;" +++ (Text.XHtml.Strict.sub $ primHtml t) +++ primHtml " " +++
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
decoratedSeq2html (gamma,c) = mconcat left +++ (thespan ! [theclass "turnstile"] << primHtml " &#x22A2; ") +++ f c where
    left = intersperse (toHtml ", ") $ map f gamma
    f (DF _ lt f) = (thespan ! [theclass "term"] << lambda2html (betaReduce $ monadReduce $ etaReduce $ lt)) +++ (thespan << (toHtml " : " +++ (thespan ! [theclass "formula"] << formula2html f)))

formula2html :: Formula -> Html
formula2html (Atom a) = toHtml a
formula2html (Var x) = toHtml x
formula2html (M _ (Atom a)) = primHtml "&loz;" +++ a
formula2html (M _ (Var x)) = primHtml "&loz;" +++ x
formula2html (M _ f) = primHtml "&loz;(" +++ formula2html f +++ toHtml ")"
formula2html (P (Atom a) f) = a +++ primHtml " &otimes; " +++ formula2html f
formula2html (P (Var a) f) = a +++ primHtml " &otimes; " +++ formula2html f
formula2html (P d@(M _ _) f) = formula2html d +++ primHtml " &otimes; " +++ formula2html f
formula2html (P a b) = toHtml "(" +++ formula2html a +++ primHtml ") &otimes; " +++ formula2html b
formula2html (LI f g) = parentheses	f (formula2html f) +++ primHtml " \\ " +++ parentheses g (formula2html g)
formula2html (RI f g) = parentheses	g (formula2html g) +++ primHtml " / " +++ parentheses f (formula2html f)

parentheses :: Formula -> Html -> Html
parentheses (RI _ _) h = primHtml "(" +++ h +++ primHtml ")"
parentheses (LI _ _) h = primHtml "(" +++ h +++ primHtml ")"
parentheses _ h = h
