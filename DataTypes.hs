module DataTypes where

import Data.Foldable hiding (msum)
import Data.Map (Map)
import Data.Monoid
import Data.List
import Control.Monad.State
import Data.Traversable
import Data.Functor
import Control.Applicative

type Type = String

data Formula = Atom String
             | Var String
             | M Type Formula
             | P Formula Formula
             | LI Formula Formula
             | RI Formula Formula deriving (Eq, Show, Ord)

type Context = [Formula]
type Sequent = (Context, Formula)

-- |The datatype of focused lists (isn't this a zipper?)
data Focused a = ContextLess [a] a [a]
               | LeftContext [a] [a] a [a]
               | RightContext [a] a [a] [a] deriving (Show,Eq,Ord)

getFocus :: Focused a -> a
getFocus (ContextLess _ a _) = a
getFocus (LeftContext _ _ a _) = a
getFocus (RightContext _ a _ _) = a

getContexts :: Focused a -> [[a]]
getContexts (ContextLess l _ r) = [l,r]
getContexts (LeftContext l lc _ r) = [l,lc,r]
getContexts (RightContext l _ rc r) = [l,rc,r]

createAllContextLessFocuses :: [a] -> [Focused a]
createAllContextLessFocuses l = aux l [] where
  aux [] _ = []
  aux (a : rest) l = ContextLess l a rest : aux rest (l ++ [a])

createAllLeftContextFocuses :: [a] -> [Focused a]
createAllLeftContextFocuses l = aux l [] [] where
  aux :: [a] -> [a] -> [a] -> [Focused a]
  aux [] _ _ = []
  aux (a : rest) l [] = LeftContext l [] a rest : (x ++ y) where
      x = aux rest (l ++ [a]) []
      y = aux rest l [a]
  aux (a : rest) l lc = LeftContext l lc a rest : aux rest l (lc ++ [a])

createAllRightContextFocuses :: [a] -> [Focused a]
createAllRightContextFocuses l = aux l [] where
  aux [] _ = []
  aux (a : rest) l = x ++ aux rest (l ++ [a]) where
      x = [ RightContext l a rc r | (rc,r) <- split rest ]

split :: [a] -> [([a],[a])]
split l = zip (inits l) (tails l)

unfocus :: Focused a -> [a]
unfocus (ContextLess l a r) = l ++ (a : r)
unfocus (LeftContext l lc a r) = l ++ lc ++ (a : r)
unfocus (RightContext l a rc r) = l ++ (a : rc) ++ r


data BinTree a = Branch Label (BinTree a) a (BinTree a)
               | Unary Label a (BinTree a)
               | Leaf Label a deriving (Eq, Show)

instance Foldable BinTree where
  foldMap f (Leaf _ a) = f a
  foldMap f (Unary _ a c) = f a `mappend` foldMap f c
  foldMap f (Branch _ l a r) = foldMap f l `mappend` f a `mappend` foldMap f r
instance Functor BinTree where
  fmap f (Leaf l a) = Leaf l (f a)
  fmap f (Unary l a c) = Unary l (f a) (fmap f c)
  fmap f (Branch lab l a r) = Branch lab (fmap f l) (f a) (fmap f r)

instance Traversable BinTree where
  traverse f (Leaf l a) = (Leaf l) <$> f a
  traverse f (Unary l a c) = (Unary l) <$> f a <*> traverse f c
  traverse f (Branch lab l a r) = (Branch lab) <$> traverse f l <*> f a <*> traverse f r

getVal :: BinTree a -> a
getVal (Leaf _ a) = a
getVal (Branch _ _ a _) = a
getVal (Unary _ a _) = a

setVal :: a -> BinTree a -> BinTree a
setVal a (Leaf l _) = Leaf l a
setVal a (Branch lab l _ r) = Branch lab l a r
setVal a (Unary l _ c) = Unary l a c

data Label = Id
           | LImplL
           | LImplR
           | RImplL
           | RImplR
           | TensL
           | TensR
           | MonL Type
           | MonR Type deriving (Eq, Show)

-- Curry Howard

data LambdaTerm = V Int
                | C String
                | Lambda LambdaTerm LambdaTerm -- this definition sucks because we want only variables but it'll do for now
                | App LambdaTerm LambdaTerm
                | Pair LambdaTerm LambdaTerm
                | FirstProjection LambdaTerm
                | SecondProjection LambdaTerm
                | Eta LambdaTerm
                | Bind LambdaTerm LambdaTerm deriving (Eq, Show, Ord) -- also this one is a poor definition

data DecoratedFormula = DF { identifier :: Int
                           , term :: LambdaTerm
                           , formula :: Formula } deriving Show

instance Eq DecoratedFormula where
  f == g = (identifier f) == (identifier g)

type DecoratedSequent = ([DecoratedFormula],DecoratedFormula)

type FocusedDecoratedSequent = (Focused DecoratedFormula, DecoratedFormula)

data S = S { counter :: Int
           , vars    :: Map Formula Formula} deriving Show

sanevars = ["x","y","z","w","v","k","h","l","m","n","a","b","c","d","e"]

type NonDeterministicState s a = StateT s [] a

failure :: NonDeterministicState s a
failure = StateT $ \_ -> []

every :: [NonDeterministicState s a] -> NonDeterministicState s a
every = msum

evaluateState :: NonDeterministicState s a -> s -> [a]
evaluateState = evalStateT

type Lexicon = [(String, (Formula, LambdaTerm))]


-- |Deletes an element from a list and returns the left and right contexts
deleteWithRemainders :: Eq a => a -> [a] -> ([a],[a])
deleteWithRemainders a l = (x,y) where
     (x,y') = break (==a) l
     y = safeTail y'
     safeTail [] = []
     safeTail (_ : t) = t
