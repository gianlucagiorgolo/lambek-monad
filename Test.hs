module Main where

import Test.HUnit
import System.Exit
import qualified Data.Set as Set 

import DataTypes
import TP

tests = TestList [ testUnfocus
                 , testCreateAllContextLessFocuses
                 , testCreateAllLeftContextFocuses
                 , testCreateAllRightContextFocuses
                 , testProvable ]

testUnfocus = "unfocus" ~: TestList
    [ unfocus (ContextLess [] 1 []) ~?= [1]
    , unfocus (ContextLess [1] 2 [3]) ~?= [1,2,3]
    , unfocus (LeftContext [1] [2] 3 [4]) ~?= [1,2,3,4]
    , unfocus (RightContext [1] 2 [3] [4]) ~?= [1,2,3,4] ]

testCreateAllContextLessFocuses = "createAllContextLessFocuses" ~: TestList
    [ createAllContextLessFocuses [] ~?= ([] :: [Focused Int])
    , createAllContextLessFocuses [1] ~?:= [ContextLess [] 1 []]
    , createAllContextLessFocuses [1,2] ~?:= [ContextLess [] 1 [2], ContextLess [1] 2 []]
    , createAllContextLessFocuses [1,2,3,4,5] ~?:= [ContextLess [] 1 [2,3,4,5], ContextLess [1] 2 [3,4,5], ContextLess [1,2] 3 [4,5], ContextLess [1,2,3] 4 [5], ContextLess [1,2,3,4] 5 []]]
    
testCreateAllLeftContextFocuses = "createAllLeftContextFocuses" ~: TestList
    [ createAllLeftContextFocuses [] ~?= ([] :: [Focused Int])
    , createAllLeftContextFocuses [1] ~?:= [LeftContext [] [] 1 []]
    , createAllLeftContextFocuses [1,2] ~?:= [LeftContext [] [] 1 [2], LeftContext [1] [] 2 [], LeftContext [] [1] 2 []]
    , createAllLeftContextFocuses [1,2,3,4] ~?:= [LeftContext [] [] 1 [2,3,4], LeftContext [1] [] 2 [3,4], LeftContext [] [1] 2 [3,4], LeftContext [1,2] [] 3 [4], LeftContext [1] [2] 3 [4], LeftContext [] [1,2] 3 [4], LeftContext [1,2,3] [] 4 [], LeftContext [1,2] [3] 4 [], LeftContext [1] [2,3] 4 [], LeftContext [] [1,2,3] 4 []]]

testCreateAllRightContextFocuses = "createAllRightContextFocuses" ~: TestList
    [ createAllRightContextFocuses [] ~?= ([] :: [Focused Int])
    , createAllRightContextFocuses [1] ~?:= [RightContext [] 1 [] []]
    , createAllRightContextFocuses [1,2] ~?:= [RightContext [] 1 [2] [], RightContext [] 1 [] [2], RightContext [1] 2 [] []]
    , createAllRightContextFocuses [1,2,3] ~?:= [RightContext [] 1 [2,3] [], RightContext [] 1 [2] [3], RightContext [] 1 [] [2,3], RightContext [1] 2 [3] [], RightContext [1] 2 [] [3], RightContext[1,2] 3 [] []]]

(~?:=) :: (Ord a, Show a) => [a] -> [a] -> Test
l ~?:= r = Set.fromList l ~?= Set.fromList r 

testProvable = "provable" ~: TestList
    [ provable ([Atom "a"],Atom "a") ~?= True
    , provable ([],Atom "a") ~?= False
    , provable ([Atom "a", LI (Atom "a") (Atom "b")],Atom "b") ~?= True
    , provable ([LI (Atom "a") (Atom "b"),Atom "a"], Atom "b") ~?= False
    , provable ([RI (Atom "a") (Atom "b"),Atom "a"], Atom "b") ~?= True
    , provable ([Atom "a",RI (Atom "a") (Atom "b")], Atom "b") ~?= False ]


testAll = runTestTT tests

main = do
  counts <- testAll
  if errors counts == 0 && failures counts == 0 then exitSuccess else exitFailure