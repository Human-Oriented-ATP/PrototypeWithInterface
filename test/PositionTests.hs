{-# LANGUAGE OverloadedStrings #-}

module PositionTests (positionTests) where

import Robot.Lib
import Robot.TableauFoundation

import Test.HUnit

positionTests :: Test
positionTests = TestLabel "Position tests" (TestList [test1, test2, test3, test4,
    test5, test6, test7, test8, test9, test10])

testExpr1 :: Expr
testExpr1 = And (Con "A") (Con "B")

testExpr2 :: Expr
testExpr2 = Or (Con "A") (Con "B")

testExpr3 :: Expr
testExpr3 = Implies (Con "A") (Con "B")

testDirs1 :: ExprDirections
testDirs1 = [GoRight]

testDirs2 :: ExprDirections
testDirs2 = [GoLeft, GoRight]

test1 :: Test
test1 = TestCase (assertEqual "A and B" (Just Positive)
    (getPosition (exprTypeToPosition T) testExpr1 testDirs1))

test2 :: Test
test2 = TestCase (assertEqual "A and B" (Just Negative)
    (getPosition (exprTypeToPosition H) testExpr1 testDirs2))

test3 :: Test
test3 = TestCase (assertEqual "A or B" (Just Negative)
    (getPosition (exprTypeToPosition H) testExpr2 testDirs1))

test4 :: Test
test4 = TestCase (assertEqual "A or B" (Just Positive)
    (getPosition (exprTypeToPosition T) testExpr2 testDirs2))

test5 :: Test
test5 = TestCase (assertEqual "A implies B" (Just Positive)
    (getPosition (exprTypeToPosition T) testExpr3 testDirs1))

test6 :: Test
test6 = TestCase (assertEqual "A implies B" (Just Positive)
    (getPosition (exprTypeToPosition H) testExpr3 testDirs2))

testExpr4 :: Expr
testExpr4 = Not (Not (Con "A"))

testDirs3 :: ExprDirections
testDirs3 = [GoRight, GoRight]

testDirs4 :: ExprDirections
testDirs4 = [GoRight, GoLeft]

test7 :: Test
test7 = TestCase (assertEqual "not(not(A))" (Just Positive)
    (getPosition (exprTypeToPosition T) testExpr4 testDirs3))

test8 :: Test
test8 = TestCase (assertEqual "not(not(A))" Nothing
    (getPosition (exprTypeToPosition T) testExpr4 testDirs4))

testExpr5 :: Expr
testExpr5 = Forall (Just "x") (Sc (And (Con "A") (App (Con "P") (B 0))))

testDirs5 :: ExprDirections
testDirs5 = [GoRight, Enter, GoLeft, GoRight]

testExpr6 :: Expr
testExpr6 = Exists (Just "y") (Sc (Or (App (Con "Q") (B 0)) (Con "B")))

testDirs6 :: ExprDirections
testDirs6 = [GoRight, Enter, GoRight]

test9 :: Test
test9 = TestCase (assertEqual "forall x, A and P(x)" (Just Positive)
    (getPosition (exprTypeToPosition T) testExpr5 testDirs5))

test10 :: Test
test10 = TestCase (assertEqual "exists y, Q(y) or B" (Just Negative)
    (getPosition (exprTypeToPosition H) testExpr6 testDirs6))
