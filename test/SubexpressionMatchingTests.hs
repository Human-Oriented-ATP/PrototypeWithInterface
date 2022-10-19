{-# LANGUAGE OverloadedStrings #-}

module SubexpressionMatchingTests (subexpressionMatchingTests) where

import Robot.Lib

import Test.HUnit

subexpressionMatchingTests :: Test
subexpressionMatchingTests = TestLabel "Subexpression matching tests" $ (TestList
    [test1, test2, test3])

testExpr1 :: Expr
-- (exists y, Q(y)) and (forall x, P(x))
testExpr1 = And (Exists (Just "y") (Sc (App (Con "Q") (B 0))))
                (Forall Nothing (Sc (App (Con "P") (B 0))))

directions1 :: ExprDirections
directions1 = [GoLeft, GoRight, GoRight, Enter]

resultExpr1 :: Expr
resultExpr1 = App (Con "Q") (B 0)

resultZipper1 :: ExprZipper
resultZipper1 = (App (Con "Q") (B 0),
    [EnterCrumb (Just "y"),
    RightCrumb (Con "exists"),
    RightCrumb (Con "and"),
    LeftCrumb (Forall Nothing (Sc (App (Con "P") (B 0))))])

test1 :: Test
test1 = TestCase (assertEqual "Directions to Expr" (Just resultExpr1)
    (followDirections testExpr1 directions1))

test2 :: Test
test2 = TestCase (assertEqual "Directions to ExprZipper" (Just resultZipper1)
    (zFollowDirections (testExpr1, []) directions1))

test3 :: Test
test3 = TestCase (assertEqual "Unzipping an Expr" testExpr1
    (unzipper resultZipper1))
