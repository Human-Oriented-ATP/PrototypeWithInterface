{-# LANGUAGE OverloadedStrings #-}

module SubexpressionMatchingTests (subexpressionMatchingTests) where

import Robot.Lib
import Robot.Parser
import Robot.TableauFoundation
import Robot.LibraryMoves
import Robot.HoleExpr

import Test.HUnit

subexpressionMatchingTests :: Test
subexpressionMatchingTests = TestLabel "Subexpression matching tests" $ (TestList
    [test1, test2, test3, test4, test5, test6])

-- <<< Tests for navigating within expressions >>>

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

-- <<< Tests for subLibraryEquivalence >>>

Just eqSubstQZone = parseQZone "forall a, forall b, forall P"
Just eqSubstCond = parseWithQZone eqSubstQZone "eq(a, b)"
Just eqSubsta = parseWithQZone eqSubstQZone "P(a)"
Just eqSubstb = parseWithQZone eqSubstQZone "P(b)"
eqSubst = LibraryEquivalence eqSubstQZone [holeFreeVars eqSubstCond]
        (map holeFreeVars [eqSubsta, eqSubstb])

Just testQZone1 = parseQZone "forall a, forall b"
Just testHyp1 = parseWithQZone testQZone1 "eq(a, b)"
Just testExpr2 = parseWithQZone testQZone1 "forall P, P(a)"
Just testExpr3 = parseWithQZone testQZone1 "forall P, P(b)"

testTab1 = Tableau testQZone1 (Box [testHyp1] [PureTarg testExpr2])
resultTab1 = Tableau testQZone1 (Box [testHyp1] [PureTarg testExpr3])

testTab2 = Tableau testQZone1 (Box [testHyp1, testExpr2] [PureTarg (Con "True")])
resultTab2 = Tableau testQZone1 (Box [testHyp1, testExpr3] [PureTarg (Con "True")])

test4 :: Test
test4 = TestCase (assertEqual "eqSubst in target" [resultTab1]
    (subLibraryEquivalence eqSubst (0, 1) T ([], 0) [GoRight, Enter] testTab1))

test5 :: Test
test5 = TestCase (assertEqual "eqSubst in hypothesis" [resultTab2]
    (subLibraryEquivalence eqSubst (0, 1) H ([], 1) [GoRight, Enter] testTab2))

-- Multiple possible outputs
Just testQZone2 = parseQZone "forall a, forall b, forall c"
Just testHyp2 = parseWithQZone testQZone1 "eq(a, b)"
Just testHyp3 = parseWithQZone testQZone1 "eq(a, c)"
Just testExpr4 = parseWithQZone testQZone1 "forall P, P(a)"
Just testExpr5 = parseWithQZone testQZone1 "forall P, P(b)"
Just testExpr6 = parseWithQZone testQZone1 "forall P, P(c)"

testTab3 = Tableau testQZone2 (Box [testHyp2, testHyp3] [PureTarg testExpr4])
resultTab3a = Tableau testQZone2 (Box [testHyp2, testHyp3] [PureTarg testExpr5])
resultTab3b = Tableau testQZone2 (Box [testHyp2, testHyp3] [PureTarg testExpr6])

test6 :: Test
test6 = TestCase (assertEqual "multiple possible eqSubst" [resultTab3a, resultTab3b]
    (subLibraryEquivalence eqSubst (0, 1) T ([], 0) [GoRight, Enter] testTab3))
