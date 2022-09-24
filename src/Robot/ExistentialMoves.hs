{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use zipWith" #-}
module Robot.ExistentialMoves where

import Robot.Lib
import Robot.TableauFoundation
import Robot.Poset
import Robot.PPrinting
import Robot.Parser

import Control.Monad
import qualified Data.HashMap.Strict as M


-- IMPROVEMENT - currently we'll have issues inputting more complex expressions
-- because the parsing can't handle them, and there's ambiguity resolved only by
-- context in expressions like epsilon/3 (which would be represented as something)
-- like real_divide_by(epsilon, 3). Implement a solution to this.

-- | Instantiate an existentially quantified variable, x, in the QZone with a given
-- expression. We need to ensure that none of the free variables in the expression
-- must come after x. We then need to update the dependencies so that all variables
-- which had to come after x must now come after all free variables in the expression
instantiateExistentialNoParse :: InternalName -> Expr -> Tableau -> Maybe Tableau
instantiateExistentialNoParse inNm expr (Tableau qZone@(Poset set deps) rootBox) = do
    let relevantQVars = filter (\qVar -> qVarGetInternalName qVar == inNm) set
    -- Ensure the given InternalName is actually in the QZone
    guard $ not (null relevantQVars)

    let qVar = head relevantQVars
    -- Ensure the given InternalName is existentially quantified
    guard $ qVarGetQuantifier qVar == "Exists"

    let freeVarsInExpr = getFreeVars expr
    -- Can't try to substitute a variable for something which contains itself
    guard $ inNm `notElem` freeVarsInExpr
    
    -- IMPROVEMENT - Technically not safe, but should be practically unless QZone becomes ill-formed
    let qVarsInExpr = concatMap (\inNm -> filter (\qVar -> qVarGetInternalName qVar == inNm) set) freeVarsInExpr
     -- Ensure dependencies are valid
    guard $ all (\x -> not $ isAfter qZone x qVar) qVarsInExpr

    -- Now we have the all-clear to make the instantiation, and update dependencies
    let previousDependents = [y | y <- set, isAfter qZone y qVar]
    let newDeps = [(x, y) | y <- previousDependents, x <- qVarsInExpr]
    newQZone <- addRels (removeMember qZone qVar) newDeps

    let
        instantiateInExpr :: Expr -> Expr
        instantiateInExpr (App a b) = App (instantiateInExpr a) (instantiateInExpr b)
        instantiateInExpr (Abs exNm (Sc sc)) = Abs exNm (Sc (instantiateInExpr sc))
        instantiateInExpr (Con con) = Con con
        instantiateInExpr (B i) = B i
        instantiateInExpr (Free i) = if i == inNm then expr else Free i

    -- Performs the instantiate using fmap over the rootBox
    return $ Tableau newQZone (fmap instantiateInExpr rootBox)


-- | Takes a string giving the show-ExternalName of the relevant variable,
-- then a string specifying the term we want to instantiate it for.
-- Parses the information to hand onto instantiateExistentialNoParse.
instantiateExistential :: String -> String -> Tableau -> Maybe Tableau
instantiateExistential exNmStr exprStr tab@(Tableau qZone@(Poset set rel) boxes) = do
    let showMap = getShowMap $ getStartingPrintState qZone (PS mempty mempty 0)
    let inNms = filter (\n -> M.lookup n showMap == Just (ExternalName exNmStr)) (map qVarGetInternalName set)
    guard $ length inNms == 1
    let (inNm:_) = inNms
    expr <- parseWithQZone qZone exprStr
    instantiateExistentialNoParse inNm expr tab

