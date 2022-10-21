{-# OPTIONS -Wno-unused-imports #-}

module Robot.HoleExpr where

import Robot.Poset
import Robot.Lib
import Robot.TableauFoundation
import Robot.PPrinting

import Data.List ( nub )


-- | The type of expressions with the addition of variables in the sense of unification.
data HoleExpr
  = HoleApp HoleExpr HoleExpr
    -- ^ A function application. Note that the function itself can be an expression.
  | HoleAbs (Maybe ExternalName) HoleScoped
    -- ^ An abstraction (eg \(x \mapsto x^2\)).
  | HoleFree InternalName
    -- ^ A free variable.
  | HoleCon String
    -- ^ A constant (eg the naturals, or the sin function).
  | HoleB Int
    -- ^ A bound variable
  | Hole InternalName
    -- ^ A hole variable to be filled
  deriving (Eq, Show) 

newtype HoleScoped = HoleSc HoleExpr
  deriving (Eq, Show)

-- | Takes an expression and gives the corresponding holed expression
exprToHoleExpr :: Expr -> HoleExpr
exprToHoleExpr (App e e') = HoleApp (exprToHoleExpr e) (exprToHoleExpr e')
exprToHoleExpr (Abs exNm (Sc sc)) = HoleAbs exNm (HoleSc (exprToHoleExpr sc))
exprToHoleExpr (Free n) = HoleFree n
exprToHoleExpr (Con con) = HoleCon con
exprToHoleExpr (B i) = HoleB i

-- | Takes an expression and gives the holed expression obtained by turning all free variables into holes
holeFreeVars :: Expr -> HoleExpr
holeFreeVars (App e e') = HoleApp (holeFreeVars e) (holeFreeVars e')
holeFreeVars (Abs exNm (Sc sc)) = HoleAbs exNm (HoleSc (holeFreeVars sc))
holeFreeVars (Free n) = Hole n
holeFreeVars (Con con) = HoleCon con
holeFreeVars (B i) = HoleB i

-- | Takes a holed expression without holes and returns an expression (Maybe because there might be holes)
holeExprToExpr :: HoleExpr -> Maybe Expr
holeExprToExpr (HoleApp e e') = do
    a <- holeExprToExpr e
    b <- holeExprToExpr e'
    return $ App a b
holeExprToExpr (HoleAbs exNm (HoleSc sc)) = do
    a <- holeExprToExpr sc
    return $ Abs exNm (Sc a)
holeExprToExpr (HoleFree n) = Just $ Free n
holeExprToExpr (HoleCon con) = Just $ Con con
holeExprToExpr (HoleB i) = Just $ B i
holeExprToExpr (Hole _) = Nothing


-- IMPROVEMENT - probably change to HashMap later, but will keep as list for now
type Substitution = [(InternalName, Expr)]

-- Add a single assignment to a substitution. Maybe because consistency
-- could fail
addAssignment :: Substitution -> (InternalName, Expr) -> Maybe Substitution
addAssignment sub (i, expr) = case lookup i sub of
    Nothing -> Just ((i, expr):sub)
    Just expr' -> if expr == expr' then Just sub else Nothing

-- | Check that all InternalNames map to things which agree, then union
-- (there are more efficient ways to do this, of course)
mergeSubstitutions :: Substitution -> Substitution -> Maybe Substitution
mergeSubstitutions s1 s2 = 
    let attempt = nub (s1 ++ s2)
        agree = map fst attempt == nub (map fst attempt)
    in if agree then Just attempt else Nothing

-- | Asks if we can get the second expression from the first by substituting terms for holes correctly.
matchExpressions :: HoleExpr -> Expr -> Maybe Substitution
matchExpressions (HoleApp e1 e2) (App e1' e2') = do
    sub1 <- matchExpressions e1 e1'
    sub2 <- matchExpressions e2 e2'
    mergeSubstitutions sub1 sub2
matchExpressions (HoleAbs _ (HoleSc sc1)) (Abs _ (Sc sc2)) = matchExpressions sc1 sc2
matchExpressions (HoleCon s) (Con s') = if s == s' then Just [] else Nothing
matchExpressions (HoleB i) (B i') = if i == i' then Just [] else Nothing
matchExpressions (HoleFree n) (Free n') = if n == n' then Just [] else Nothing
matchExpressions (Hole i) expr = Just [(i, expr)]-- IMPROVEMENT - currently doesn't check that expr is a term (as now have removed constant types)
matchExpressions _ _ = Nothing

-- Check whether the non-hole parts of the expressions match
basicMatchCheck :: HoleExpr -> Expr -> Bool
basicMatchCheck (HoleApp e1 e2) (App e1' e2') = basicMatchCheck e1 e1' &&
                                                basicMatchCheck e2 e2'
basicMatchCheck (HoleAbs _ (HoleSc sc)) (Abs _ (Sc sc')) = basicMatchCheck sc sc'
basicMatchCheck (HoleCon s) (Con s') = s == s'
basicMatchCheck (HoleFree n) (Free n') = n == n'
basicMatchCheck (HoleB i) (B i') = i == i'
basicMatchCheck (Hole _) _ = True
basicMatchCheck _ _ = False

-- | Performs a given substitution on an expression
applySubstitution :: Substitution -> HoleExpr -> HoleExpr
applySubstitution [] expr = expr
applySubstitution ((inNm, subExpr):rest) expr = applySubstitution rest (singleSub inNm subExpr expr) where
    singleSub :: InternalName -> Expr -> HoleExpr -> HoleExpr
    singleSub i e (Hole j) = if i == j then exprToHoleExpr e else Hole j
    singleSub i e (HoleApp e1 e2) = HoleApp (singleSub i e e1) (singleSub i e e2)
    singleSub i e (HoleAbs exNm (HoleSc sc)) = HoleAbs exNm (HoleSc (singleSub i e sc))
    singleSub _ _ (HoleFree j) = HoleFree j
    singleSub _ _ (HoleCon conS) = HoleCon conS
    singleSub _ _ (HoleB j) = HoleB j

-- returns a list giving the ExprDirections to each hole, along with
-- the identifier of each hole
getHoleDirections :: HoleExpr -> [(ExprDirections, InternalName)]
getHoleDirections (HoleApp e1 e2) =
    (map (\(dirs, nm) -> (GoLeft:dirs, nm)) $ getHoleDirections e1) ++
    (map (\(dirs, nm) -> (GoRight:dirs, nm)) $ getHoleDirections e2)
getHoleDirections (HoleAbs _ (HoleSc e)) =
    (map (\(dirs, nm) -> (Enter:dirs, nm)) $ getHoleDirections e)
getHoleDirections (Hole nm) = [([], nm)]
getHoleDirections _ = []

-- Takes a HoleExpr and directions to a hole and instantiates the
-- hole with a given expr
instantiateOneHole :: HoleExpr -> ExprDirections -> Expr -> Maybe HoleExpr
instantiateOneHole (Hole _) [] e = Just $ exprToHoleExpr e
instantiateOneHole (HoleApp x y) (GoLeft:rest) e = do
                                newx <- instantiateOneHole x rest e
                                Just $ HoleApp newx y
instantiateOneHole (HoleApp x y) (GoRight:rest) e = do
                                newy <- instantiateOneHole y rest e
                                Just $ HoleApp x newy
instantiateOneHole (HoleAbs nm (HoleSc x)) (Enter:rest) e = do
                                newx <- instantiateOneHole x rest e
                                Just $ HoleAbs nm (HoleSc newx)
instantiateOneHole _ _ _ = Nothing
