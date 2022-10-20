module Robot.NewBinderIdentifiers where

import Robot.Lib
import Robot.HoleExpr

import Control.Monad

type ExprIdentifier = Int

-- A new binder identifier consists of an expression identifier
-- together with directions for reaching the binder from the root
-- of the identifed expression
data NBI = NBI { getExprIdentifier :: Int,
                 getDirections :: ExprDirections }
    deriving (Eq)

-- An NBIExpr is an expression that allows bound variables to be
-- stored not as De Bruijn indices, but using new binder identifiers.
-- see definition of Expr (in Robot.Lib) for further information
data NBIExpr
    = NBIApp NBIExpr NBIExpr
    | NBIAbs (Maybe ExternalName) NBIScoped
    | NBIFree InternalName
    | NBICon String
    -- we still allow deBruijn indices, as NBIB
    | NBIB Int
    | NBINBI NBI

newtype NBIScoped = NBISc NBIExpr

-- We don't care when external names don't match, so we need
-- to provide our own instance for Eq
instance Eq NBIExpr where
    (==) (NBIApp e1 e2) (NBIApp e1' e2') = e1 == e1' && e2 == e2'
    (==) (NBIAbs _ sc) (NBIAbs _ sc') = sc == sc'
    (==) (NBIFree n) (NBIFree n') = n == n'
    (==) (NBICon s) (NBICon s') = s == s'
    (==) (NBIB i) (NBIB i') = i == i'
    (==) (NBINBI nbi) (NBINBI nbi') = nbi == nbi'

instance Eq NBIScoped where
    (==) (NBISc e) (NBISc e') = e == e'

-- A substitution assigning NBI expressions to hole numbers
type NBISub = [(InternalName, NBIExpr)]

-- Tries to add an assignment to a substitution and succeeds if it is
-- consistent
addAssignment :: NBISub -> (InternalName, NBIExpr) -> Maybe NBISub
addAssignment sub (i, expr) = case lookup i sub of
    Nothing -> Just ((i, expr):sub)
    Just expr' -> if expr == expr' then Just sub else Nothing

matchSubExpression :: (Expr, Int) -> ExprDirections -> (HoleExpr, Int) -> Maybe NBISub
matchSubExpression (rootExpr, rootID) directions (holeExpr, matchID) = do
    matchExpr <- followDirections rootExpr directions
    guard $ basicMatchCheck holeExpr matchExpr
    return []
