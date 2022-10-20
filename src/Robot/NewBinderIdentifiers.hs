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

-- If we have an expression that was reached after following a series
-- of directions, with each set of directions corresponding to a nested
-- identified subexpression, we can turn the De Bruijn indices in the
-- expression into new binder identifiers. The list of nested
-- expression identifiers is innermost-first
exprToNBIExpr :: Expr -> [(ExprDirections, Int)] -> Maybe NBIExpr
exprToNBIExpr = exprToNBIExprAux 0

-- first argument is how many binders we've entered within the expr
exprToNBIExprAux :: Int -> Expr -> [(ExprDirections, Int)] -> Maybe NBIExpr
exprToNBIExprAux n (App e1 e2) dirs = do
    e1' <- exprToNBIExprAux n e1 dirs
    e2' <- exprToNBIExprAux n e2 dirs
    Just $ NBIApp e1' e2'
exprToNBIExprAux n (Abs nm (Sc e)) dirs = do
    e' <- exprToNBIExprAux (n+1) e dirs
    Just $ NBIAbs nm (NBISc e')
exprToNBIExprAux n (Free m) _ = Just $ NBIFree m
exprToNBIExprAux n (Con s) _ = Just $ NBICon s
exprToNBIExprAux n (B i) allDirections = if n > i then Just $ NBIB i else
    let remainingDepth = i-n
        binderCounts = map (\(dirs, _) -> length $ filter (==Enter) dirs) allDirections
        getNBI :: Int -> [Int] -> [(ExprDirections, Int)] -> Maybe NBI
        getNBI depth [] _ = Nothing
        getNBI depth _ [] = Nothing
        getNBI depth (count:remainingCounts) ((dirs, id):remainingDirections) =
            if count > depth then
                let getBinderDirections :: Int -> ExprDirections -> Maybe ExprDirections
                    getBinderDirections n dirs'
                        | n < 0 = Just dirs'
                        | otherwise = case dirs' of
                            [] -> Nothing
                            (GoLeft:rest) -> getBinderDirections n rest
                            (GoRight:rest) -> getBinderDirections n rest
                            (Enter:rest) -> getBinderDirections (n-1) rest in
                do  binderDirections <- getBinderDirections depth dirs
                    return $ NBI {getExprIdentifier = id,
                                  getDirections = binderDirections}
            else getNBI (depth - count) remainingCounts remainingDirections in
    do  nbi <- getNBI remainingDepth binderCounts allDirections
        Just $ NBINBI nbi

matchSubExpression :: (Expr, Int) -> ExprDirections -> (HoleExpr, Int) -> Maybe NBISub
matchSubExpression (rootExpr, rootID) directions (holeExpr, matchID) = do
    matchExpr <- followDirections rootExpr directions
    guard $ basicMatchCheck holeExpr matchExpr
    let holeDirs = getHoleDirections holeExpr
    assignments <- mapM (\(dirs, nm) -> do
        preNBIExpr <- followDirections matchExpr dirs
        nbiExpr <- exprToNBIExpr preNBIExpr [(dirs, matchID), (directions, rootID)]
        return (nm, nbiExpr)) holeDirs
    foldM addAssignment [] assignments
