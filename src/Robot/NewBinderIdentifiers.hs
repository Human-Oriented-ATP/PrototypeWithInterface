module Robot.NewBinderIdentifiers where

import Robot.Lib
import Robot.HoleExpr

import Control.Monad
import Data.List
import Data.Tuple

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
addNBIAssignment :: NBISub -> (InternalName, NBIExpr) -> Maybe NBISub
addNBIAssignment sub (i, expr) = case lookup i sub of
    Nothing -> Just ((i, expr):sub)
    Just expr' -> if expr == expr' then Just sub else Nothing

-- Merging two substitutions together
mergeNBISubstitutions :: NBISub -> NBISub -> Maybe NBISub
mergeNBISubstitutions = foldM addNBIAssignment

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

-- Functions performing the reverse conversion
nbiExprToExpr :: NBIExpr -> [(ExprDirections, Int)] -> Maybe Expr
nbiExprToExpr = nbiExprToExprAux 0

-- first argument is how many binders we've entered within the NBIExpr
nbiExprToExprAux :: Int -> NBIExpr -> [(ExprDirections, Int)] -> Maybe Expr
nbiExprToExprAux n (NBIApp e1 e2) dirs = do
    e1' <- nbiExprToExprAux n e1 dirs
    e2' <- nbiExprToExprAux n e2 dirs
    Just $ App e1' e2'
nbiExprToExprAux n (NBIAbs nm (NBISc e)) dirs = do
    e' <- nbiExprToExprAux (n+1) e dirs
    Just $ Abs nm (Sc e')
nbiExprToExprAux n (NBIFree m) _ = Just $ Free m
nbiExprToExprAux n (NBICon s) _ = Just $ Con s
nbiExprToExprAux n (NBIB i) _ = Just $ B i
nbiExprToExprAux n (NBINBI (NBI id dirs)) allDirections = do
    relevantDirections <- lookup id (map swap allDirections)
    guard $ isPrefixOf dirs relevantDirections
    -- The number of binders inbetween the nbi and the binder thus
    -- identified is a sum consisting of three parts:
    -- 1) the number of binders entered into within the NBIExpr itself
    -- = n
    -- 2) the number of binders in the intermediate nested expressions
    -- (These expressions have different ids comapred to the one we're
    -- looking for)
    let intermediateBinderCount = sum (
            map (\(dirs', _) -> length $ filter (==Enter) dirs') $
            takeWhile (\(_,id') -> id /= id') allDirections)
    -- 3) the number of binders passed within the relevant nested
    -- expression. -1 here because we don't want to count the
    -- identified binder itself
    let finalBinderCount = (length $ filter (==Enter) relevantDirections) -
                           (length $ filter (==Enter) dirs) - 1
    Just $ B (n + intermediateBinderCount + finalBinderCount)

-- If we have an expression, some directions to a subexpression thereof,
-- and a HoleExpr that should match the subexpression, attempt the match
-- and return the substitution
matchSubExpression :: (Expr, Int) -> ExprDirections -> (HoleExpr, Int) -> Maybe NBISub
matchSubExpression (rootExpr, rootID) directions (holeExpr, matchID) = do
    matchExpr <- followDirections rootExpr directions
    guard $ basicMatchCheck holeExpr matchExpr
    let holeDirs = getHoleDirections holeExpr
    assignments <- mapM (\(dirs, nm) -> do
        preNBIExpr <- followDirections matchExpr dirs
        nbiExpr <- exprToNBIExpr preNBIExpr [(dirs, matchID), (directions, rootID)]
        return (nm, nbiExpr)) holeDirs
    mergeNBISubstitutions [] assignments

-- Same as above, apart from that it matches a whole expression rather
-- than a subexpression
matchExpression :: (Expr, Int) -> HoleExpr -> Maybe NBISub
matchExpression (expr, id) holeExpr = do
    guard $ basicMatchCheck holeExpr expr
    let holeDirs = getHoleDirections holeExpr
    assignments <- mapM (\(dirs, nm) -> do
        preNBIExpr <- followDirections expr dirs
        nbiExpr <- exprToNBIExpr preNBIExpr [(dirs, id)]
        return (nm, nbiExpr)) holeDirs
    mergeNBISubstitutions [] assignments
