module Robot.NewBinderIdentifiers where

import Robot.Lib
import Robot.HoleExpr

type ExprIdentifier = Int

-- A new binder identifier consists of an expression identifier
-- together with directions for reaching the binder from the root
-- of the identifed expression
data NBI = NBI { getExprIdentifier :: Int,
                 getDirections :: ExprDirections } 

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
