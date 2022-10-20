{-|
Adapted from
<http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.66.6645&rep=rep1&type=pdf>
/[MM] I am not a number: I am a free variable - Conor McBride and James McKinna/.
-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}

module Robot.Lib where

import Data.Hashable
import Data.String (IsString(..))
import Data.List ( union )
import GHC.Generics
import Data.Aeson (FromJSON, ToJSON)
import Control.Monad

-- | A type to represent external variable names.
newtype ExternalName = ExternalName { getExternalName :: String }
  deriving (Eq, Ord, Show, Hashable, Read, Generic)

type InternalName = Int

-- For convenience
instance IsString ExternalName where
  fromString = ExternalName


-- | The type of terms with free variables of type v.
data Expr
  = App Expr Expr
    -- ^ A function application. Note that the function itself can be an expression.
  | Abs (Maybe ExternalName) Scoped
    -- ^ An abstraction (eg \(x \mapsto x^2\)).
  | Free InternalName
    -- ^ A free variable.
  | Con String
    -- ^ A constant (eg the naturals, or the sin function).
  | B Int
    -- ^ A bound variable
  deriving (Eq, Show, Read, Generic) 


newtype Scoped = Sc Expr
  deriving (Eq, Show, Read, Generic)

instance ToJSON Scoped
instance ToJSON Expr
instance ToJSON ExternalName
instance FromJSON Scoped
instance FromJSON Expr
instance FromJSON ExternalName

-- | Check for equality of expressions up to alpha-equivalence.
class AlphaEq t where
  (~=) :: t -> t -> Bool

-- | Equality of scoped expressions, up to alpha equivalence.
instance AlphaEq Scoped where
  Sc x ~= Sc y = x ~= y

-- | Equality of expressions, up to alpha equivalence.
instance AlphaEq Expr where
  App f x ~= App g y = f ~= g && x ~= y
  Abs _ x ~= Abs _ y = x ~= y
  Free n  ~= Free m  = n == m
  Con s   ~= Con t   = s == t
  B i     ~= B j     = i == j
  _       ~= _       = False

-- | Example: Peano's first axiom as an expression
peanoOne :: Expr
peanoOne = App (Con "forall") $ Abs (Just "x") $ Sc $ App (Con "forall") $ Abs (Just "y") $ Sc $ App (Con "not") $
  App (App (Con "eq") $ App (Con "succ") (B 0)) $ App (Con "succ") (B 1)

apps :: Expr -> [Expr] -> Expr
apps e [] = e
apps e (x : xs) = apps (App e x) xs

-- f                       -> (f, [])
-- App f x                 -> (f, [x])
-- App (App f x) y         -> (f, [y, x])
-- App (App (App g x) y) z -> (g, [z, y, x])
getAppChain :: Expr -> (Expr, [Expr])
getAppChain (App f x) = (g, x:t)
  where (g, t) = getAppChain f
getAppChain t = (t, [])

-- | Unary application of a constant function to an expression.
pattern UApp :: String -> Expr -> Expr
pattern UApp f x = App (Con f) x

-- | Binary application of a constant function to an expression.
pattern BApp :: String -> Expr -> Expr -> Expr
pattern BApp f x y = App (App (Con  f) x) y

-- | Just for convenience, though could just use apps and write the Con explicitly
pattern TApp :: String -> Expr -> Expr -> Expr -> Expr
pattern TApp f x y z = App (App (App (Con f) x) y) z

pattern QApp :: String -> Expr -> Expr -> Expr -> Expr -> Expr
pattern QApp f a b c d = App (App (App (App (Con f) a) b) c) d

pattern PApp :: String -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr
pattern PApp f a b c d e = App (App (App (App (App (Con f) a) b) c) d) e

pattern HApp :: String -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr
pattern HApp f a b c d e g = App (App (App (App (App (App (Con f) a) b) c) d) e) g

pattern TAnd :: Expr -> Expr -> Expr -> Expr
pattern TAnd x y z = And (And x y) z

pattern QAnd :: Expr -> Expr -> Expr -> Expr -> Expr
pattern QAnd a b c d = And (And (And a b) c) d

pattern PAnd :: Expr -> Expr -> Expr -> Expr -> Expr -> Expr
pattern PAnd a b c d e = And (And (And (And a b) c) d) e

pattern HAnd :: Expr -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr
pattern HAnd a b c d e f = And (And (And (And (And a b) c) d) e) f

-- | The conjunction of two expressions.
pattern And :: Expr -> Expr -> Expr
pattern And x y = App (App (Con "and") x) y

-- | The disjunction of two expressions.
pattern Or :: Expr -> Expr -> Expr
pattern Or x y = App (App (Con "or") x) y

-- | The implication of two expressions.
pattern Implies :: Expr -> Expr -> Expr
pattern Implies x y = App (App (Con "implies") x) y

-- | The negation of an expression.
pattern Not :: Expr -> Expr
pattern Not x = App (Con "not") x

-- | Equality of two expressions.
pattern Eq :: Expr -> Expr -> Expr
pattern Eq x y = App (App (Con "eq") x) y

pattern Forall :: Maybe ExternalName -> Scoped -> Expr
pattern Forall x y = App (Con "forall") (Abs x y)

pattern Exists :: Maybe ExternalName -> Scoped -> Expr
pattern Exists x y = App (Con "exists") (Abs x y)

abstract :: InternalName -> Expr -> Scoped
abstract n e = Sc (nameTo 0 e) where
  nameTo i (App f x)       = App (nameTo i f) (nameTo i x)
  nameTo i (Abs nm (Sc b)) = Abs nm (Sc (nameTo (i+1) b))
  nameTo i (Free m)
    | m == n               = B i
  nameTo _ t               = t -- otherwise, B and Con cases

instantiate :: Expr -> Scoped -> Expr
instantiate im (Sc b) = replace 0 b where
  replace i (Abs nm (Sc m)) = Abs nm (Sc (replace (i+1) m))
  replace i (App f x) = App (replace i f) (replace i x)
  replace i (B m)
    | i == m    = im
  replace _ t = t

forall :: Maybe ExternalName -> InternalName -> Expr -> Expr
forall m x exp = Forall m (abstract x exp)

exists :: Maybe ExternalName -> InternalName -> Expr -> Expr
exists m x p = Exists m (abstract x p)

instantiateAbs :: Expr -> Expr -> Maybe Expr
instantiateAbs (Abs _ p) x = Just (instantiate x p)
instantiateAbs _         _ = Nothing

instantiateForall :: Expr -> Expr -> Maybe (Maybe ExternalName, Expr)
instantiateForall (Forall nm p) x = Just (nm, instantiate x p)
instantiateForall _            _  = Nothing


-- | Forget all name suggestions.
forgetSuggestions :: Expr -> Expr
forgetSuggestions (App f x)      = App (forgetSuggestions f) (forgetSuggestions x)
forgetSuggestions (Abs _ (Sc e)) = Abs Nothing (Sc (forgetSuggestions e))
forgetSuggestions (Free m)       = Free m
forgetSuggestions (Con s)        = Con s
forgetSuggestions (B i)          = B i


getFreeVars :: Expr -> [InternalName]
getFreeVars (App e e') = getFreeVars e `union` getFreeVars e'
getFreeVars (Abs _ (Sc sc)) = getFreeVars sc
getFreeVars (Free n) = [n]
getFreeVars (Con _) = []
getFreeVars (B _) = []

-- | Nothing right now.
someFunc :: IO ()
someFunc = return ()

-- <<< NAVIGATION WITHIN EXPRESSIONS >>

-- Direction for navigating within an expression.
-- GoLeft navigates from App x y to x
-- GoRight navigates from App x y to y
-- Enter navigates from Abs _ (Sc x) to x
data ExprDirection = GoLeft | GoRight | Enter
    deriving (Eq)

type ExprDirections = [ExprDirection]

followDirection :: Expr -> ExprDirection -> Maybe Expr
followDirection (App x y) GoLeft = Just x
followDirection (App x y) GoRight = Just y
followDirection (Abs _ (Sc x)) Enter = Just x
followDirection _ _ = Nothing

followDirections :: Expr -> ExprDirections -> Maybe Expr
followDirections = foldM followDirection

-- Zipper type for Expressions
-- (see http://learnyouahaskell.com/zippers for an intro to Zippers in Haskell)
type ExprZipper = (Expr, [ExprCrumb])

data ExprCrumb
    -- Crumb from going left
    = LeftCrumb Expr
    -- Crumb from going right
    | RightCrumb Expr
    -- Crumb from entering an abstraction
    | EnterCrumb (Maybe ExternalName)
    deriving (Eq, Show)

-- zipper versions of above functions
zFollowDirection :: ExprZipper -> ExprDirection -> Maybe ExprZipper
zFollowDirection ((App x y), crumbs) GoLeft = Just (x, (LeftCrumb y):crumbs)
zFollowDirection ((App x y), crumbs) GoRight = Just (y, (RightCrumb x):crumbs)
zFollowDirection ((Abs nm (Sc x)), crumbs) Enter = Just (x, (EnterCrumb nm):crumbs)
zFollowDirection _ _ = Nothing

zFollowDirections :: ExprZipper -> ExprDirections -> Maybe ExprZipper
zFollowDirections = foldM zFollowDirection

zGoUp :: ExprZipper -> Maybe ExprZipper
-- if we're already at the top, can't go up
zGoUp (e, []) = Nothing
zGoUp (e, (LeftCrumb e'):crumbs) = Just (App e e', crumbs)
zGoUp (e, (RightCrumb e'):crumbs) = Just (App e' e, crumbs)
zGoUp (e, (EnterCrumb nm):crumbs) = Just (Abs nm (Sc e), crumbs)

unzipper :: ExprZipper -> Expr
unzipper (e, []) = e
unzipper exprZipper = let Just newZipper = zGoUp exprZipper
    in unzipper newZipper
