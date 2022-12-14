{-|
A parser for a basic Lisp-like syntax into an internal expression.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS -Wno-unused-imports #-}
{-# HLINT ignore "Use <$>" #-}

module Robot.Parser where

import Robot.Lib
import Robot.PPrinting
import Robot.TableauFoundation
import Robot.Poset
import Robot.PPrinting

import Control.Applicative hiding (many, some)
import Control.Monad.State
import Data.Foldable
import Data.Functor.Identity
import Data.HashMap.Strict (HashMap)
import Data.HashSet (HashSet)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Debug.Trace



-- Uses megaparsec with a custom state to keep track of local bindings
-- See https://markkarpov.com/tutorial/megaparsec.html for a tutorial on
-- megaparsec. In the future, might want to change the monad from StateT to
-- something else which runs mutably, but should test to see. STRef or IORef
-- might be more efficient, but also might give overheads (and IORef restricts
-- how it can be used).
type Parser =
    ParsecT Void String
    (StateT (HashMap String InternalName, Int) Identity)


-- This is the syntax I want to parse
-- expr := expr(args)
--       | forall x, expr
--       | con
--       | free
-- args := expr[,expr]*
--
-- To remove left-recursion, transform it into this syntax
-- expr     := expr-non(args)*
-- expr-non := forall x, expr
--           | con
--           | free

-- | The general expression parser.
parseExpr :: Parser Expr
parseExpr = do
    f <- parseExprNon
    i <- many parseApps
    return $ foldl' apps f i

parseExprNon :: Parser Expr
parseExprNon = parseForall <|> parseExists <|> parseFree <|> parseCon

-- | Parse a sequence of arguments
parseApps :: Parser [Expr]
parseApps = char '(' *> sepBy1 parseExpr (string ", ") <* char ')'

-- | Register a new identifier, and return its internal name
registerIdent :: MonadState (HashMap String InternalName, Int) m
              => String -> m InternalName
registerIdent s = do
  (m, i) <- get
  put (M.insert s i m, i + 1)
  return i

-- | Parse a forall expression
parseForall :: Parser Expr
parseForall = do
  _ <- string "forall "
  i <- parseIdent
  nm <- registerIdent i
    -- ^ it's important that this runs before the e <- parseExpr
  _ <- string ", "
  e <- parseExpr
  return (forall (Just (ExternalName i)) nm e)

-- | Parse an exists expression
parseExists :: Parser Expr
parseExists = do
  _ <- string "exists "
  i <- parseIdent
  nm <- registerIdent i
    -- ^ it's important that this runs before the e <- parseExpr
  _ <- string ", "
  e <- parseExpr
  return (exists (Just (ExternalName i)) nm e)

-- | Parse a free variable (must be known from the context)
parseFree :: Parser Expr
parseFree = try $ do
  i <- parseIdent
  (m, _) <- get
  case m M.!? i of
    Just n -> return $ Free n
    Nothing -> fail "unrecognised identifier"
      -- the name used wasn't recognised
      -- not sure if this error can even happen?

-- | Parse a constant
parseCon :: Parser Expr
parseCon = try (Con <$> some (letterChar <|> char '_'))
  -- this try might be unnecessary but if the syntax changes it could become
  -- crucial

-- | Parse an identifier (doesn't register it!)
parseIdent :: Parser String
parseIdent = try (some (letterChar <|> char '_'))

-- | Run the parser in the IO monad - mostly for testing.  This assumes an
-- empty context - if we already know for example that "x" means something
-- and has an existing internal name, then this doesn't apply.
parseTestT :: Show a => Parser a -> String -> IO ()
parseTestT p inp =
  case evalState (runParserT p "example" inp) (M.empty, 0) of
      -- change the (M.empty, 0) to change the context
    Left e -> putStr (errorBundlePretty e)
    Right x -> print x

-- | Run the parser, returning Just _ on success, and `Nothing` on failure.
-- This assumes an empty context - if we already know for example that "x"
-- means something and has an existing internal name, then this doesn't apply.
parseSimple :: Parser Expr -> String -> Maybe Expr
parseSimple p inp =
  case evalState (runParserT p "example" inp) (M.empty, 0) of
    Left _ -> Nothing
    Right x -> Just x

-- We will parse QZone's like this:
-- "forall x, forall y, forall z, exists a, forall b, exists c"
-- The resulting QZone has the dependencies implied by the FOL statement above

type QZoneParser =
    ParsecT Void String
    (StateT (HashSet ExternalName, Int) Identity)

-- | Register a new identifier, and return its internal name
qZoneregisterIdent :: MonadState (HashSet ExternalName, Int) m
              => ExternalName -> m InternalName
qZoneregisterIdent str = do
  (usedNames, counter) <- get
  put (S.insert str usedNames, counter + 1)
  return counter

-- | Parses an identifier, which is allowed to contain letters and underscores
-- (any other symbol indicates the end of the identifier)
qZoneParseIdent :: QZoneParser String
qZoneParseIdent = try (some (letterChar <|> char '_'))

-- | Parses forall's in the qZone
qZoneParserForall :: QZoneParser QuantifiedVariable
qZoneParserForall = do
  _ <- string "forall "
  exNmStr <- qZoneParseIdent
  (usedNames, counter) <- get
  let exNm = ExternalName exNmStr
  if S.member exNm usedNames then fail "variable repeated" else do
    inNm <- qZoneregisterIdent exNm
    (do
      _ <- string ", "
      return $ QVar "Forall" (Just exNm) inNm) <|>  (do return $ QVar "Forall" (Just exNm) inNm)

-- | Parses exists in the qZone
qZoneParserExists :: QZoneParser QuantifiedVariable
qZoneParserExists = do
  _ <- string "exists "
  exNmStr <- qZoneParseIdent
  (usedNames, counter) <- get
  let exNm = ExternalName exNmStr
  if S.member exNm usedNames then fail "variable repeated" else do
    inNm <- qZoneregisterIdent exNm
    (do
      _ <- string ", "
      return $ QVar "Exists" (Just exNm) inNm) <|>  (do return $ QVar "Exists" (Just exNm) inNm)

-- | Parses a QZone. We do this by simply writing "forall x, forall y, exists z" in order
-- the strictest dependencies will be applied (only consecutive forall's or exist's can commute)
qZoneParseOnce :: QZoneParser QuantifiedVariable
qZoneParseOnce = qZoneParserForall <|> qZoneParserExists

-- | Function to actually parse a qZone
parseQZone :: String -> Maybe QZone
parseQZone input = let
  qZoneFromListofQVars :: [QuantifiedVariable] -> [QuantifiedVariable] -> QZone -> Maybe QZone
  qZoneFromListofQVars _ [] currentQZone = Just currentQZone
  qZoneFromListofQVars [] (firstQVar:rest) currentQZone = qZoneFromListofQVars [firstQVar] rest $ addSetMember currentQZone firstQVar
  qZoneFromListofQVars (previousQVar:before) (nextQVar:after) currentQZone =
    if qVarGetQuantifier previousQVar == qVarGetQuantifier nextQVar then qZoneFromListofQVars (nextQVar:previousQVar:before) after $ addSetMember currentQZone nextQVar
    else
      do
        newQZone <- addRels (addSetMember currentQZone nextQVar) [(y, nextQVar) | y <- previousQVar:before]
        qZoneFromListofQVars (nextQVar:previousQVar:before) after newQZone
  result = evalState (runParserT (many qZoneParseOnce <* eof) "example" input) (S.empty, 0)
  in case result of
    Left _ -> Nothing
    Right x -> qZoneFromListofQVars [] x (Poset [] [])


-- IMPROVEMENT - what is the meaning of the "source file" given by the string "example"?
-- Parses an expression with the context given by a specified qZone
parseWithQZone :: QZone -> String -> Maybe Expr
parseWithQZone qZone@(Poset set rel) input =
  let
    PS showMap usedNames counter = getStartingPrintState qZone (PS mempty mempty 0)
    startingMap = M.fromList $ map (\(inNm, exNm) -> let ExternalName s = exNm in (s, inNm)) (M.toList showMap)
  in case evalState (runParserT (parseExpr <* eof) "example" input) (startingMap, counter) of
    Left _ -> Nothing
    Right x -> Just x



openSetsProblem :: Expr
openSetsProblem =
  forall (Just $ ExternalName "X") 0 $
    Implies (UApp "is_metric_space" (Free 0)) $
      forall (Just $ ExternalName "Y") 1 $
        Implies (UApp "is_metric_space" (Free 1)) $
          forall (Just $ ExternalName "f") 2 $
            Implies (apps (Con "is_function_on") [Free 2, Free 0, Free 1]) $
              forall (Just $ ExternalName "U") 3 $
                Implies (BApp "subset" (Free 3) (Free 1)) $
                  Implies (UApp "continuous" (Free 2)) $
                    Implies (UApp "open" (Free 3)) $
                      UApp "open" (App (UApp "inv_image" (Free 2)) (Free 3))
