{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS -Wno-unused-imports #-}

module Robot.PPrinting where

import Robot.Poset
import Robot.Lib
import Robot.TableauFoundation


import Data.Hashable
import Data.HashSet (HashSet)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.String (IsString(..))
import Data.List
import Control.Monad.State
import Data.Maybe
import Debug.Trace
import Text.Read (Lexeme(String))
import GHC.Generics
import Data.Aeson (FromJSON, ToJSON, decode, toJSON)


-- <<< Pretty printing expressions >>>

-- | For displaying unicode symbols written phonetically in English properly.
htmlEntityCodes :: HashMap String String
htmlEntityCodes = M.fromList [("delta", "\948"), ("epsilon", "\949"), ("theta", "\952")]

-- | A PrintingState contains the showMap from InternalName's to ExternalName's
-- a list of used ExternalName's, and a counter keeping track of the largest
-- InternalName encountered thus far (allowing us to choose a free one if need be)
data PrintingState = PS
  { getShowMap :: HashMap InternalName ExternalName
  , getUsedNames :: HashSet ExternalName
  , getCounter :: Int
  }

-- | Given an ExternalName and PrintingState, returns the PrintingState corresponding
-- to the simple choice of that externalName being used, along with the first 
-- free InternalName available (and returns the (inNm, exNm))
getSuggestion' :: ExternalName -> State PrintingState (InternalName, ExternalName)
getSuggestion' x = do
  PS m s n <- get
  let r = n
  put (PS (M.insert r x m) (S.insert x s) (n+1))
  return (r, x)

basicNames :: [ExternalName]
basicNames = [ExternalName (x : replicate n '\'') | n <- [0..], x <- alph]
  where alph = "abcdefghijklmnopqrstuvwxyz"

unusedName :: HashSet ExternalName -> ExternalName
unusedName s = head $ filter (not . (`S.member` s)) basicNames

-- | Takes a PrintingState and returns a new PrintingState and (inNm, exNm)
-- corresponding to choosing the first free ExternalName
getFresh :: State PrintingState (InternalName, ExternalName)
getFresh = do
  (PS _ u _) <- get
  getSuggestion' (unusedName u)

-- | Takes an ExternalName and a PrintingState. If the ExternalName has been used,
-- finds a fresh one. If not, uses it. Returns the updated PrintingState along
-- with the (inNm, exNm) used.
getSuggestion :: ExternalName -> State PrintingState (InternalName, ExternalName)
getSuggestion x = do
  (PS _ y _) <- get
  if x `S.member` y
     then getFresh
     else getSuggestion' x

-- | PPrint a Scoped expression with the binder given by b using the suggested
-- ExternalName in the pprinting.
pprintBinderM :: String -> Maybe ExternalName -> Scoped -> State PrintingState String
pprintBinderM b sug sc = do
  (m, ExternalName sug') <- maybe getFresh getSuggestion sug -- If there's an ExternalName, getsSuggestion. If it's a Nothing, getsFresh
  s <- pprintExprM $ instantiate (Free m) sc
  return $ case sug' `M.lookup` htmlEntityCodes of
    Just str -> b ++ str ++ ", " ++ s
    Nothing -> b ++ sug' ++ ", " ++ s

-- | Allows us to print things like "forall x in X, ..." rather than
-- forall x, x in X implies, ... ...
pprintBinderWithDomM :: String -> Maybe ExternalName -> String -> Expr -> Scoped -> State PrintingState String
pprintBinderWithDomM b sug intermediateStr dom sc = do
  (m, ExternalName sug') <- maybe getFresh getSuggestion sug
  s <- pprintExprM $ instantiate (Free m) sc
  do
    domOut <- pprintExprM dom
    return $ case sug' `M.lookup` htmlEntityCodes of
      Just str -> b ++ str ++ intermediateStr ++ domOut ++ ", " ++ s
      Nothing -> b ++ sug' ++ intermediateStr ++ domOut ++ ", " ++ s

-- | PPrints to expressions with a specified string between them. Useful for things
-- like a = b, or a < b.
pprintWithStringBetween :: Expr -> Expr -> String -> State PrintingState String
pprintWithStringBetween a b str = do
  outA <- pprintExprM a
  outB <- pprintExprM b
  return $ outA ++ str ++ outB

-- | PPrints an expression
pprintExprM :: Expr -> State PrintingState String
-- Special patterns (these must come first!)
-- forall/exists with domains
pprintExprM (Forall sug sc@(Sc (Implies (BApp "element_of" (B 0) dom) q))) =
  pprintBinderWithDomM "\8704" sug " \8712 " dom (Sc q)
pprintExprM (Exists sug sc@(Sc (And (BApp "element_of" (B 0) dom) q))) = 
  pprintBinderWithDomM "\8707" sug " \8712 " dom (Sc q)
pprintExprM (Forall sug sc@(Sc (Implies (BApp "real_greater_than" (B 0) expr) q))) = 
  pprintBinderWithDomM "\8704" sug " > " expr (Sc q)
pprintExprM (Exists sug sc@(Sc (And (BApp "real_greater_than" (B 0) expr) q))) = 
  pprintBinderWithDomM "\8707" sug " > " expr (Sc q)
pprintExprM (Forall sug sc@(Sc (Implies (BApp "real_lesser_than" (B 0) expr) q))) = 
  pprintBinderWithDomM "\8704" sug " < " expr (Sc q)
pprintExprM (Exists sug sc@(Sc (And (BApp "real_lesser_than" (B 0) expr) q))) = 
  pprintBinderWithDomM "\8707" sug " < " expr (Sc q)
-- general forall/exists
pprintExprM (Forall sug sc) = pprintBinderM "\8704" sug sc
pprintExprM (Exists sug sc) = pprintBinderM "\8707" sug sc
-- implies
pprintExprM (Implies a b) = do
  outA <- pprintExprM a
  outB <- pprintExprM b
  return $ "(" ++ outA ++ " \8658  " ++ outB ++ ")"
-- and
pprintExprM (And a b) = do
  outA <- pprintExprM a
  outB <- pprintExprM b
  return $ "(" ++ outA ++ " \8743 " ++ outB ++ ")"
-- constant function applications which can be displayed more nicely
pprintExprM (BApp "element_of" a dom) = pprintWithStringBetween a dom " \8712 "
pprintExprM (BApp "real_lesser_than" a dom) = pprintWithStringBetween a dom " < "
pprintExprM (BApp "real_greater_than" a dom) = pprintWithStringBetween a dom " > "
pprintExprM (TApp "function" f x y) = do
  fOut <- pprintExprM f
  xOut <- pprintExprM x
  yOut <- pprintExprM y
  return $ fOut ++ ":" ++ xOut ++ "\8594" ++ yOut
-- constants that can be displayed more nicely
pprintExprM (Con "naturals") = do return "\8469"
pprintExprM (Con "0") = do return "0"

-- General patterns
pprintExprM t@(App _ _) = do
  let (f, x) = getAppChain t
  fs <- pprintExprM f
  xs <- traverse pprintExprM (reverse x)
  return $ fs ++ "(" ++ intercalate ", " xs ++ ")"
pprintExprM (Free x) = do
  (PS m _ _) <- get
  let name = getExternalName $ m M.! x
  let htmlCode = name `M.lookup` htmlEntityCodes
  return $ case htmlCode of
    Just something -> handleUnderscores something
    _ -> handleUnderscores name
pprintExprM (Con s) = return $ "\\texttt{" ++ s ++ "}"
pprintExprM (Abs sug sc) = pprintBinderM "λ" sug sc
pprintExprM (B _) = error "term not closed"


handleUnderscores :: String -> String
handleUnderscores str = case reverse str of
  ('_':rest) -> reverse ("_\\"++rest)
  normal -> reverse normal


-- | Takes a QZone and finds a legitimate ordering of the quantified variables
-- in the QZone.
orderQZone :: QZone -> [QuantifiedVariable]
orderQZone (Poset [] _) = []
orderQZone qZone@(Poset set rel) = let
  (nextUp:xs) = filter (not . hasParent qZone) set -- WARNING - this might cause the program to crash if pattern match fails, but shouldn't happen otherwise there isn't an ordering?
  in nextUp : orderQZone (Poset (delete nextUp set) rel)


-- | Takes a QZone and returns an updated PrintingState taking it into account
-- (e.g. if a variable is quantified over, it should appear in the usedNames, 
-- and have a showMap entry)
getStartingPrintState :: QZone -> PrintingState -> PrintingState
getStartingPrintState (Poset [] _) state = state -- if there are no quantified variables in the QZone, we have nothing to do
getStartingPrintState qZone@(Poset set rel) (PS showMap usedNames counter) = let
  (qVar@(QVar quantifier exNm inNm):xs) = set
  newQZone = Poset xs []
  useInNm = findExNameFromInName usedNames inNm
  name = case exNm of
    Just str -> if not $ str `S.member` usedNames then str else useInNm
    Nothing -> useInNm
  newMap = M.insert inNm name showMap
  newUsedNames = S.insert name usedNames
  newState = PS newMap newUsedNames (max (counter + 1) (maximum (map qVarGetInternalName set)))
  in getStartingPrintState newQZone newState

-- | Takes a HashSet of used ExternalName's, and an InternalName, and generates a unique ExternalName for this
findExNameFromInName :: HashSet ExternalName -> InternalName -> ExternalName
findExNameFromInName usedNames inNm = let alph = map (\c -> [c]) ['a'..'z']
  in unusedNameFromOptions usedNames (basicNamesFromAlphabet alph)

unusedNameFromOptions :: HashSet ExternalName -> [ExternalName] -> ExternalName
unusedNameFromOptions s options = head $ filter (not . (`S.member` s)) options

basicNamesFromAlphabet :: [String] -> [ExternalName]
basicNamesFromAlphabet alph = [ExternalName (x ++ replicate n '\'') | n <- [0..], x <- alph]

-- | PPrint an expression with context given by a QZone
pprintExprWithQZone :: QZone -> Expr -> String
pprintExprWithQZone qZone e = evalState (pprintExprM e) (getStartingPrintState qZone (PS mempty mempty 0))

-- | PPrint an expression with no context
pprintExpr :: Expr -> String
pprintExpr e = evalState (pprintExprM e) (PS mempty mempty 0)


-- | Just a Tableau with Box String instead of Box Expr and String instead of QZone
data PrettyTableau = PrettyTableau {getPrettyQZone :: String,
                                    getPrettyRootBox :: Box String} deriving (Eq, Read, Show, Generic)
instance ToJSON PrettyTableau
instance FromJSON PrettyTableau

-- | Prettifies a tab by pprinting its expressions and pprinting its QZone
prettifyTab :: Tableau -> PrettyTableau
prettifyTab (Tableau qZone box) = let PS showMap usedNames counter = getStartingPrintState qZone (PS mempty mempty 0)
  in PrettyTableau (pprintQZone qZone) (fmap (pprintExprWithQZone qZone) box)

-- | PPrints a QZone without dependencies
pprintQZone :: QZone -> String
pprintQZone qZone = let
  PS showMap usedNames counter = getStartingPrintState qZone (PS mempty mempty 0)
  dealWithEmpty str = if str /= "" then str else "(empty)"
  dealWithHtmlCode :: String -> String
  dealWithHtmlCode str = fromMaybe str (str `M.lookup` htmlEntityCodes)
  qListToStr = dealWithEmpty . intercalate ", " . map (\qVar -> (if qVarGetQuantifier qVar == "Forall" then "\8704" else "\8707") ++ handleUnderscores (dealWithHtmlCode (getExternalName (showMap M.! qVarGetInternalName qVar))))
  in qListToStr $ orderQZone qZone

-- | PPrints a QZone with dependencies
pprintQZoneDeps :: QZone -> String
pprintQZoneDeps qZone@(Poset set rel) = let
  PS showMap usedNames counter = getStartingPrintState qZone (PS mempty mempty 0)
  dealWithEmpty str = if str /= "" then str else "(empty)"
  dealWithHtmlCode :: String -> String
  dealWithHtmlCode str = fromMaybe str (str `M.lookup` htmlEntityCodes)
  depsStr = dealWithEmpty . intercalate ", " $ map (\(q1, q2) -> handleUnderscores (dealWithHtmlCode (getExternalName (showMap M.! qVarGetInternalName q1))) ++ "<" ++ handleUnderscores (dealWithHtmlCode (getExternalName (showMap M.! qVarGetInternalName q2)))) rel
  in depsStr

-- | PPrints a BoxNumber
boxNumberToStr :: BoxNumber -> String
boxNumberToStr [] = "R"
boxNumberToStr boxNumber = intercalate "." (map show boxNumber)

-- | PPrints a box (mostly for debugging, as interface is nicer)
printBoxForDebug :: BoxNumber -> Box String -> String
printBoxForDebug boxNumber (Box hyps targs) = let
  hypsStr = intercalate "\n" $
    zipWith (\hypInd hyp -> boxNumberToStr boxNumber ++ "." ++ show hypInd ++ ": " ++ hyp) [0..] hyps
  pprintTarg :: BoxNumber -> Int -> Targ String -> String
  pprintTarg boxNumber' targInd (PureTarg s) = boxNumberToStr boxNumber' ++ "." ++ show targInd ++ ": " ++ s
  pprintTarg boxNumber' targInd (BoxTarg s) = printBoxForDebug (boxNumber'++[targInd]) s

  targsStr = intercalate "\n" $
    zipWith (pprintTarg boxNumber) [0..] targs
  in "\n-----------------\nHyps (" ++ boxNumberToStr boxNumber ++ ")\n-----------------\n"
  ++ hypsStr ++
  "\n-----------------\nTargs ("++ boxNumberToStr boxNumber ++ ")\n-----------------\n"
  ++ targsStr

-- | PPrints a Tableau for debug
printTabForDebug :: Tableau -> String
printTabForDebug tab@(Tableau qZone rootBox) = let
  PrettyTableau _ prettyRootBox = prettifyTab tab
  qZoneStr = pprintQZone qZone
  qZoneDeps = pprintQZoneDeps qZone
  rootBoxStr = printBoxForDebug [] prettyRootBox
  in "QZone: " ++ qZoneStr ++ "\n-----------------\n"
    ++ "Deps: " ++ qZoneDeps ++ rootBoxStr