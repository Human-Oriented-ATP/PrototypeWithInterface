{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS -Wno-unused-imports #-}

module Robot.TableauFoundation where

import Robot.Poset
import Robot.Lib

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as M
import Data.List
import GHC.Generics
import Data.Aeson (FromJSON, ToJSON, decode, toJSON)

-- <<<< TYPES DEFINING WHAT A TABLEAU IS >>>>

-- | Either "Exists" or "Forall", for now stored as a string, though we
-- could probably make this more Haskell-y with a simple algebraic data-type
type Quantifier = String

-- | A quantified variable, given by a quantifier, a suggested ExternalName, and
-- an InternalName
data QuantifiedVariable = QVar { qVarGetQuantifier :: Quantifier
                               , qVarGetExternalName :: Maybe ExternalName
                               , qVarGetInternalName :: InternalName}
  deriving (Eq, Read, Show, Generic)

-- | A QZone is a Poset of quantified variables, with the poset structure
-- determining the dependencies of the variables in the set
type QZone = Poset QuantifiedVariable

-- | The fundamental part of a Tableau. A list of hypotheses with a list of targets.
-- Importantly, each target can itself be a box, allowing for nested boxes.
data Box a = Box {getBoxHyps :: [a],
                getBoxTargs :: [Targ a]} deriving (Eq, Show, Read, Generic)
data Targ a = BoxTarg (Box a) | PureTarg a deriving (Eq, Show, Read, Generic)

-- | A Tableau is then simply a "rootBox", along with a QZone
data Tableau = Tableau {getQZone :: QZone,
                        getRootBox :: Box Expr}
                        deriving (Eq, Read, Show, Generic)

-- Enum data type: Targets or Hypotheses
data ExprType = T | H

-- | Simply for JSON requests to allow the web interface to work
instance ToJSON (Targ Expr)
instance ToJSON (Box Expr)
instance ToJSON (Box String)
instance ToJSON (Targ String)
instance ToJSON (Poset QuantifiedVariable)
instance ToJSON QuantifiedVariable
instance ToJSON Tableau
instance FromJSON (Targ Expr)
instance FromJSON (Box Expr)
instance FromJSON (Box String)
instance FromJSON (Targ String)
instance FromJSON (Poset QuantifiedVariable)
instance FromJSON (QuantifiedVariable)
instance FromJSON Tableau


-- <<< HELPER FUNCTIONS TO WORK WITH NESTED BOXES >>>

-- | Naturally a functor by acting on all expressions in the box.
instance Functor Box where
  fmap f (Box hyps targs) = Box (map f hyps) (map targf targs) where
    targf (BoxTarg box) = BoxTarg $ fmap f box
    targf (PureTarg targ) = PureTarg $ f targ

-- | To efficiently traverse the nested structure, we use a Zipper
-- (see http://learnyouahaskell.com/zippers for an intro to Zippers in Haskell)
data BoxCrumb a = Crumb [a] [Targ a] [Targ a]
type BoxZipper a = (Box a, [BoxCrumb a])

-- | BoxNumber's simply point to particular boxes. They can be viewed as a list of
-- instructions to arrive at the box from a root. So the root box is [] and
-- the first target box would be [0], while its second box would be [0, 2].
type BoxNumber = [Int]

-- | Follows the directions specified by a BoxNumber From a BoxZipper
toBoxNumberFromZipper :: BoxNumber -> BoxZipper a -> Maybe (BoxZipper a)
toBoxNumberFromZipper [] zipper = Just zipper
toBoxNumberFromZipper (nextBoxInd:rest) (Box hyps targs, crumbs)
  | nextBoxInd < 0 || nextBoxInd >= length targs = Nothing
  | otherwise = let (as, ourTarg:bs) = splitAt nextBoxInd targs in case ourTarg of
      PureTarg _ -> Nothing
      BoxTarg newBox -> let
        newCrumb = Crumb hyps as bs
        newZipper = Just (newBox, newCrumb:crumbs)
        in newZipper >>= toBoxNumberFromZipper rest

-- | Follows the directions to a BoxNumber from the root
toBoxNumberFromRoot :: BoxNumber -> Box a -> Maybe (BoxZipper a)
toBoxNumberFromRoot boxNumber box = toBoxNumberFromZipper boxNumber (box, [])

-- | Takes a BoxZipper and "goes up" a single level
goUp :: BoxZipper a -> Maybe (BoxZipper a)
goUp (_, []) = Nothing
goUp (box, crumb:rest) = let
  Crumb hyps aTargs bTargs = crumb
  newBox = Box hyps (aTargs ++ [BoxTarg box] ++ bTargs)
  in Just (newBox, rest)

-- | Takes a BoxZipper and entirely unzips it, returning the whole Box
unzipBox :: BoxZipper a -> Box a
unzipBox (box, []) = box
unzipBox zipper = let Just newZipper = goUp zipper
  in unzipBox newZipper


-- | Gets the hypInd-th hyp from a BoxZipper, if it exists
getHypInZipper :: Int -> BoxZipper a -> Maybe a
getHypInZipper hypInd (Box hyps _, _)
  | hypInd < 0 || hypInd >= length hyps = Nothing
  | otherwise = Just $ hyps !! hypInd

getPureTargInZipper :: Int -> BoxZipper a -> Maybe a
getPureTargInZipper targInd (Box _ targs, _)
  | targInd < 0 || targInd >= length targs = Nothing
  | otherwise = case targs !! targInd of
    BoxTarg _ -> Nothing
    PureTarg targ -> Just targ

getBoxTargInZipper :: Int -> BoxZipper a -> Maybe (Box a)
getBoxTargInZipper targInd (Box _ targs, _)
  | targInd < 0 || targInd >= length targs = Nothing
  | otherwise = case targs !! targInd of
    BoxTarg box -> Just box
    PureTarg _ -> Nothing

-- | Gets the box given by a BoxNumber from a given "root" box
getBox :: BoxNumber -> Box a -> Maybe (Box a)
getBox boxNumber rootBox = case toBoxNumberFromRoot boxNumber rootBox of
  Just (box, _) -> Just box
  Nothing -> Nothing

-- | Adds a hypothesis to a BoxZipper
addHypToZipper :: a -> BoxZipper a -> BoxZipper a
addHypToZipper hyp (Box hyps targs, crumbs) = (Box (hyps++[hyp]) targs, crumbs)

addPureTargToZipper :: a -> BoxZipper a -> BoxZipper a
addPureTargToZipper targ (Box hyps targs, crumbs) = (Box hyps (targs++[PureTarg targ]), crumbs)

addBoxTargToZipper :: Box a -> BoxZipper a -> BoxZipper a
addBoxTargToZipper targ (Box hyps targs, crumbs) = (Box hyps (targs++[BoxTarg targ]), crumbs)

-- | Removes the hypInd-th hypothesis from a BoxZipper
removeHypFromZipper :: Int -> BoxZipper a -> Maybe (BoxZipper a)
removeHypFromZipper hypInd (Box hyps targs, crumbs)
  | hypInd < 0 || hypInd >= length hyps = Nothing
  | otherwise = let (as, ourHyp:bs) = splitAt hypInd hyps
    in Just (Box (as++bs) targs, crumbs)

removeTargFromZipper :: Int -> BoxZipper a -> Maybe (BoxZipper a)
removeTargFromZipper targInd (Box hyps targs, crumbs)
  | targInd < 0 || targInd >= length targs = Nothing
  | otherwise = let (as, ourTarg:bs) = splitAt targInd targs
    in Just (Box hyps (as++bs), crumbs)

-- | Updates the hypInd-th hypothesis in a BoxZipper
updateHypInZipper :: Int -> a -> BoxZipper a -> Maybe (BoxZipper a)
updateHypInZipper hypInd newHyp (Box hyps targs, crumbs)
  | hypInd < 0 || hypInd >= length hyps = Nothing
  | otherwise = let (as, ourHyp:bs) = splitAt hypInd hyps
    in Just (Box (as++newHyp:bs) targs, crumbs)

updatePureTargInZipper :: Int -> a -> BoxZipper a -> Maybe (BoxZipper a)
updatePureTargInZipper targInd newTarg (Box hyps targs, crumbs)
  | targInd < 0 || targInd >= length targs = Nothing
  | otherwise = let (as, ourTarg:bs) = splitAt targInd targs
    in case ourTarg of
      PureTarg _ -> Just (Box hyps (as++PureTarg newTarg:bs), crumbs)
      BoxTarg _ -> Nothing

updateBoxTargInZipper :: Int -> Box a -> BoxZipper a -> Maybe (BoxZipper a)
updateBoxTargInZipper targInd newTarg (Box hyps targs, crumbs)
  | targInd < 0 || targInd >= length targs = Nothing
  | otherwise = let (as, ourTarg:bs) = splitAt targInd targs
    in case ourTarg of
      BoxTarg _ -> Just (Box hyps (as++BoxTarg newTarg:bs), crumbs)
      PureTarg _ -> Nothing


-- | Turns a PureTarg into a BoxTarg containing no hyps and a single targ
pureToBoxTargZipper :: Int -> BoxZipper a -> Maybe (BoxZipper a)
pureToBoxTargZipper targInd (Box hyps targs, crumbs)
  | targInd < 0 || targInd >= length targs = Nothing
  | otherwise = let (as, ourTarg:bs) = splitAt targInd targs in
    case ourTarg of
      BoxTarg _ -> Nothing
      PureTarg targ -> Just (Box hyps (as ++ BoxTarg (Box [] [PureTarg targ]):bs), crumbs)

-- | Returns all the hypotheses in a box and its parents. These are the ones
-- that can be used when trying to prove targets in this box.
getHypsUsableInBoxNumber :: BoxNumber -> Box Expr -> Maybe [Expr]
getHypsUsableInBoxNumber [] (Box rootHyps _) = Just rootHyps
getHypsUsableInBoxNumber (nextBoxInd:rest) (Box rootHyps rootTargs)
  | nextBoxInd < 0 || nextBoxInd >= length rootTargs = Nothing
  | otherwise = case rootTargs !! nextBoxInd of
      PureTarg _ -> Nothing
      BoxTarg box -> do
        lowerHyps <- getHypsUsableInBoxNumber rest box
        Just $ rootHyps ++ lowerHyps

-- | Checks whether a boxNumber is a prefix of another
-- i.e. (isPrefix a b) iff a is a parent of b
isPrefix :: BoxNumber -> BoxNumber -> Bool
isPrefix [] _ = True
isPrefix (a:_) [] = False
isPrefix (a:as) (b:bs) = a == b && isPrefix as bs

-- | Given a list of BoxNumbers, returns them in an order s.t. parents come
-- first then children. If this isn't possible (i.e. if two boxes are
-- not parent/child to each other), returns Nothing
orderBoxNumbers :: [BoxNumber] -> Maybe [BoxNumber]
orderBoxNumbers boxNumbers = let
  sortedBoxNumbers = sortBy (\a b -> length a `compare` length b) boxNumbers
  in if verifyPrefix [] (nub sortedBoxNumbers) then Just sortedBoxNumbers else Nothing
  where
    verifyPrefix :: BoxNumber -> [BoxNumber] -> Bool
    verifyPrefix _ [] = True
    verifyPrefix currentNumber (nextNumber:rest) = isPrefix currentNumber nextNumber && verifyPrefix nextNumber rest

-- | e.g. (getPrefixDiff [0,1,4,3] [0,1] = Just [4,3])
-- getPrefixDiff [0,1,4,3] [0,1,3,0,0] = Nothing 
getPrefixDiff :: BoxNumber -> BoxNumber -> Maybe BoxNumber
getPrefixDiff longer [] = Just longer
getPrefixDiff [] (a:_) = Nothing
getPrefixDiff (a:as) (b:bs) = if a == b then getPrefixDiff as bs else Nothing

-- | If the list of BoxNumber's provided can be linearly ordered then
-- returns the list of directions that one would follow from the root
-- to hit all of them in order. We carry along additional data (of type a) 
-- with us, so we can perform actions at each stage if wanted.
-- Also returns the deepest box in the list (useful because this tells us,
-- which targs we're allowed to solve using the hyps from the given boxes)
-- e.g. boxNumbersToDirections [([1,0,3], "bottom"),([1,0], "middle"),([], "root")]
-- = Just ([([], "root"), ([1, 0], "middle"), ([3], "bottom")], [1,0,3])
boxNumbersToDirections :: [(BoxNumber, a)] -> Maybe ([(BoxNumber, a)], BoxNumber)
boxNumbersToDirections boxNumbersWithData = let
  reverseSortedBoxNumbersWithData = sortBy (\b a -> length (fst a) `compare` length (fst b)) boxNumbersWithData
  traverseBoxNumbers :: [(BoxNumber, a)] -> [(BoxNumber, a)] -> Maybe [(BoxNumber, a)]
  traverseBoxNumbers trailSoFar [] = Just trailSoFar
  traverseBoxNumbers trailSoFar [thisBox] = Just (thisBox:trailSoFar)
  traverseBoxNumbers trailSoFar (thisBox:(nextBox:rest)) = -- thisBox is further down than nextBox
    case getPrefixDiff (fst thisBox) (fst nextBox) of
      Nothing -> Nothing
      Just diff -> traverseBoxNumbers ((diff, snd thisBox):trailSoFar) (nextBox:rest)
  deepestBox = case map fst reverseSortedBoxNumbersWithData of
    [] -> []
    (a:_) -> a
  in do
    directions <- traverseBoxNumbers [] reverseSortedBoxNumbersWithData
    Just (directions, deepestBox)

-- | The same as above, but returns the shallowest box (useful because this
-- tells us which hypotheses we can use in solving a list of targets)
boxNumbersToDirectionsFlipped :: [(BoxNumber, a)] -> Maybe ([(BoxNumber, a)], BoxNumber)
boxNumbersToDirectionsFlipped boxNumbersWithData = let
  reverseSortedBoxNumbersWithData = sortBy (\b a -> length (fst a) `compare` length (fst b)) boxNumbersWithData
  traverseBoxNumbers :: [(BoxNumber, a)] -> [(BoxNumber, a)] -> Maybe [(BoxNumber, a)]
  traverseBoxNumbers trailSoFar [] = Just trailSoFar
  traverseBoxNumbers trailSoFar [thisBox] = Just (thisBox:trailSoFar)
  traverseBoxNumbers trailSoFar (thisBox:(nextBox:rest)) = -- thisBox is further down than nextBox
    case getPrefixDiff (fst thisBox) (fst nextBox) of
      Nothing -> Nothing
      Just diff -> traverseBoxNumbers ((diff, snd thisBox):trailSoFar) (nextBox:rest)
  shallowestBox = case map fst (reverse reverseSortedBoxNumbersWithData) of
    [] -> []
    (a:_) -> a
  in do
    directions <- traverseBoxNumbers [] reverseSortedBoxNumbersWithData
    Just (directions, shallowestBox)


-- | This function basically only exists to help removing hyps and targs.
-- Exact same as boxNumbersToDirections, but ensures that ties in the ordering
-- are broken by forcing the second argument to be decreasing.
-- e.g. boxNumbersToDirectionsWithInt [([], 0), ([], 1), ([0,1],2), ([0,1],3)] =
-- Just ([([], 1), ([], 0), ([0,1], 3), ([], 2)], [0,1])
boxNumbersToDirectionsWithInt :: [(BoxNumber, Int)] -> Maybe ([(BoxNumber, Int)], BoxNumber)
boxNumbersToDirectionsWithInt boxNumbersWithData = let
  reverseSortedBoxNumbersWithData = sortBy (\b a -> let
    firstCompare = length (fst a) `compare` length (fst b)
    in if firstCompare /= EQ then firstCompare else snd b `compare` snd a) boxNumbersWithData
  traverseBoxNumbers :: [(BoxNumber, a)] -> [(BoxNumber, a)] -> Maybe [(BoxNumber, a)]
  traverseBoxNumbers trailSoFar [] = Just trailSoFar
  traverseBoxNumbers trailSoFar [thisBox] = Just (thisBox:trailSoFar)
  traverseBoxNumbers trailSoFar (thisBox:(nextBox:rest)) = -- thisBox is further down than nextBox
    case getPrefixDiff (fst thisBox) (fst nextBox) of
      Nothing -> Nothing
      Just diff -> traverseBoxNumbers ((diff, snd thisBox):trailSoFar) (nextBox:rest)
  shallowestBox = case map fst (reverse reverseSortedBoxNumbersWithData) of
    [] -> []
    (a:_) -> a
  in do
    directions <- traverseBoxNumbers [] reverseSortedBoxNumbersWithData
    Just (directions, shallowestBox)
