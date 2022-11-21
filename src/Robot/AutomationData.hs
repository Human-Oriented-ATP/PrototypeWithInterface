{-# LANGUAGE DeriveGeneric #-}

module Robot.AutomationData where

import Robot.TableauFoundation

import Control.Monad
import GHC.Generics
import Data.Aeson (FromJSON, ToJSON)
import Data.Maybe
import Data.Tuple

type HypID = Int
type TargID = Int

data AutData = AutData {
    -- keep track of hypotheses/targets used by various moves
    -- so we don't get stuck in a loop by using them again
    getPeeledUniversalHyps :: [HypID],
    getModusPonensPairs :: [(HypID, HypID)],
    getRawModusPonensPairs :: [(HypID, HypID)],
    getLibEquivHyps :: [HypID],
    -- ^ Currently not in use. To track this properly, we would need to know the
    -- library result id
    getLibEquivTargs :: [TargID],
    -- ^ Currently not in use. To track this properly, we would need to know the
    -- library result id
    getCommittedToHyps :: [HypID],

    getHypLookupTable :: ([((BoxNumber, Int), HypID)], Int), -- Int at the end is
    getTargLookupTable :: ([((BoxNumber, Int), TargID)], Int) -- guaranteed clean id
} deriving (Show, Generic, Read)

startAutData :: AutData
startAutData = AutData [] [] [] [] [] [] ([], 0) ([], 0)

-- Functions registering a hypothesis/target if not already present in the
-- lookup tables. The id is returned along with the autData
registerHyp :: (BoxNumber, Int) -> AutData -> (AutData, HypID)
registerHyp hyp autData =
    let (table, newID) = getHypLookupTable autData in
        case lookup hyp table of
            Just id -> (autData, id)
            Nothing -> (autData { getHypLookupTable = ((hyp, newID):table, newID+1)},
                        newID)

registerTarg :: (BoxNumber, Int) -> AutData -> (AutData, TargID)
registerTarg targ autData =
    let (table, newID) = getTargLookupTable autData in
        case lookup targ table of
            Just id -> (autData, id)
            Nothing -> (autData { getTargLookupTable = ((targ, newID):table, newID+1)},
                        newID)

-- Lookup functions. Think of the monad m as being a Maybe,
-- included to account for failure. (Sometimes we want the monad
-- to be Mathematician, otherwise we would just have said Maybe)
getHypID :: (MonadPlus m) => (BoxNumber, Int) -> AutData -> m HypID
getHypID hyp autData = case lookup hyp $ fst $ getHypLookupTable autData of
    Just hid -> return hid
    Nothing -> mzero

getTargID :: (MonadPlus m) => (BoxNumber, Int) -> AutData -> m TargID
getTargID targ autData = case lookup targ $ fst $ getTargLookupTable autData of
    Just tid -> return tid
    Nothing -> mzero

getHypFromID :: (MonadPlus m) => HypID -> AutData -> m (BoxNumber, Int)
getHypFromID hypID autData =
    case lookup hypID $ map swap $ fst $ getHypLookupTable autData of
        Just hyp -> return hyp
        Nothing -> mzero

getTargFromID :: (MonadPlus m) => TargID -> AutData -> m (BoxNumber, Int)
getTargFromID targID autData =
    case lookup targID $ map swap $ fst $ getTargLookupTable autData of
        Just targ -> return targ
        Nothing -> mzero

-- This boilerplate code could be reduced with Lens and template Haskell but
-- I'll avoid that for now because it's no effort to just copy paste these.
addPeeledUniversalHyp :: (BoxNumber, Int) -> AutData -> AutData
addPeeledUniversalHyp h autData = let
    already = getPeeledUniversalHyps autData
    (autData', id) = registerHyp h autData
    in autData' { getPeeledUniversalHyps = id:already}

addModusPonensPair :: (BoxNumber, Int) -> (BoxNumber, Int) -> AutData -> AutData
addModusPonensPair h1 h2 autData = let 
    already = getModusPonensPairs autData
    (autData', id1) = registerHyp h1 autData
    (autData'', id2) = registerHyp h2 autData'
    in autData'' { getModusPonensPairs = (id1, id2):already}

addRawModusPonensPair :: (BoxNumber, Int) -> (BoxNumber, Int) -> AutData -> AutData
addRawModusPonensPair h1 h2 autData = let 
    already = getRawModusPonensPairs autData
    (autData', id1) = registerHyp h1 autData
    (autData'', id2) = registerHyp h2 autData'
    in autData'' { getRawModusPonensPairs = (id1, id2):already}

addLibEquivHyp :: (BoxNumber, Int) -> AutData -> AutData
addLibEquivHyp h autData = let 
    already = getLibEquivHyps autData
    (autData', id) = registerHyp h autData
    in autData' { getLibEquivHyps = id:already}

addLibEquivTarg :: (BoxNumber, Int) -> AutData -> AutData
addLibEquivTarg t autData = let 
    already = getLibEquivTargs autData
    (autData', id) = registerTarg t autData
    in autData' { getLibEquivTargs = id:already}

addCommittedToHyp :: (BoxNumber, Int) -> AutData -> AutData
addCommittedToHyp h autData = let
    already = getCommittedToHyps autData
    (autData', id) = registerHyp h autData
    in autData' { getCommittedToHyps = id:already}


instance ToJSON AutData
instance FromJSON AutData

-- | Functions which keep track of the new (BoxNumber,Int) values after a move.
-- Maybe because the hypothesis/target might have been deleted.
type HypTracker = (BoxNumber, Int) -> Maybe (BoxNumber, Int)
type TargTracker = (BoxNumber, Int) -> Maybe (BoxNumber, Int)
type Tracker = (HypTracker, TargTracker)

applyTracker :: Tracker -> AutData -> AutData
applyTracker (hypTracker, targTracker) autData =
    let (hypLookup, hypCounter) = getHypLookupTable autData
        (targLookup, targCounter) = getTargLookupTable autData
        newHypLookup = mapMaybe (
            \(hyp, id) -> case hypTracker hyp of
                Just hyp' -> Just (hyp', id)
                Nothing -> Nothing
            ) hypLookup
        newTargLookup = mapMaybe(
            \(targ, id) -> case targTracker targ of
                Just targ' -> Just (targ', id)
                Nothing -> Nothing
            ) targLookup in
    autData {getHypLookupTable = (newHypLookup, hypCounter),
            getTargLookupTable = (newTargLookup, targCounter)}

-- Trackers for the deletion of a target
targDeletionTargTracker :: (BoxNumber, Int) -> TargTracker
targDeletionTargTracker (delBoxNumber, delInt) (trackBoxNumber, trackInt) =
    case getPrefixDiff trackBoxNumber delBoxNumber of
        Just suffix -> case suffix of
            [] -> case delInt `compare` trackInt of
                LT -> Just (trackBoxNumber, trackInt - 1)
                EQ -> Nothing
                GT -> Just (trackBoxNumber, trackInt)
            x:xs -> case delInt `compare` x of
                LT -> Just (delBoxNumber++(x-1):xs, trackInt)
                EQ -> Nothing
                GT -> Just (delBoxNumber++suffix, trackInt)
        Nothing -> Just (trackBoxNumber, trackInt)

targDeletionHypTracker :: (BoxNumber, Int) -> HypTracker
targDeletionHypTracker (delBoxNumber, delInt) (trackBoxNumber, trackInt) =
    case getPrefixDiff trackBoxNumber delBoxNumber of
        Just suffix -> case suffix of
            [] -> Just (trackBoxNumber, trackInt)
            x:xs -> case delInt `compare` x of
                LT -> Just (delBoxNumber++(x-1):xs, trackInt)
                EQ -> Nothing
                GT -> Just (delBoxNumber++suffix, trackInt)
        Nothing -> Just (trackBoxNumber, trackInt)

targDeletionTracker :: (BoxNumber, Int) -> Tracker
targDeletionTracker t = (targDeletionHypTracker t, targDeletionTargTracker t)

-- Trackers for when there is further nesting
-- i.e. boxNumber -> boxNumber ++ [index]
nestHypTracker :: BoxNumber -> Int -> HypTracker
nestHypTracker boxNumber index (trackBoxNumber, trackInt) =
    case getPrefixDiff trackBoxNumber boxNumber of
        Just suffix -> case suffix of
            [] -> Just (trackBoxNumber, trackInt)
            _ -> Just (boxNumber++index:suffix, trackInt)
        Nothing -> Just (trackBoxNumber, trackInt)

nestTargTracker :: BoxNumber -> Int -> TargTracker
nestTargTracker boxNumber index (trackBoxNumber, trackInt) =
    case getPrefixDiff trackBoxNumber boxNumber of
        Just suffix -> Just (boxNumber++index:suffix, trackInt)
        Nothing -> Just (trackBoxNumber, trackInt)

nestTracker :: BoxNumber -> Int -> Tracker
nestTracker boxNumber index = (nestHypTracker boxNumber index, nestTargTracker boxNumber index)
