{-# LANGUAGE DeriveGeneric #-}

module Robot.AutomationData where

import Robot.TableauFoundation

import GHC.Generics
import Data.Aeson (FromJSON, ToJSON)

data AutData = AutData {
    -- keep track of which universal hypotheses we've peeled
    -- so we don't peel them again
    getPeeledUniversalHyps :: [(BoxNumber, Int)],
    getModusPonensPairs :: [((BoxNumber, Int), (BoxNumber, Int))],
    getRawModusPonensPairs :: [((BoxNumber, Int), (BoxNumber, Int))],
    getLibEquivHyps :: [(BoxNumber, Int)],
    getLibEquivTargs :: [(BoxNumber, Int)],
    getCommittedToHyps :: [(BoxNumber, Int)]
} deriving (Show, Generic, Read)

startAutData :: AutData
startAutData = AutData [] [] [] [] [] []

-- This boilerplate code could be reduced with Lens and template Haskell but
-- I'll avoid that for now because it's no effort to just copy paste these.
addPeeledUniversalHyp :: (BoxNumber, Int) -> AutData -> AutData
addPeeledUniversalHyp peeledUniversalHyp autData = let 
    peeledUniversalHyps = getPeeledUniversalHyps autData
    in autData { getPeeledUniversalHyps = peeledUniversalHyp:peeledUniversalHyps}

addModusPonensPair :: (BoxNumber, Int) -> (BoxNumber, Int) -> AutData -> AutData
addModusPonensPair h1 h2 autData = let 
    already = getModusPonensPairs autData
    in autData { getModusPonensPairs = (h1, h2):already}

addRawModusPonensPair :: (BoxNumber, Int) -> (BoxNumber, Int) -> AutData -> AutData
addRawModusPonensPair h1 h2 autData = let 
    already = getRawModusPonensPairs autData
    in autData { getRawModusPonensPairs = (h1, h2):already}

addLibEquivHyp :: (BoxNumber, Int) -> AutData -> AutData
addLibEquivHyp h autData = let 
    already = getLibEquivHyps autData
    in autData { getLibEquivHyps = h:already}

addLibEquivTarg :: (BoxNumber, Int) -> AutData -> AutData
addLibEquivTarg t autData = let 
    already = getLibEquivTargs autData
    in autData { getLibEquivTargs = t:already}

addCommittedToHyps :: (BoxNumber, Int) -> AutData -> AutData
addCommittedToHyps t autData = let 
    already = getCommittedToHyps autData
    in autData { getCommittedToHyps = t:already}


instance ToJSON AutData
instance FromJSON AutData
