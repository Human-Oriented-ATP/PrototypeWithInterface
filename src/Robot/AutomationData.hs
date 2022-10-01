{-# LANGUAGE DeriveGeneric #-}

module Robot.AutomationData where

import Robot.TableauFoundation

import GHC.Generics
import Data.Aeson (FromJSON, ToJSON)

data AutData = AutData {
    -- keep track of which universal hypotheses we've peeled
    -- so we don't peel them again
    getPeeledUniversalHyps :: [(BoxNumber, Int)]
} deriving (Show, Generic, Read)

startAutData :: AutData
startAutData = AutData []

addPeeledUniversalHyp :: (BoxNumber, Int) -> AutData -> AutData
addPeeledUniversalHyp peeledUniversalHyp (AutData peeledUniversalHyps) = AutData {
    getPeeledUniversalHyps = peeledUniversalHyp:peeledUniversalHyps
}

instance ToJSON AutData
instance FromJSON AutData
