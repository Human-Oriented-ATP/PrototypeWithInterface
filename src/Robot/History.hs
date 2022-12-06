{-# LANGUAGE DeriveGeneric #-}

module Robot.History where

import Robot.AutomationData
import Robot.TableauFoundation

import GHC.Generics
import Control.Monad

import Data.Aeson (FromJSON, ToJSON)

-- | History item is a data type storing the relevent information for
-- our problem state at a given point in time
data HistoryItem = HistoryItem { getOldTableau :: Tableau,
                                getOldAutData :: AutData }
    deriving (Show, Read, Generic)

-- | The History is effectively a stack of history items,
-- implemented as a list.
-- Design decision: History includes the present, so that we don't
-- need to look in two places when doing analysis on present/history.
-- first should be the present.
type History = [HistoryItem]

instance ToJSON HistoryItem
instance FromJSON HistoryItem

-- | Remove the top entry in the history, effectively going back in time one step.
-- Fails if there is no history
historyBackInTimeStep :: (MonadPlus m) => History -> m History
historyBackInTimeStep [] = mzero
historyBackInTimeStep (historyItem:history) = return history

-- | Returns the top entry in the history, which should be the present.
-- Fails if there is no history
historyPresent :: (MonadPlus m) => History -> m HistoryItem
historyPresent [] = mzero
historyPresent (historyItem:history) = return historyItem
