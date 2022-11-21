{-# LANGUAGE DeriveGeneric #-}

module Robot.History where

import Robot.AutomationData
import Robot.TableauFoundation

import GHC.Generics
import Control.Monad

-- | History item is a data type storing the relevent information for
-- our problem state at a given point in time
data HistoryItem = HistoryItem { getOldTableau :: Tableau,
                                getOldAutData :: AutData }
    deriving (Show, Read, Generic)

infix 5 :=>
-- | The History is effectively a stack of history items.
-- Design decision: History includes the present, so that we don't
-- need to look in two places when doing analysis on present/history.
-- Top of the stack should be the present.
data History = NoHistory | History :=> HistoryItem
    deriving (Show, Read, Generic)

-- | Remove the top entry in the history, effectively going back in time one step.
-- Fails if there is no history
historyBackInTimeStep :: (MonadPlus m) => History -> m History
historyBackInTimeStep NoHistory = mzero
historyBackInTimeStep (history :=> historyItem) = return history

-- | Returns the top entry in the history, which should be the present.
-- Fails if there is no history
historyPresent :: (MonadPlus m) => History -> m HistoryItem
historyPresent NoHistory = mzero
historyPresent (history :=> historyItem) = return historyItem
