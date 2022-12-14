{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Robot.MathematicianMonad where

import Robot.AutomationData
import Robot.History
import Robot.TableauFoundation

import Control.Monad.State
import GHC.Generics
import Data.Aeson (FromJSON, ToJSON)

-- | The state we have in the monad is called MathematicianState
data MathematicianState = MathematicianState
    { returnFreshName :: Int,
      -- ^ An integer larger than all the names of free variables.
      -- ready to be used as a new name
      returnAutData :: AutData,
      returnHistory :: History }
      deriving (Show, Read, Generic)

instance ToJSON MathematicianState
instance FromJSON MathematicianState

-- | The Mathematician monad combines State and Maybe capabilities
type Mathematician = StateT MathematicianState Maybe

-- | Lifting function mainly used to turn Maybes into Mathematicians
liftMaybe :: (MonadPlus m) => Maybe a -> m a
liftMaybe (Just x) = return x
liftMaybe Nothing = mzero

-- | Get a fresh name and increment the counter
getFreshName :: MonadState MathematicianState m => m Int
getFreshName = do
    state <- get
    let freshName = returnFreshName state
    put $ state { returnFreshName = freshName + 1 }
    return freshName

getAutData :: MonadState MathematicianState m => m AutData
getAutData = do
    state <- get
    return $ returnAutData state

putAutData :: MonadState MathematicianState m => AutData -> m ()
putAutData autData = do
    state <- get
    put $ state { returnAutData = autData }

updateAutData :: MonadState MathematicianState m => (AutData -> AutData) -> m ()
updateAutData f = modify (\state -> state { returnAutData = f $ returnAutData state })

-- | Function to be called thus when a move is complete:
-- result tab
-- This is to ensure the tableau is added to the history
result :: MonadState MathematicianState m => Tableau -> m Tableau
result tab = do
    state <- get
    let history = returnHistory state
    let present = HistoryItem tab (returnAutData state)
    put $ state { returnHistory = present:history }
    return tab

getHistory :: MonadState MathematicianState m => m History
getHistory = do
    state <- get
    return $ returnHistory state

baseMathematicianState :: MathematicianState
baseMathematicianState = MathematicianState 1 startAutData []

runMathematician :: Mathematician a -> MathematicianState -> Maybe (a, MathematicianState)
runMathematician = runStateT
