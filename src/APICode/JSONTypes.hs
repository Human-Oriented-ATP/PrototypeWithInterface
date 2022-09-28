{-# LANGUAGE DeriveGeneric #-}

module APICode.JSONTypes where

import Robot.TableauFoundation

import Data.Aeson (FromJSON, ToJSON)

import GHC.Generics
import qualified Data.Text.Internal.Lazy as LT


type Move = String
data ProblemState = ProblemState {
      getTab :: Tableau
    , getTabHtml :: LT.Text
    , getAllowedActions :: [String]
    , getProofHistory :: [(Tableau, String)]}
    deriving (Show, Generic, Read)

type Action = String
data ActionState = ActionState {
    getAction :: Action,
    getProblemState :: ProblemState
    } deriving (Show, Generic, Read)
instance ToJSON ActionState
instance FromJSON ActionState

instance ToJSON ProblemState
instance FromJSON ProblemState