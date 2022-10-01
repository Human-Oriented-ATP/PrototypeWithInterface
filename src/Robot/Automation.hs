{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use first" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Redundant $" #-}
{-# HLINT ignore "Redundant if" #-}
{-# HLINT ignore "Use bimap" #-}
{-# OPTIONS -Wno-unused-imports #-}

module Robot.Automation where

import Robot.Lib
import Robot.TableauFoundation
import Robot.Poset
import Robot.PPrinting
import Robot.BasicMoves
import Robot.LibraryMoves
import Robot.AutomationData

import Data.Maybe
import Data.List
import Control.Monad
import Control.Applicative
import Debug.Trace

-- An Automatic move is a move which has AutData as extra state
type AutMove = AutData -> Tableau -> Maybe (AutData, Tableau)

liftMove :: Move -> AutMove
liftMove move autData tab = case move tab of 
    Just newTab -> Just (autData, newTab) 
    Nothing -> Nothing

waterfall :: AutMove
waterfall autData tab = autPeelUniversalTarg autData tab
                    <|> autTidyImplInTarg autData tab
                    <|> autPeelExistentialHyp autData tab
                    <|> autPeelExistentialTarg autData tab
                    <|> autPeelUniversalHyp autData tab
                    <|> autTidyAndInTarg autData tab
                    <|> autTidyAndInHyp autData tab

-- Enum data type: Targets or Hypotheses
data ExprType = T | H

-- Avoid repeating code by having a function which automates trying
-- to apply a move on all hypotheses / all targets
autBase :: ExprType -> ((BoxNumber, Int) -> Move) -> Move
autBase exprType move tab =
    let exprs = case exprType of
            T -> getAllTargInds tab
            H -> getAllHypInds tab
        tryMove :: [(BoxNumber, Int)] -> Move
        tryMove []     _   = Nothing
        tryMove (e:es) tab = case move e tab of
            Just newTab -> Just newTab
            Nothing -> tryMove es tab in
    tryMove exprs tab

autPeelUniversalTarg :: AutMove
autPeelUniversalTarg = liftMove $ autBase T peelUniversalTarg

autPeelExistentialHyp :: AutMove
autPeelExistentialHyp = liftMove $ autBase H peelExistentialHyp

autPeelExistentialTarg :: AutMove
autPeelExistentialTarg = liftMove $ autBase T peelExistentialTarg

autTidyImplInTarg :: AutMove
autTidyImplInTarg = liftMove $ autBase T tidyImplInTarg

autTidyAndInHyp :: AutMove
autTidyAndInHyp = liftMove $ autBase H tidyAndInHyp

autTidyAndInTarg :: AutMove
autTidyAndInTarg = liftMove $ autBase T tidyAndInTarg

autPeelUniversalHyp :: AutMove
autPeelUniversalHyp autData tab =
    let hyps = getAllHypInds tab
        tryMove :: [(BoxNumber, Int)] -> Tableau -> Maybe (AutData, Tableau)
        tryMove []     _   = Nothing
        tryMove (h:hs) tab = case peelUniversalHyp h tab of
            Just newTab -> if h `elem` getPeeledUniversalHyps autData
                then tryMove hs tab
                else Just (addPeeledUniversalHyp h autData, newTab)
            Nothing -> tryMove hs tab in
    tryMove hyps tab
