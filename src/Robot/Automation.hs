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

import Data.Maybe
import Data.List
import Control.Monad
import Control.Applicative
import Debug.Trace

waterfall :: Move
waterfall tab = autPeelUniversalTarg tab
            <|> autTidyImplInTarg tab
            <|> autPeelExistentialHyp tab
            <|> autPeelExistentialTarg tab
            -- <|> autPeelUniversalHyp tab
            -- currently peeling universal hypothesis gets us stuck in
            -- a loop as the original hypothesis is maintained
            <|> autTidyAndInTarg tab
            <|> autTidyAndInHyp tab

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

autPeelUniversalTarg :: Move
autPeelUniversalTarg = autBase T peelUniversalTarg

autPeelExistentialTarg :: Move
autPeelExistentialTarg = autBase T peelExistentialTarg

autPeelExistentialHyp :: Move
autPeelExistentialHyp = autBase H peelExistentialHyp

autPeelUniversalHyp :: Move
autPeelUniversalHyp = autBase H peelUniversalHyp

autTidyImplInTarg :: Move
autTidyImplInTarg = autBase T tidyImplInTarg

autTidyAndInHyp :: Move
autTidyAndInHyp = autBase H tidyAndInHyp

autTidyAndInTarg :: Move
autTidyAndInTarg = autBase T tidyAndInTarg
