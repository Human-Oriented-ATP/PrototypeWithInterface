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

{-
storedLibEquivs :: [LibraryEquivalence]
storedLibEquivs = [continuousDef, uniformLimDef, sequenceOfFunctionsDef, openSetDef, intersectionDef]

storedLibImpls :: [LibraryImplication]
storedLibImpls = [triIneq, lesserThanTrans]
-}

infixl <||>
(<||>) :: Move -> Move -> Move
(<||>) move1 move2 tab = move1 tab <|> move2 tab

waterfall :: Move
waterfall = autTidyAndInHyp
      <||>   autTidyAndInTarg
      <||>   autTidyImplInTarg
      <||>   autPeelUniversalTarg
      <||>   autPeelExistentialHyp
      <||>   autPeelExistentialTarg

      <||>   autPeelUniversalHyp
      <||>   autCommitToHyp

      <||>   autModusPonens
      <||>   autRawModusPonens

      <||>   autBackwardReasoningHyp

      {-    TODO : refactor the moves below so they are in the Mathematician monad
      <||>   autLibForwardReasoning
      <||>   autLibEquivTarg
      <||>   autLibEquivHyp
      <||>   autLibBackwardReasoning
      -}

tidyEverything :: Move
tidyEverything tab = let
    tidyOnce :: Move
    tidyOnce =  autTidyAndInHyp
            <||> autTidyAndInTarg
            <||> autTidyImplInTarg
            <||> autPeelUniversalTarg
            <||> autPeelExistentialHyp in
    (do newTab <- tidyOnce tab
        tidyEverything newTab) <|> return tab

-- Avoid repeating code by having a function which automates trying
-- to apply a move on all hypotheses / all targets
autBase :: ExprType -> ((BoxNumber, Int) -> Move) -> Move
autBase exprType move tab =
    let exprs = case exprType of
            T -> getAllTargInds tab
            H -> getAllHypInds tab
        tryMove :: [(BoxNumber, Int)] -> Move
        tryMove []     _   = mzero
        tryMove (e:es) tab = move e tab <|> tryMove es tab in
    tryMove exprs tab

autBase2 :: ExprType -> ExprType ->
    ((BoxNumber, Int) -> (BoxNumber, Int) -> Move) -> Move
autBase2 exprType1 exprType2 move tab =
    let exprs1 = case exprType1 of
            T -> getAllTargInds tab
            H -> getAllHypInds tab
        exprs2 = case exprType2 of
            T -> getAllTargInds tab
            H -> getAllHypInds tab
        tryMove :: [((BoxNumber, Int), (BoxNumber, Int))] -> Move
        tryMove []     _   = mzero
        tryMove ((e1, e2):es) tab = move e1 e2 tab <|> tryMove es tab in
    tryMove [(e1, e2) | e1 <- exprs1, e2 <- exprs2] tab

autPeelUniversalTarg :: Move
autPeelUniversalTarg = autBase T peelUniversalTarg

autPeelExistentialHyp :: Move
autPeelExistentialHyp = autBase H peelExistentialHyp

autPeelExistentialTarg :: Move
autPeelExistentialTarg = autBase T peelExistentialTarg

autTidyAndInHyp :: Move
autTidyAndInHyp = autBase H tidyAndInHyp

autTidyAndInTarg :: Move
autTidyAndInTarg = autBase T tidyAndInTarg

-- Again, this can probably be cleaned up with template Haskell. I'll look into
-- this soon, but copy-pasting for now to see how this goes.
autPeelUniversalHyp :: Move
autPeelUniversalHyp = autBase H peelUniversalHyp

autModusPonens :: Move
autModusPonens = autBase2 H H modusPonens

autRawModusPonens :: Move
autRawModusPonens = autBase2 H H rawModusPonens

autBackwardReasoningHyp :: Move
autBackwardReasoningHyp = autBase2 H T backwardReasoningHyp

autTidyImplInTarg :: Move
autTidyImplInTarg = autBase T tidyImplInTarg

autCommitToHyp :: Move
autCommitToHyp = autBase H commitToHyp

{-
autLibEquivHypWithEquiv :: LibraryEquivalence -> Move
autLibEquivHypWithEquiv libEquiv@(LibraryEquivalence _ _ equivalents) autData tab =
    let hyps = getAllHypInds tab
        tryMove :: [(BoxNumber, Int)] -> Tableau -> (Int, Int) -> Maybe (AutData, Tableau)
        tryMove []     _   _   = Nothing
        tryMove (h:hs) tab (i, j) = case libEquivHyp libEquiv (i, j) h tab of
            Just newTab -> case getHypID h autData of
                Just hid -> if hid `elem` getLibEquivHyps autData
                    then tryMove hs tab (i, j)
                    else Just (addLibEquivHyp h autData, newTab)
                Nothing -> Just (addLibEquivHyp h autData, newTab)
            Nothing -> tryMove hs tab (i, j)
        viableSwaps = [(i, j)
            | i <- [0..length equivalents-1], j <- [0..length equivalents-1], i /= j]
        results = mapMaybe (tryMove hyps tab) viableSwaps
    in case results of
        (res:_) -> Just res
        _ -> Nothing

autLibEquivHyp :: AutMove
autLibEquivHyp autData tab = let
    results = mapMaybe (\libEquiv -> autLibEquivHypWithEquiv libEquiv autData tab)
        storedLibEquivs
    in case results of
        (res:_) -> Just res
        _ -> Nothing

autLibEquivTargWithEquiv :: LibraryEquivalence -> AutMove
autLibEquivTargWithEquiv libEquiv@(LibraryEquivalence _ _ equivalents) autData tab =
    let targs = getAllTargInds tab
        tryMove :: [(BoxNumber, Int)] -> Tableau -> (Int, Int) -> Maybe (AutData, Tableau)
        tryMove []     _   _   = Nothing
        tryMove (t:ts) tab (i, j) = case libEquivTarg libEquiv (i, j) t tab of
            Just newTab -> case getTargID t autData of
                Just tid -> if tid `elem` getLibEquivTargs autData
                    then tryMove ts tab (i, j)
                    else Just (addLibEquivTarg t autData, newTab)
                Nothing -> Just (addLibEquivTarg t autData, newTab)
            Nothing -> tryMove ts tab (i, j)
        viableSwaps = [(i, j)
            | i <- [0..length equivalents-1], j <- [0..length equivalents-1], i /= j]
        results = mapMaybe (tryMove targs tab) viableSwaps
    in case results of
        (res:_) -> Just res
        _ -> Nothing

autLibEquivTarg :: AutMove
autLibEquivTarg autData tab = let
    results = mapMaybe (\libEquiv -> autLibEquivTargWithEquiv libEquiv autData tab) storedLibEquivs
    in case results of
        (res:_) -> Just res
        _ -> Nothing


autLibForwardReasoningWithImpl :: LibraryImplication -> AutMove
autLibForwardReasoningWithImpl libImpl = liftMove $ libForwardReasoning libImpl

autLibForwardReasoning :: AutMove
autLibForwardReasoning autData tab = let
    results = mapMaybe (\libImpl -> autLibForwardReasoningWithImpl libImpl autData tab) storedLibImpls
    in case results of
        (res:_) -> Just res
        _ -> Nothing

autLibBackwardReasoningWithImpl :: LibraryImplication -> AutMove
autLibBackwardReasoningWithImpl libImpl = liftMove $ libBackwardReasoning libImpl

autLibBackwardReasoning :: AutMove
autLibBackwardReasoning autData tab = let
    results = mapMaybe (\libImpl -> autLibBackwardReasoningWithImpl libImpl autData tab) storedLibImpls
    in case results of
        (res:_) -> Just res
        _ -> Nothing -}

