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
import Robot.Testing

-- An Automatic move is a move which has AutData as extra state
type AutMove = AutData -> Tableau -> Maybe (AutData, Tableau)

liftMove :: Move -> AutMove
liftMove move autData tab = case move tab of 
    Just newTab -> Just (autData, newTab) 
    Nothing -> Nothing

storedLibEquivs :: [LibraryEquivalence]
storedLibEquivs = [continuousDef, uniformLimDef, sequenceOfFunctionsDef, openSetDef, intersectionDef]

storedLibImpls :: [LibraryImplication]
storedLibImpls = [triIneq, lesserThanTrans]


(<|||>) :: AutMove -> AutMove -> AutMove
(<|||>) move1 move2 autData tab = move1 autData tab <|> move2 autData tab

waterfall :: AutMove
waterfall = autTidyAndInHyp
    <|||>   autTidyAndInTarg
    <|||>   autTidyImplInTarg
    <|||>   autPeelUniversalTarg
    <|||>   autPeelExistentialHyp
    <|||>   autPeelExistentialTarg

    <|||>   autPeelUniversalHyp
    <|||>   autCommitToHyp

    <|||>   autModusPonens
    <|||>   autRawModusPonens

    <|||>   autBackwardReasoningHyp
    <|||>   autLibForwardReasoning
    <|||>   autLibEquivTarg
    <|||>   autLibEquivHyp
    <|||>   autLibBackwardReasoning

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

autTidyAndInHyp :: AutMove
autTidyAndInHyp = liftMove $ autBase H tidyAndInHyp

autTidyAndInTarg :: AutMove
autTidyAndInTarg = liftMove $ autBase T tidyAndInTarg

-- Again, this can probably be cleaned up with template Haskell. I'll look into
-- this soon, but copy-pasting for now to see how this goes.
autPeelUniversalHyp :: AutMove
autPeelUniversalHyp autData tab =
    let hyps = getAllHypInds tab
        tryMove :: [(BoxNumber, Int)] -> Tableau -> Maybe (AutData, Tableau)
        tryMove []     _   = Nothing
        tryMove (h:hs) tab = case peelUniversalHyp h tab of
            Just newTab -> case getHypID h autData of
                Just hid -> if hid `elem` getPeeledUniversalHyps autData
                    then tryMove hs tab
                    else Just (addPeeledUniversalHyp h autData, newTab)
                Nothing -> Just (addPeeledUniversalHyp h autData, newTab)
            Nothing -> tryMove hs tab in
    tryMove hyps tab

autModusPonens :: AutMove
autModusPonens autData tab =
    let tryOn = [(i, j) | i <- getAllHypInds tab, j <- getAllHypInds tab, i /= j]
        tryMove :: [((BoxNumber, Int), (BoxNumber, Int))] -> Tableau -> Maybe (AutData, Tableau)
        tryMove []     _   = Nothing
        tryMove ((h1, h2):hs) tab = case modusPonens h1 h2 tab of
            Just newTab -> case (getHypID h1 autData, getHypID h2 autData) of
                (Just h1id, Just h2id) -> if (h1id, h2id) `elem` getModusPonensPairs autData
                    then tryMove hs tab
                    else Just (addModusPonensPair h1 h2 autData, newTab)
                _ -> Just (addModusPonensPair h1 h2 autData, newTab)
            Nothing -> tryMove hs tab in
    tryMove tryOn tab

autRawModusPonens :: AutMove
autRawModusPonens autData tab =
    let tryOn = [(i, j) | i <- getAllHypInds tab, j <- getAllHypInds tab, i /= j]
        tryMove :: [((BoxNumber, Int), (BoxNumber, Int))] -> Tableau -> Maybe (AutData, Tableau)
        tryMove []     _   = Nothing
        tryMove ((h1, h2):hs) tab = case rawModusPonens h1 h2 tab of
            Just newTab -> case (getHypID h1 autData, getHypID h2 autData) of
                (Just h1id, Just h2id) -> if (h1id, h2id) `elem` getRawModusPonensPairs autData
                    then tryMove hs tab
                    else Just (addRawModusPonensPair h1 h2 autData, newTab)
                _ -> Just (addRawModusPonensPair h1 h2 autData, newTab)
            Nothing -> tryMove hs tab in
    tryMove tryOn tab

autBackwardReasoningHyp :: AutMove
autBackwardReasoningHyp autData tab =
    let tryOn = [(h, t) | h <- getAllHypInds tab, t <- getAllTargInds tab]
        tryMove :: [((BoxNumber, Int), (BoxNumber, Int))] -> Tableau -> Maybe (AutData, Tableau)
        tryMove []     _   = Nothing
        tryMove ((h, t):rest) tab = case backwardReasoningHyp h t tab of
            Just newTab -> Just (autData, newTab)
            Nothing -> tryMove rest tab in
    tryMove tryOn tab


autLibEquivHypWithEquiv :: LibraryEquivalence -> AutMove
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
        _ -> Nothing

-- moves that require tracking

trackTidyImplInTarg :: Tableau -> (BoxNumber, Int) -> AutData -> AutData
trackTidyImplInTarg tab targ@(boxNumber, _) autData =
    case getBox boxNumber (getRootBox tab) of
        Just (Box hyps targs) -> if length targs == 1 then
            autData else
            applyTracker autData (targDeletionTracker targ)
        _ -> autData -- Couldn't find box: leave autData unchanged

autTidyImplInTarg :: AutMove
autTidyImplInTarg autData tab =
    let targs = getAllTargInds tab
        tryMove :: [(BoxNumber, Int)] -> Maybe (AutData, Tableau)
        tryMove []     = Nothing
        tryMove (t:ts) = case tidyImplInTarg t tab of
            Just newTab -> Just (trackTidyImplInTarg tab t autData, newTab)
            Nothing -> tryMove ts in
    tryMove targs

-- The way commitToHyp is written, the box always becomes nested at index 1
trackCommitToHyp :: BoxNumber -> AutData -> AutData
trackCommitToHyp boxNumber autData = applyTracker autData $ nestTracker boxNumber 1

autCommitToHyp :: AutMove
autCommitToHyp autData tab =
    let hyps = getAllHypInds tab
        tryMove :: [(BoxNumber, Int)] -> Tableau -> Maybe (AutData, Tableau)
        tryMove []     _   = Nothing
        tryMove (h:hs) tab = let autData' = trackCommitToHyp (fst h) autData in
            case commitToHyp h tab of
            Just newTab -> case getHypID h autData of
                Just hid -> if hid `elem` getCommittedToHyps autData
                    then tryMove hs tab
                    else Just (addCommittedToHyps h autData', newTab)
                Nothing -> Just (addCommittedToHyps h autData', newTab)
            Nothing -> tryMove hs tab in
    tryMove hyps tab
