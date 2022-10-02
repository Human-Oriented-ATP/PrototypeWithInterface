{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use first" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Redundant $" #-}
{-# HLINT ignore "Redundant if" #-}
{-# HLINT ignore "Use bimap" #-}

module Robot.BasicMoves where

import Robot.Lib
import Robot.TableauFoundation
import Robot.Poset
import Robot.BasicMoveHelpers

import Control.Monad
import Data.Maybe
import Debug.Trace


-- <<< FOUNDATIONAL CODE >>>
-- IMPROVEMENT - currently there are a lot of nearly-identical functions - one for
-- hyps and one for targs. I've done it this way because it's not at all difficult
-- and I wanted to avoid possible strange behaviours, but there's certainly a nicer
-- and more "Haskell-y" way to do it. Would be nice for aesthetic purposes to find
-- and implement that.


-- | Takes a Tableau and returns an updated Tableau. Maybe because the move could fail.
type Move = Tableau -> Maybe Tableau


-- <<< NON-LIB MOVES >>>

-- PEELING

-- | Peels universal target
-- targ i : forall x, P(x)
peelUniversalTarg :: (BoxNumber, Int) -> Move
peelUniversalTarg (boxNumber, targInd) tab@(Tableau qZone@(Poset set rel) rootBox) = do
    expr@(Forall exNm sc) <- getPureTarg (boxNumber, targInd) tab
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Forall" peeledExternalName peeledName
    
    let freeVars = map (\inNm -> head $ filter (\q -> qVarGetInternalName q == inNm) set) $ getFreeVars expr
    let newDeps = [(y, peeledVariable) | y <- freeVars, qVarGetQuantifier y == "Exists"] -- We only need to add dependencies relating to exists, because dependencies between forall's is given by this
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (Tableau _ newRootBox) <- updatePureTarg (boxNumber, targInd) (instantiate (Free peeledName) sc) tab
    return $ Tableau newQZone newRootBox

-- | Peels existential target, creating a metavariable
-- targ i : exists x, P(x)
peelExistentialTarg :: (BoxNumber, Int) -> Move
peelExistentialTarg (boxNumber, targInd) tab@(Tableau qZone@(Poset set rel) rootBox) = do
    expr@(Exists exNm sc) <- getPureTarg (boxNumber, targInd) tab
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Exists" peeledExternalName peeledName
    
    let freeVars = map (\inNm -> head $ filter (\q -> qVarGetInternalName q == inNm) set) $ getFreeVars expr
    let newDeps = [(y, peeledVariable) | y <- freeVars, qVarGetQuantifier y == "Forall"] -- We only need to add dependencies relating to exists, because dependencies between forall's is given by this
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (Tableau _ newRootBox) <- updatePureTarg (boxNumber, targInd) (instantiate (Free peeledName) sc) tab
    return $ Tableau newQZone newRootBox

-- | Peels existential hypothesis
-- hyp i : exists x, P(x)
-- IMPROVEMENT - currently find new external name to prevent confusing outputs after a single move, but maybe this should happen at the print stage? Think about this.
peelExistentialHyp :: (BoxNumber, Int) -> Move
peelExistentialHyp (boxNumber, hypInd) tab@(Tableau qZone@(Poset set rel) rootBox) = do
    expr@(Exists exNm sc) <- getHyp (boxNumber, hypInd) tab
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Forall" peeledExternalName peeledName
    
    let freeVars = map (\inNm -> head $ filter (\q -> qVarGetInternalName q == inNm) set) $ getFreeVars expr
    let newDeps = [(y, peeledVariable) | y <- freeVars, qVarGetQuantifier y == "Exists"] -- We only need to add dependencies relating to exists, because dependencies between forall's is given by this
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (Tableau _ newRootBox) <- updateHyp (boxNumber, hypInd) (instantiate (Free peeledName) sc) tab
    return $ Tableau newQZone newRootBox

-- | Peels universal hypothesis, creating a metavariable
-- This move keeps the original hypothesis, because it's dangerous otherwise
-- hyp i : forall x, P(x)
peelUniversalHyp :: (BoxNumber, Int) -> Move
peelUniversalHyp (boxNumber, hypInd) tab@(Tableau qZone@(Poset set rel) rootBox) = do
    expr@(Forall exNm sc) <- getHyp (boxNumber, hypInd) tab
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Exists" peeledExternalName peeledName
    
    let freeVars = map (\inNm -> head $ filter (\q -> qVarGetInternalName q == inNm) set) $ getFreeVars expr
    let newDeps = [(y, peeledVariable) | y <- freeVars, qVarGetQuantifier y == "Forall"] -- We only need to add dependencies relating to exists, because dependencies between forall's is given by this
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (Tableau _ newRootBox) <- addHyp boxNumber (instantiate (Free peeledName) sc) tab
    return $ Tableau newQZone newRootBox


-- TIDYING

-- | Tidies implication in target
-- targ i : P \implies Q
tidyImplInTarg :: (BoxNumber, Int) -> Move
tidyImplInTarg (boxNumber, targInd) tab@(Tableau qZone rootBox) = do
    Box hyps targs <- getBox boxNumber rootBox
    PureTarg (Implies p q) <- getFromListMaybe targs targInd
    if length targs == 1 then
        addHyp boxNumber p tab >>= updatePureTarg (boxNumber, targInd) q
    else
        removeTarg (boxNumber, targInd) tab >>= addBoxTarg boxNumber (Box [p] [PureTarg q])

-- | Splits and hypotheses up
-- hyp i : P ^ Q
tidyAndInHyp :: (BoxNumber, Int) -> Move
tidyAndInHyp (boxNumber, hypInd) tab@(Tableau qZone rootBox) = do
    And p q <- getHyp (boxNumber, hypInd) tab
    updateHyp (boxNumber, hypInd) p tab >>= addHyp boxNumber q

tidyAndInTarg :: (BoxNumber, Int) -> Move
tidyAndInTarg (boxNumber, targInd) tab@(Tableau qZone rootBox) = do
    And p q <- getPureTarg (boxNumber, targInd) tab
    updatePureTarg (boxNumber, targInd) p tab >>= addPureTarg boxNumber q


-- MODUS PONENS AND BACKWARDS REASONING

-- | Performs modus ponens on hypotheses i and j
-- hyp i : forall x, P(x) \implies Q(x)
-- hyp j : P(y)
-- conclude : Q(y)
modusPonens :: (BoxNumber, Int) -> (BoxNumber, Int) -> Move
modusPonens (boxNumber1, hypInd1) (boxNumber2, hypInd2) tab@(Tableau qZone rootBox) = do
    guard $ isPrefix boxNumber1 boxNumber2 || isPrefix boxNumber2 boxNumber1
    let deepestBoxNumber = if isPrefix boxNumber1 boxNumber2 then boxNumber2 else boxNumber1

    expr@(Forall exNm (Sc (Implies px qx))) <- getHyp (boxNumber1, hypInd1) tab
    let freeVars = getFreeVars expr
    py <- getHyp (boxNumber2, hypInd2) tab
    let freeVars'@(freeVar':rest') = getFreeVars py
        toInstantiate' = filter (`notElem` freeVars) freeVars' -- Finds the freeVars in p', but not expr
    guard $ not (null toInstantiate')
    guard $ (expr /= py)
    let successes = filter (\var -> instantiate (Free var) (Sc px) == py) toInstantiate'
    guard $ length successes == 1
    let newHyp = instantiate (Free . head $ successes) (Sc qx)
    
    addHyp deepestBoxNumber newHyp tab

-- | Performs raw modus ponens on hypotheses i and j
-- hyp i : P \implies Q
-- hyp j : P
-- conclude : Q
rawModusPonens :: (BoxNumber, Int) -> (BoxNumber, Int) -> Move
rawModusPonens (boxNumber1, hypInd1) (boxNumber2, hypInd2) tab@(Tableau qZone rootBox) = do
    guard $ isPrefix boxNumber1 boxNumber2 || isPrefix boxNumber2 boxNumber1
    let deepestBoxNumber = if isPrefix boxNumber1 boxNumber2 then boxNumber2 else boxNumber1
    expr@(Implies p q) <- getHyp (boxNumber1, hypInd1) tab
    p' <- getHyp (boxNumber2, hypInd2) tab
    guard $ p' == p
    addHyp deepestBoxNumber q tab


-- | Performs backwards reasoning on hypothesis i and target j
-- hyp i  : P \implies Q
-- targ j : Q
-- replace targ j with P
backwardReasoningHyp :: (BoxNumber, Int) -> (BoxNumber, Int) -> Move
backwardReasoningHyp (boxNumber1, hypInd) (boxNumber2, targInd) tab@(Tableau qZone rootBox) = do
    guard $ isPrefix boxNumber1 boxNumber2

    expr@(Implies p q) <- getHyp (boxNumber1, hypInd) tab
    q' <- getPureTarg (boxNumber2, targInd) tab
    guard $ q == q'
    updatePureTarg (boxNumber2, targInd) p tab


-- <<< OTHER >>>

-- | Commits to the use of a particular hypothesis
-- hyp i : P \implies Q
-- add a new box with only target P and all hypotheses except i
-- replace hyp i in this box with Q
commitToHyp :: (BoxNumber, Int) -> Move
commitToHyp (boxNumber, hypInd) tab@(Tableau qZone rootBox) = do
    Implies p q <- getHyp (boxNumber, hypInd) tab
    Box hyps targs <- getBox boxNumber rootBox
    let targsWithQ = Box [q] targs
    removeAllTargs boxNumber tab >>= addPureTarg boxNumber p >>= addBoxTarg boxNumber targsWithQ


-- <<< QUALITY OF LIFE MOVES >>>

-- | To "tidy everything" we will simply repeat all the tidying moves until none of
-- them can be done. The tidying moves are:
-- peelUniversalTarg, peelExistentialHyp, tidyImplInTarg, tidyAndInHyp, tidyAndInTarg

getAllHypInds :: Tableau -> [(BoxNumber, Int)]
getAllHypInds tab@(Tableau qZone rootBox) = let
    getAllHypIndsFromZipper :: BoxZipper Expr -> BoxNumber -> [(BoxNumber, Int)]
    getAllHypIndsFromZipper zipper@(Box hyps targs, _) boxNumber =
        zip (repeat boxNumber) [0..length hyps-1] ++
        concatMap (\targInd -> case toBoxNumberFromZipper [targInd] zipper of
            Just newZipper -> getAllHypIndsFromZipper newZipper (boxNumber++[targInd])
            Nothing -> []) [0..length targs-1]
    in getAllHypIndsFromZipper (rootBox, []) []

getAllTargInds :: Tableau -> [(BoxNumber, Int)]
getAllTargInds tab@(Tableau qZone rootBox) = let
    getAllTargIndsFromZipper :: BoxZipper Expr -> BoxNumber -> [(BoxNumber, Int)]
    getAllTargIndsFromZipper zipper@(Box hyps targs, _) boxNumber = let
        pureTargs = mapMaybe (\targInd -> case targs!!targInd of
            PureTarg _ -> Just targInd
            _ -> Nothing) [0..length targs-1]
        pureTargInds = zip (repeat boxNumber) pureTargs
        in pureTargInds ++
            concatMap (\targInd -> case toBoxNumberFromZipper [targInd] zipper of
                Just newZipper -> getAllTargIndsFromZipper newZipper (boxNumber++[targInd])
                Nothing -> []) [0..length targs-1]
    in getAllTargIndsFromZipper (rootBox, []) []

-- As horrific as this looks, I think laziness means it's not too bad actually
tidyEverything :: Move
tidyEverything tab = let
    repeatOnce :: Move
    repeatOnce tab' = let
        allHypInds = getAllHypInds tab'
        allTargInds = getAllTargInds tab'
        universalTargPeels = mapMaybe (\i -> peelUniversalTarg i tab') allTargInds
        existentialHypPeels = mapMaybe (\i -> peelExistentialHyp i tab') allHypInds
        implPeels = mapMaybe (\i -> tidyImplInTarg i tab') allTargInds
        andHypPeels = mapMaybe (\i -> tidyAndInHyp i tab') allHypInds
        andTargPeels = mapMaybe (\i -> tidyAndInTarg i tab') allTargInds
        concated = universalTargPeels ++ existentialHypPeels ++ implPeels ++
            andHypPeels ++ andTargPeels
        in case concated of
            [] -> Nothing
            (res:_) -> Just res
    in case repeatOnce tab of
        Just newTab -> tidyEverything newTab
        Nothing -> Just tab
