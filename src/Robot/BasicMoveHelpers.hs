module Robot.BasicMoveHelpers where

import Robot.Lib
import Robot.Poset
import Robot.TableauFoundation

import Data.Maybe

-- | Gets an unused InternalName from a QZone
getNewInternalName :: QZone -> InternalName
getNewInternalName (Poset set rel) = freshName (map qVarGetInternalName set)
    where
        freshName :: [InternalName] -> InternalName
        freshName [] = 0
        freshName usedNames = maximum usedNames + 1

-- | Finds a fresh ExternalName from a list of used ones
findFreshExNm :: [ExternalName] -> ExternalName
findFreshExNm usedNames = head $ filter (`notElem` usedNames) options
    where options = [ExternalName (x : replicate n '\'') | n <- [0..], x <- ['a'..'z']]

-- | Gets an ExternalName for a variable being peeled. If the peeled variable
-- already has a suggested ExternalName and it doesn't conflict with others
-- then we use that. Otherwise, we find a fresh one
getNewExternalNamePeel :: Maybe ExternalName -> QZone -> Maybe ExternalName
getNewExternalNamePeel exNm (Poset set rel) = case exNm of
    Just nm -> if nm `elem` (mapMaybe qVarGetExternalName set) then
            Just $ findFreshExNm (mapMaybe qVarGetExternalName set)
        else exNm
    _ -> Just $ findFreshExNm (mapMaybe qVarGetExternalName set)


-- | Adds a hypothesis to a specified Box. Because this is just a helper
-- function in writing moves, not a move itself, I don't use the "Move"
-- type synonym here.
addHyp :: BoxNumber -> Expr -> Tableau -> Maybe Tableau
addHyp boxNumber hyp (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    let newZipper = addHypToZipper hyp boxZipper
    Just $ Tableau qZone (unzipBox newZipper)

addPureTarg :: BoxNumber -> Expr -> Tableau -> Maybe Tableau
addPureTarg boxNumber targ (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    let newZipper = addPureTargToZipper targ boxZipper
    Just $ Tableau qZone (unzipBox newZipper)

addBoxTarg :: BoxNumber -> Box Expr -> Tableau -> Maybe Tableau
addBoxTarg boxNumber boxTarg (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    let newZipper = addBoxTargToZipper boxTarg boxZipper
    Just $ Tableau qZone (unzipBox newZipper)

-- | Repeats addHyp on many arguments in an efficient way
addHyps :: [(BoxNumber, Expr)] -> Tableau -> Maybe Tableau
addHyps addSchedule (Tableau qZone rootBox) = do
    (boxRoute, _) <- boxNumbersToDirections addSchedule
    
    let zippedBox = (rootBox, [])
        followAndAddHyps :: [(BoxNumber, Expr)] -> BoxZipper Expr -> Maybe (BoxZipper Expr)
        followAndAddHyps [] currentZipper = Just currentZipper
        followAndAddHyps ((direction, hyp):rest) currentZipper = do
            newZipper <- toBoxNumberFromZipper direction currentZipper
            Just $ addHypToZipper hyp newZipper
    
    addedHypsZipper <- followAndAddHyps boxRoute zippedBox
    let newRootBox = unzipBox addedHypsZipper
    Just $ Tableau qZone newRootBox


addPureTargs :: [(BoxNumber, Expr)] -> Tableau -> Maybe Tableau
addPureTargs addSchedule (Tableau qZone rootBox) = do
    (boxRoute, _) <- boxNumbersToDirections addSchedule
    
    let zippedBox = (rootBox, [])
        followAndAddPureTargs :: [(BoxNumber, Expr)] -> BoxZipper Expr -> Maybe (BoxZipper Expr)
        followAndAddPureTargs [] currentZipper = Just currentZipper
        followAndAddPureTargs ((direction, pureTarg):rest) currentZipper = do
            newZipper <- toBoxNumberFromZipper direction currentZipper
            Just $ addPureTargToZipper pureTarg newZipper
    
    addTargsZipper <- followAndAddPureTargs boxRoute zippedBox
    let newRootBox = unzipBox addTargsZipper
    Just $ Tableau qZone newRootBox

addBoxTargs :: [(BoxNumber, Box Expr)] -> Tableau -> Maybe Tableau
addBoxTargs addSchedule (Tableau qZone rootBox) = do
    (boxRoute, _) <- boxNumbersToDirections addSchedule
    
    let zippedBox = (rootBox, [])
        followAndAddBoxTargs :: [(BoxNumber, Box Expr)] -> BoxZipper Expr -> Maybe (BoxZipper Expr)
        followAndAddBoxTargs [] currentZipper = Just currentZipper
        followAndAddBoxTargs ((direction, boxTarg):rest) currentZipper = do
            newZipper <- toBoxNumberFromZipper direction currentZipper
            Just $ addBoxTargToZipper boxTarg newZipper
    
    addTargsZipper <- followAndAddBoxTargs boxRoute zippedBox
    let newRootBox = unzipBox addTargsZipper
    Just $ Tableau qZone newRootBox



-- | Remove a hypothesis, specified by a BoxNumber and the hyp's index within that box
-- Maybe because the specified hyp may not exist.
removeHyp :: (BoxNumber, Int) -> Tableau -> Maybe Tableau
removeHyp (boxNumber, hypInd) (Tableau qZone boxes) = do
    boxZipper <- toBoxNumberFromRoot boxNumber boxes
    newBoxZipper <- removeHypFromZipper hypInd boxZipper
    Just (Tableau qZone (unzipBox newBoxZipper))

removeTarg :: (BoxNumber, Int) -> Tableau -> Maybe Tableau
removeTarg (boxNumber, targInd) (Tableau qZone boxes) = do
    boxZipper <- toBoxNumberFromRoot boxNumber boxes
    newBoxZipper <- removeTargFromZipper targInd boxZipper
    Just (Tableau qZone (unzipBox newBoxZipper))

removeAllTargs :: BoxNumber -> Tableau -> Maybe Tableau
removeAllTargs boxNumber (Tableau qZone boxes) = do
    (Box hyps targs, crumbs) <- toBoxNumberFromRoot boxNumber boxes
    Just (Tableau qZone (unzipBox (Box hyps [], crumbs)))

-- | Helper function to remove the i-th element from a list if it exists
-- and otherwise return Nothing
removeFromListMaybe :: [a] -> Int -> Maybe [a]
removeFromListMaybe l i
    | i < 0 || i >= length l = Nothing
    | otherwise = let
        (as, _:bs) = splitAt i l
        in Just $ as++bs

-- | Repeats removeHyp on many arguments in an efficient way
removeHyps :: [(BoxNumber, Int)] -> Tableau -> Maybe Tableau
removeHyps removeSchedule tab@(Tableau qZone rootBox) = do
    (orderedRemoveSchedule, _) <- boxNumbersToDirectionsWithInt removeSchedule
    let
        followAndRemoveHyps :: [(BoxNumber, Int)] -> BoxZipper Expr -> Maybe (BoxZipper Expr)
        followAndRemoveHyps [] boxZipper = Just boxZipper
        followAndRemoveHyps ((boxNumber, hypInd):rest) boxZipper = do
            (Box hyps targs, crumbs) <- toBoxNumberFromZipper boxNumber boxZipper
            newHyps <- removeFromListMaybe hyps hypInd
            followAndRemoveHyps rest (Box newHyps targs, crumbs)
    finalZipper <- followAndRemoveHyps orderedRemoveSchedule (rootBox, [])
    Just $ (Tableau qZone (unzipBox finalZipper))

removePureTargs :: [(BoxNumber, Int)] -> Tableau -> Maybe Tableau
removePureTargs removeSchedule tab@(Tableau qZone rootBox) = do
    (orderedRemoveSchedule, _) <- boxNumbersToDirectionsWithInt removeSchedule
    let
        followAndRemoveTargs :: [(BoxNumber, Int)] -> BoxZipper Expr -> Maybe (BoxZipper Expr)
        followAndRemoveTargs [] boxZipper = Just boxZipper
        followAndRemoveTargs ((boxNumber, targInd):rest) boxZipper = do
            (Box hyps targs, crumbs) <- toBoxNumberFromZipper boxNumber boxZipper
            PureTarg targ <- getFromListMaybe targs targInd
            newTargs <- removeFromListMaybe targs targInd
            followAndRemoveTargs rest (Box hyps newTargs, crumbs)
    finalZipper <- followAndRemoveTargs orderedRemoveSchedule (rootBox, [])
    Just $ (Tableau qZone (unzipBox finalZipper))

removeBoxTargs :: [(BoxNumber, Int)] -> Tableau -> Maybe Tableau
removeBoxTargs removeSchedule tab@(Tableau qZone rootBox) = do
    (orderedRemoveSchedule, _) <- boxNumbersToDirectionsWithInt removeSchedule
    let
        followAndRemoveTargs :: [(BoxNumber, Int)] -> BoxZipper Expr -> Maybe (BoxZipper Expr)
        followAndRemoveTargs [] boxZipper = Just boxZipper
        followAndRemoveTargs ((boxNumber, targInd):rest) boxZipper = do
            (Box hyps targs, crumbs) <- toBoxNumberFromZipper boxNumber boxZipper
            BoxTarg targ <- getFromListMaybe targs targInd
            newTargs <- removeFromListMaybe targs targInd
            followAndRemoveTargs rest (Box hyps newTargs, crumbs)
    finalZipper <- followAndRemoveTargs orderedRemoveSchedule (rootBox, [])
    Just $ (Tableau qZone (unzipBox finalZipper))


-- | Updates the specified hypothesis.
updateHyp :: (BoxNumber, Int) -> Expr -> Tableau -> Maybe Tableau
updateHyp (boxNumber, hypInd) newHyp (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    newBoxZipper <- updateHypInZipper hypInd newHyp boxZipper
    let newBox = unzipBox newBoxZipper
    Just (Tableau qZone newBox)

updatePureTarg :: (BoxNumber, Int) -> Expr -> Tableau -> Maybe Tableau
updatePureTarg (boxNumber, targInd) newTarg (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    newBoxZipper <- updatePureTargInZipper targInd newTarg boxZipper
    let newBox = unzipBox newBoxZipper
    Just (Tableau qZone newBox)

updateBoxTarg :: (BoxNumber, Int) -> Box Expr -> Tableau -> Maybe Tableau
updateBoxTarg (boxNumber, targInd) newTarg (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    newBoxZipper <- updateBoxTargInZipper targInd newTarg boxZipper
    let newBox = unzipBox newBoxZipper
    Just (Tableau qZone newBox)

-- | Helper function to get the i-th element from a list if it exists
-- and return Nothing if not.
getFromListMaybe :: [a] -> Int -> Maybe a
getFromListMaybe l i
    | i < 0 || i >= length l = Nothing
    | otherwise = Just $ l!!i

-- | Gets the specified Hyp
getHyp :: (BoxNumber, Int) -> Tableau -> Maybe Expr
getHyp (boxNumber, hypInd) (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    getHypInZipper hypInd boxZipper

getPureTarg :: (BoxNumber, Int) -> Tableau -> Maybe Expr
getPureTarg (boxNumber, targInd) (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    getPureTargInZipper targInd boxZipper

getBoxTarg :: (BoxNumber, Int) -> Tableau -> Maybe (Box Expr)
getBoxTarg (boxNumber, targInd) (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    getBoxTargInZipper targInd boxZipper

-- | Efficiently gets the specified list of hyps. Data is stored with each hyp,
-- and this is preserved. Also returns the deepest BoxNumber from the boxes
getHypsWithData :: [((BoxNumber, Int), a)] -> Tableau -> Maybe ([(Expr, a)], BoxNumber)
getHypsWithData getSchedule tab@(Tableau qZone rootBox) = do
    let boxNumbersWithData = map (\((boxNumber, hypInd), dat) -> (boxNumber, (hypInd, dat))) getSchedule
    (directions, deepestBox) <- boxNumbersToDirections boxNumbersWithData
    let
        followAndGetHyps :: [(BoxNumber, (Int, a))] -> BoxZipper Expr -> Maybe [(Expr, a)]
        followAndGetHyps [] _ = Just []
        followAndGetHyps ((boxNumber, (hypInd, dat)):rest) boxZipper = do
            newBoxZipper <- toBoxNumberFromZipper boxNumber boxZipper
            hyp <- getHypInZipper hypInd newBoxZipper
            otherHyps <- followAndGetHyps rest newBoxZipper
            Just ((hyp, dat):otherHyps)
    extractedHyps <- followAndGetHyps boxNumbersWithData (rootBox, [])
    Just (extractedHyps, deepestBox)

-- | As above, but for targs and returns the shallowest (not deepest) BoxNumber.
getTargsWithData :: [((BoxNumber, Int), a)] -> Tableau -> Maybe ([(Expr, a)], BoxNumber)
getTargsWithData getSchedule tab@(Tableau qZone rootBox) = do
    let boxNumbersWithData = map (\((boxNumber, targInd), dat) -> (boxNumber, (targInd, dat))) getSchedule
    (directions, shallowestBox) <- boxNumbersToDirectionsFlipped boxNumbersWithData
    let
        followAndGetTargs :: [(BoxNumber, (Int, a))] -> BoxZipper Expr -> Maybe [(Expr, a)]
        followAndGetTargs [] _ = Just []
        followAndGetTargs ((boxNumber, (targInd, dat)):rest) boxZipper = do
            newBoxZipper <- toBoxNumberFromZipper boxNumber boxZipper
            targ <- getPureTargInZipper targInd newBoxZipper
            otherTargs <- followAndGetTargs rest newBoxZipper
            Just ((targ, dat):otherTargs)
    extractedTargs <- followAndGetTargs boxNumbersWithData (rootBox, [])
    Just (extractedTargs, shallowestBox)

-- | Checks if the list of expressions provided exist as hypothess in the tableau
-- in such a way that they can be used together. If not, returns Nothing.
-- If so, returns the deepest BoxNumber's in which the hypotheses lies
-- (there could be many, depending on the route taken)
checkHypsExistCompatibly :: [Expr] -> Tableau -> [BoxNumber]
checkHypsExistCompatibly hypsToFind tab@(Tableau qZone rootBox@(Box rootHyps rootTargs)) = let
    exploreBranch :: ((BoxNumber, BoxZipper Expr), [Expr]) -> [((BoxNumber, BoxZipper Expr), [Expr])]
    exploreBranch ((boxNumber, boxZipper@(Box hyps targs, crumbs)), hypsToFind') = let
        newBranches = mapMaybe (\targInd -> case toBoxNumberFromZipper [targInd] boxZipper of
            Just newBoxZipper -> Just (boxNumber++[targInd], newBoxZipper)
            Nothing -> Nothing
            ) [0..length targs-1]
        in map (\a@(_, (Box hyps targs, _)) -> (a, filter (`notElem` hyps) hypsToFind')) newBranches
    
    exploreBranches :: ((BoxNumber, BoxZipper Expr), [Expr]) -> [BoxNumber]
    exploreBranches ((boxNumber, _), []) = [boxNumber]
    exploreBranches a@((boxNumber, boxZipper), _) = concatMap (exploreBranches) (exploreBranch a)

    remainingHyps = filter (`notElem` rootHyps) hypsToFind
    rootZipper = (rootBox, [])

    in exploreBranches (([], rootZipper), remainingHyps)

-- Given a list of targets, we want to find a subset of those targets s.t. none of the
-- targs in the given list lie below them in the tree. This returns a list of subsets
-- satisfying this constraint.
getDeepestTargFromList :: [Expr] -> Tableau -> [([(Expr, Int)], BoxNumber)]
getDeepestTargFromList targsToFind tab@(Tableau qZone rootBox@(Box rootHyps rootTargs)) = let
    getDeepestTargZipper :: [Expr] -> BoxNumber -> BoxZipper Expr -> [([(Expr, Int)], BoxNumber)]
    getDeepestTargZipper targsToFind boxNumber boxZipper@(Box hyps targs, _) = let
        targsAtThisLevel = mapMaybe (\targInd -> case targs!!targInd of
            BoxTarg _ -> Nothing
            PureTarg targ -> if targ `elem` targsToFind then Just (targ, targInd)
                else Nothing)
            [0..length targs-1]
        deeperTargs = filter (not . null) $ map (\targInd -> case toBoxNumberFromZipper [targInd] boxZipper of
            Nothing -> []
            Just newZipper ->
                getDeepestTargZipper targsToFind (boxNumber++[targInd]) newZipper)
            [0..length targs-1]
        in if null deeperTargs then [(targsAtThisLevel, boxNumber)]
        else concat deeperTargs
    
    in getDeepestTargZipper targsToFind [] (rootBox, [])

