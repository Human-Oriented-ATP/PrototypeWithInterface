{-
  A lot of the functions here have type (MonadPlus m) => ... -> m (Something)
  Originally the types where just ... -> Maybe Something
  The new types are more general, making the functions more versatile
  If you want you can just think of m being Maybe when you read the code
  (Maybe is an instance of the MonadPlus type class)
  The reason for this change is so the functions can be used in the
  Mathematician monad, which is also an instance of MonadPlus.
-}

module Robot.BasicMoveHelpers where

import Robot.Lib
import Robot.Poset
import Robot.TableauFoundation

import Data.Maybe
import Control.Monad

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
getNewExternalNamePeel :: (MonadPlus m) => Maybe ExternalName -> QZone -> m ExternalName
getNewExternalNamePeel exNm (Poset set rel) = case exNm of
    Just nm -> if nm `elem` (mapMaybe qVarGetExternalName set) then
            return $ findFreshExNm (mapMaybe qVarGetExternalName set)
        else return nm
    _ -> return $ findFreshExNm (mapMaybe qVarGetExternalName set)


-- | Adds a hypothesis to a specified Box. Because this is just a helper
-- function in writing moves, not a move itself, I don't use the "Move"
-- type synonym here.
addHyp :: (MonadPlus m) => BoxNumber -> Expr -> Tableau -> m Tableau
addHyp boxNumber hyp (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    let newZipper = addHypToZipper hyp boxZipper
    return $ Tableau qZone (unzipBox newZipper)

addPureTarg :: (MonadPlus m) => BoxNumber -> Expr -> Tableau -> m Tableau
addPureTarg boxNumber targ (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    let newZipper = addPureTargToZipper targ boxZipper
    return $ Tableau qZone (unzipBox newZipper)

addBoxTarg :: (MonadPlus m) => BoxNumber -> Box Expr -> Tableau -> m Tableau
addBoxTarg boxNumber boxTarg (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    let newZipper = addBoxTargToZipper boxTarg boxZipper
    return $ Tableau qZone (unzipBox newZipper)

-- | Repeats addHyp on many arguments in an efficient way
addHyps :: (MonadPlus m) => [(BoxNumber, Expr)] -> Tableau -> m Tableau
addHyps addSchedule (Tableau qZone rootBox) = do
    (boxRoute, _) <- boxNumbersToDirections addSchedule
    
    let zippedBox = (rootBox, [])
        followAndAddHyps :: (MonadPlus m) => [(BoxNumber, Expr)] -> BoxZipper Expr ->
            m (BoxZipper Expr)
        followAndAddHyps [] currentZipper = return currentZipper
        followAndAddHyps ((direction, hyp):rest) currentZipper = do
            newZipper <- toBoxNumberFromZipper direction currentZipper
            return $ addHypToZipper hyp newZipper
    
    addedHypsZipper <- followAndAddHyps boxRoute zippedBox
    let newRootBox = unzipBox addedHypsZipper
    return $ Tableau qZone newRootBox


addPureTargs :: (MonadPlus m) => [(BoxNumber, Expr)] -> Tableau -> m Tableau
addPureTargs addSchedule (Tableau qZone rootBox) = do
    (boxRoute, _) <- boxNumbersToDirections addSchedule
    
    let zippedBox = (rootBox, [])
        followAndAddPureTargs :: (MonadPlus m) => [(BoxNumber, Expr)] ->
            BoxZipper Expr -> m (BoxZipper Expr)
        followAndAddPureTargs [] currentZipper = return currentZipper
        followAndAddPureTargs ((direction, pureTarg):rest) currentZipper = do
            newZipper <- toBoxNumberFromZipper direction currentZipper
            return $ addPureTargToZipper pureTarg newZipper
    
    addTargsZipper <- followAndAddPureTargs boxRoute zippedBox
    let newRootBox = unzipBox addTargsZipper
    return $ Tableau qZone newRootBox

addBoxTargs :: (MonadPlus m) => [(BoxNumber, Box Expr)] -> Tableau -> m Tableau
addBoxTargs addSchedule (Tableau qZone rootBox) = do
    (boxRoute, _) <- boxNumbersToDirections addSchedule
    
    let zippedBox = (rootBox, [])
        followAndAddBoxTargs :: (MonadPlus m) => [(BoxNumber, Box Expr)] ->
            BoxZipper Expr -> m (BoxZipper Expr)
        followAndAddBoxTargs [] currentZipper = return currentZipper
        followAndAddBoxTargs ((direction, boxTarg):rest) currentZipper = do
            newZipper <- toBoxNumberFromZipper direction currentZipper
            return $ addBoxTargToZipper boxTarg newZipper
    
    addTargsZipper <- followAndAddBoxTargs boxRoute zippedBox
    let newRootBox = unzipBox addTargsZipper
    return $ Tableau qZone newRootBox



-- | Remove a hypothesis, specified by a BoxNumber and the hyp's index within that box
-- Maybe because the specified hyp may not exist.
removeHyp :: (MonadPlus m) => (BoxNumber, Int) -> Tableau -> m Tableau
removeHyp (boxNumber, hypInd) (Tableau qZone boxes) = do
    boxZipper <- toBoxNumberFromRoot boxNumber boxes
    newBoxZipper <- removeHypFromZipper hypInd boxZipper
    return (Tableau qZone (unzipBox newBoxZipper))

removeTarg :: (MonadPlus m) => (BoxNumber, Int) -> Tableau -> m Tableau
removeTarg (boxNumber, targInd) (Tableau qZone boxes) = do
    boxZipper <- toBoxNumberFromRoot boxNumber boxes
    newBoxZipper <- removeTargFromZipper targInd boxZipper
    return (Tableau qZone (unzipBox newBoxZipper))

removeAllTargs :: (MonadPlus m) => BoxNumber -> Tableau -> m Tableau
removeAllTargs boxNumber (Tableau qZone boxes) = do
    (Box hyps targs, crumbs) <- toBoxNumberFromRoot boxNumber boxes
    return (Tableau qZone (unzipBox (Box hyps [], crumbs)))

-- | Helper function to remove the i-th element from a list if it exists
-- and otherwise return Nothing
removeFromListMaybe :: (MonadPlus m) => [a] -> Int -> m [a]
removeFromListMaybe l i
    | i < 0 || i >= length l = mzero
    | otherwise = let
        (as, _:bs) = splitAt i l
        in return $ as++bs

-- | Repeats removeHyp on many arguments in an efficient way
removeHyps :: (MonadPlus m) => [(BoxNumber, Int)] -> Tableau -> m Tableau
removeHyps removeSchedule tab@(Tableau qZone rootBox) = do
    (orderedRemoveSchedule, _) <- boxNumbersToDirectionsWithInt removeSchedule
    let
        followAndRemoveHyps :: (MonadPlus m) => [(BoxNumber, Int)] ->
            BoxZipper Expr -> m (BoxZipper Expr)
        followAndRemoveHyps [] boxZipper = return boxZipper
        followAndRemoveHyps ((boxNumber, hypInd):rest) boxZipper = do
            (Box hyps targs, crumbs) <- toBoxNumberFromZipper boxNumber boxZipper
            newHyps <- removeFromListMaybe hyps hypInd
            followAndRemoveHyps rest (Box newHyps targs, crumbs)
    finalZipper <- followAndRemoveHyps orderedRemoveSchedule (rootBox, [])
    return $ (Tableau qZone (unzipBox finalZipper))

removePureTargs :: (MonadPlus m) => [(BoxNumber, Int)] -> Tableau -> m Tableau
removePureTargs removeSchedule tab@(Tableau qZone rootBox) = do
    (orderedRemoveSchedule, _) <- boxNumbersToDirectionsWithInt removeSchedule
    let
        followAndRemoveTargs :: (MonadPlus m) => [(BoxNumber, Int)] ->
            BoxZipper Expr -> m (BoxZipper Expr)
        followAndRemoveTargs [] boxZipper = return boxZipper
        followAndRemoveTargs ((boxNumber, targInd):rest) boxZipper = do
            (Box hyps targs, crumbs) <- toBoxNumberFromZipper boxNumber boxZipper
            targ <- getFromListMaybe targs targInd
            case targ of
                PureTarg _ -> return ()
                _ -> mzero -- Fail if one of the targets is not a Pure target
            newTargs <- removeFromListMaybe targs targInd
            followAndRemoveTargs rest (Box hyps newTargs, crumbs)
    finalZipper <- followAndRemoveTargs orderedRemoveSchedule (rootBox, [])
    return $ (Tableau qZone (unzipBox finalZipper))

removeBoxTargs :: (MonadPlus m) => [(BoxNumber, Int)] -> Tableau -> m Tableau
removeBoxTargs removeSchedule tab@(Tableau qZone rootBox) = do
    (orderedRemoveSchedule, _) <- boxNumbersToDirectionsWithInt removeSchedule
    let
        followAndRemoveTargs :: (MonadPlus m) => [(BoxNumber, Int)] ->
            BoxZipper Expr -> m (BoxZipper Expr)
        followAndRemoveTargs [] boxZipper = return boxZipper
        followAndRemoveTargs ((boxNumber, targInd):rest) boxZipper = do
            (Box hyps targs, crumbs) <- toBoxNumberFromZipper boxNumber boxZipper
            targ <- getFromListMaybe targs targInd
            case targ of
                BoxTarg _ -> return ()
                _ -> mzero  -- Fail if one of the targets is not a Box target
            newTargs <- removeFromListMaybe targs targInd
            followAndRemoveTargs rest (Box hyps newTargs, crumbs)
    finalZipper <- followAndRemoveTargs orderedRemoveSchedule (rootBox, [])
    return $ (Tableau qZone (unzipBox finalZipper))


-- | Updates the specified hypothesis.
updateHyp :: (MonadPlus m) => (BoxNumber, Int) -> Expr -> Tableau -> m Tableau
updateHyp (boxNumber, hypInd) newHyp (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    newBoxZipper <- updateHypInZipper hypInd newHyp boxZipper
    let newBox = unzipBox newBoxZipper
    return (Tableau qZone newBox)

updatePureTarg :: (MonadPlus m) => (BoxNumber, Int) -> Expr -> Tableau -> m Tableau
updatePureTarg (boxNumber, targInd) newTarg (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    newBoxZipper <- updatePureTargInZipper targInd newTarg boxZipper
    let newBox = unzipBox newBoxZipper
    return (Tableau qZone newBox)

updateBoxTarg :: (MonadPlus m) => (BoxNumber, Int) -> Box Expr -> Tableau -> m Tableau
updateBoxTarg (boxNumber, targInd) newTarg (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    newBoxZipper <- updateBoxTargInZipper targInd newTarg boxZipper
    let newBox = unzipBox newBoxZipper
    return (Tableau qZone newBox)

-- | Helper function to get the i-th element from a list if it exists
-- and return Nothing if not.
getFromListMaybe :: (MonadPlus m) => [a] -> Int -> m a
getFromListMaybe l i
    | i < 0 || i >= length l = mzero
    | otherwise = return $ l!!i

-- | Gets the specified Hyp
getHyp :: (MonadPlus m) => (BoxNumber, Int) -> Tableau -> m Expr
getHyp (boxNumber, hypInd) (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    getHypInZipper hypInd boxZipper

getPureTarg :: (MonadPlus m) => (BoxNumber, Int) -> Tableau -> m Expr
getPureTarg (boxNumber, targInd) (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    getPureTargInZipper targInd boxZipper

getBoxTarg :: (MonadPlus m) => (BoxNumber, Int) -> Tableau -> m (Box Expr)
getBoxTarg (boxNumber, targInd) (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    getBoxTargInZipper targInd boxZipper

-- | Efficiently gets the specified list of hyps. Data is stored with each hyp,
-- and this is preserved. Also returns the deepest BoxNumber from the boxes
getHypsWithData :: (MonadPlus m) => [((BoxNumber, Int), a)] -> Tableau ->
    m ([(Expr, a)], BoxNumber)
getHypsWithData getSchedule tab@(Tableau qZone rootBox) = do
    let boxNumbersWithData = map (\((boxNumber, hypInd), dat) -> (boxNumber, (hypInd, dat))) getSchedule
    (directions, deepestBox) <- boxNumbersToDirections boxNumbersWithData
    let
        followAndGetHyps :: (MonadPlus m) => [(BoxNumber, (Int, a))] ->
            BoxZipper Expr -> m [(Expr, a)]
        followAndGetHyps [] _ = return []
        followAndGetHyps ((boxNumber, (hypInd, dat)):rest) boxZipper = do
            newBoxZipper <- toBoxNumberFromZipper boxNumber boxZipper
            hyp <- getHypInZipper hypInd newBoxZipper
            otherHyps <- followAndGetHyps rest newBoxZipper
            return ((hyp, dat):otherHyps)
    extractedHyps <- followAndGetHyps boxNumbersWithData (rootBox, [])
    return (extractedHyps, deepestBox)

-- | As above, but for targs and returns the shallowest (not deepest) BoxNumber.
getTargsWithData :: (MonadPlus m) => [((BoxNumber, Int), a)] -> Tableau ->
    m ([(Expr, a)], BoxNumber)
getTargsWithData getSchedule tab@(Tableau qZone rootBox) = do
    let boxNumbersWithData = map (\((boxNumber, targInd), dat) -> (boxNumber, (targInd, dat))) getSchedule
    (directions, shallowestBox) <- boxNumbersToDirectionsFlipped boxNumbersWithData
    let
        followAndGetTargs :: (MonadPlus m) => [(BoxNumber, (Int, a))] ->
            BoxZipper Expr -> m [(Expr, a)]
        followAndGetTargs [] _ = return []
        followAndGetTargs ((boxNumber, (targInd, dat)):rest) boxZipper = do
            newBoxZipper <- toBoxNumberFromZipper boxNumber boxZipper
            targ <- getPureTargInZipper targInd newBoxZipper
            otherTargs <- followAndGetTargs rest newBoxZipper
            return ((targ, dat):otherTargs)
    extractedTargs <- followAndGetTargs boxNumbersWithData (rootBox, [])
    return (extractedTargs, shallowestBox)

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

