{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use zipWith" #-}
module Robot.LibraryMoves where

import Robot.Lib
import Robot.TableauFoundation
import Robot.BasicMoveHelpers
import Robot.HoleExpr
import Robot.NewBinderIdentifiers

import Data.Maybe
import Data.List ( foldl', sortBy, nub )
import Control.Monad


-- | A list of conditions under which the equivalences hold
-- and a list of statements which are equivalent (equivalents).
data LibraryEquivalence = LibraryEquivalence QZone [HoleExpr] [HoleExpr]

-- | Basically just a Tableau without the boxes being nested.
-- A list of hypotheses and then a list of conclusions which hold under the hypotheses.
-- IMPROVEMENT - could we need a richer structure allowing for nesting?
data LibraryImplication = LibraryImplication QZone [HoleExpr] [HoleExpr]



-- <<< EQUIVALENCES >>>
-- To perform equivalences, we need to specify several things:
-- A) What equivalence we want to use (given by the name of the library equiv)
-- B) Which two expressions we are trading between in the equivalence (given by
--      a pair (Int, Int))
-- C) What expression (hyp/targ) we want to use it on (given by a BoxNumber and an Int)
-- D) What substitution we believe makes the analogy between the library equivalence
--      and our problem state (given by the Substitution type)
-- E) The mapping between the conditions under which the equivalence holds and the
--      hypotheses that we believe correspond to each condition (given by a list [(Int, (BoxNumber, Int))])

-- Because the last two are laboursome to specify, we'll write several functions,
-- some of which will allow us to specify only some or none of the last two inputs.


-- | Here we have to specify all information. The function verifies are suggestions
-- are in fact legitimate, otherwise returns Nothing.
libEquivTargFull :: LibraryEquivalence -> (Int, Int) -> [(Int, (BoxNumber, Int))] -> Substitution -> (BoxNumber, Int) -> Tableau -> Maybe Tableau
libEquivTargFull (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd) condMap substitution
    (targBoxNumber, targInd) tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents
        || any ((\i -> i < 0 || i >= length conditions) . fst) condMap = Nothing
    | otherwise = do
        targExpr <- getPureTarg (targBoxNumber, targInd) tab
        subedTarg <- holeExprToExpr $ applySubstitution substitution (equivalents !! originalEquivalentInd)
        guard $ subedTarg == targExpr
        (hypsWithConds, deepestBox) <- getHypsWithData (map (\(condInd, b) -> (b, conditions!!condInd)) condMap) tab
        guard $ isPrefix targBoxNumber deepestBox
        guard $ all (\(hyp, cond) -> Just hyp == holeExprToExpr (applySubstitution substitution cond)) hypsWithConds
        
        newTarg <- holeExprToExpr $ applySubstitution substitution (equivalents !! newEquivalentInd)
        updatePureTarg (targBoxNumber, targInd) newTarg tab

libEquivHypFull :: LibraryEquivalence -> (Int, Int) -> [(Int, (BoxNumber, Int))] -> Substitution -> (BoxNumber, Int) -> Tableau -> Maybe Tableau
libEquivHypFull (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd) condMap substitution
    (hypBoxNumber, hypInd) tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents
        || any ((\i -> i < 0 || i >= length conditions) . fst) condMap = Nothing
    | otherwise = do
        hypExpr <- getHyp (hypBoxNumber, hypInd) tab
        subedHyp <- holeExprToExpr $ applySubstitution substitution (equivalents !! originalEquivalentInd)
        guard $ subedHyp == hypExpr
        (hypsWithConds, deepestBox) <- getHypsWithData (map (\(condInd, b) -> (b, conditions!!condInd)) condMap) tab
        guard $ isPrefix hypBoxNumber deepestBox
        guard $ all (\(hyp, cond) -> Just hyp == holeExprToExpr (applySubstitution substitution cond)) hypsWithConds
        
        newHyp <- holeExprToExpr $ applySubstitution substitution (equivalents !! newEquivalentInd)
        updateHyp (hypBoxNumber, hypInd) newHyp tab


-- | Here we don't need to specify the substitution
libEquivTargCondMap :: LibraryEquivalence -> (Int, Int) -> [(Int, (BoxNumber, Int))] -> (BoxNumber, Int) -> Tableau -> Maybe Tableau
libEquivTargCondMap (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd) condMap (targBoxNumber, targInd) tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents
        || any ((\i -> i < 0 || i >= length conditions) . fst) condMap = Nothing
    | otherwise = do
        targExpr <- getPureTarg (targBoxNumber, targInd) tab
        let e = equivalents !! originalEquivalentInd
            e' = equivalents !! newEquivalentInd
        initialSub <- matchExpressions e targExpr
        let hypIndsWithConds = map (\(condInd, hypInd) -> (hypInd, conditions!!condInd)) condMap
        (hypsWithConds, deepestBox) <- getHypsWithData hypIndsWithConds tab
        guard $ isPrefix deepestBox targBoxNumber
        let subs = map (\(hyp, cond) -> matchExpressions cond hyp) hypsWithConds

        guard $ all isJust subs
        let -- Attempt to merge substitutions
            foldFunction :: Maybe Substitution -> Maybe Substitution -> Maybe Substitution
            foldFunction subA subB = do
                a <- subA
                b <- subB
                mergeSubstitutions a b
            finalSubMaybe = foldl' foldFunction (Just initialSub) subs
        finalSub <- finalSubMaybe
        newTarg <- holeExprToExpr $ applySubstitution finalSub e'
        updatePureTarg (targBoxNumber, targInd) newTarg tab

libEquivHypCondMap :: LibraryEquivalence -> (Int, Int) -> [(Int, (BoxNumber, Int))] -> (BoxNumber, Int) -> Tableau -> Maybe Tableau
libEquivHypCondMap (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd) condMap (hypBoxNumber, hypInd) tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents
        || any ((\i -> i < 0 || i >= length conditions) . fst) condMap = Nothing
    | otherwise = do
        hypExpr <- getHyp (hypBoxNumber, hypInd) tab
        let e = equivalents !! originalEquivalentInd
            e' = equivalents !! newEquivalentInd
        initialSub <- matchExpressions e hypExpr
        let hypIndsWithConds = map (\(condInd, hypInd) -> (hypInd, conditions!!condInd)) condMap
        (hypsWithConds, deepestBox) <- getHypsWithData hypIndsWithConds tab
        guard $ isPrefix deepestBox hypBoxNumber
        let subs = map (\(hyp, cond) -> matchExpressions cond hyp) hypsWithConds

        guard $ all isJust subs
        let -- Attempt to merge substitutions
            foldFunction :: Maybe Substitution -> Maybe Substitution -> Maybe Substitution
            foldFunction subA subB = do
                a <- subA
                b <- subB
                mergeSubstitutions a b
            finalSubMaybe = foldl' foldFunction (Just initialSub) subs
        finalSub <- finalSubMaybe
        newHyp <- holeExprToExpr $ applySubstitution finalSub e'
        updateHyp (hypBoxNumber, hypInd) newHyp tab


-- | Here we don't have to specify the mapping from conditions to hypotheses
libEquivTargSub :: LibraryEquivalence -> (Int, Int) -> Substitution -> (BoxNumber, Int) -> Tableau -> Maybe Tableau
libEquivTargSub (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd) substitution
    (targBoxNumber, targInd) tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents = Nothing
    | otherwise = do
        targExpr <- getPureTarg (targBoxNumber, targInd) tab
        subedTarg <- holeExprToExpr $ applySubstitution substitution (equivalents !! originalEquivalentInd)
        guard $ subedTarg == targExpr

        let maybeSubedConditions = map (holeExprToExpr . applySubstitution substitution) conditions
        guard $ all isJust maybeSubedConditions
        let subedConditions = catMaybes maybeSubedConditions

        let deepestBoxes = checkHypsExistCompatibly subedConditions tab
        guard $ any (isPrefix targBoxNumber) deepestBoxes

        newTarg <- holeExprToExpr $ applySubstitution substitution (equivalents !! newEquivalentInd)
        updatePureTarg (targBoxNumber, targInd) newTarg tab


libEquivHypSub :: LibraryEquivalence -> (Int, Int) -> Substitution -> (BoxNumber, Int) -> Tableau -> Maybe Tableau
libEquivHypSub (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd) substitution
    (hypBoxNumber, hypInd) tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents = Nothing
    | otherwise = do
        hypExpr <- getHyp (hypBoxNumber, hypInd) tab
        subedHyp <- holeExprToExpr $ applySubstitution substitution (equivalents !! originalEquivalentInd)
        guard $ subedHyp == hypExpr

        let maybeSubedConditions = map (holeExprToExpr . applySubstitution substitution) conditions
        guard $ all isJust maybeSubedConditions
        let subedConditions = catMaybes maybeSubedConditions

        let deepestBoxes = checkHypsExistCompatibly subedConditions tab
        guard $ any (isPrefix hypBoxNumber) deepestBoxes

        newHyp <- holeExprToExpr $ applySubstitution substitution (equivalents !! newEquivalentInd)
        updateHyp (hypBoxNumber, hypInd) newHyp tab

-- | Here we don't have to specify a mapping OR a substitution
libEquivTarg :: LibraryEquivalence -> (Int, Int) -> (BoxNumber, Int) -> Tableau -> Maybe Tableau
libEquivTarg (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd)
    (targBoxNumber, targInd) tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents = Nothing
    | otherwise = do
        let e = equivalents !! originalEquivalentInd
        let e' = equivalents !! newEquivalentInd
        targExpr <- getPureTarg (targBoxNumber, targInd) tab
        initialSub <- matchExpressions e targExpr -- Match the suggested equivalence with the suggested target
        -- Now we need to ensure all conditions in the result can match to a hypothesis consistently
        hyps <- getHypsUsableInBoxNumber targBoxNumber rootBox
        let condSubs = map fst $ findConsistentSubs (zip [0..] conditions) (zip [0..] hyps)

        -- IMPROVEMENT - Currently gives multiple, but actually isn't the substitution forced by the target? Not sure, for now will just take the head if it exists
        let possibleSubs = mapMaybe (mergeSubstitutions initialSub) condSubs
        guard $ (not . null) possibleSubs

        let (sub:_) = possibleSubs
        newTarg <- holeExprToExpr $ applySubstitution sub e'
        updatePureTarg (targBoxNumber, targInd) newTarg tab

-- | Similarly here. It's worth noting that conditions may appear below the hyp
-- we're trying to apply an equivalence to, in which case we'll simply add the
-- equivalent hypothesis to the deepest box required.
libEquivHyp :: LibraryEquivalence -> (Int, Int) -> (BoxNumber, Int) -> Tableau -> Maybe Tableau
libEquivHyp (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd)
    (hypBoxNumber, hypInd) tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents = Nothing
    | otherwise = do
        let e = equivalents !! originalEquivalentInd
            e' = equivalents !! newEquivalentInd
        hypExpr <- getHyp (hypBoxNumber, hypInd) tab
        initialSub <- matchExpressions e hypExpr
        
        let possibleSubs = filter
                (\(_, boxNumber) ->isPrefix boxNumber hypBoxNumber || isPrefix hypBoxNumber boxNumber)
                (exploreTree initialSub conditions [] (rootBox, []))
        guard $ not $ null possibleSubs
        let ((finalSub, deepestBox):_) = sortBy (\(_, a) (_, b) -> length a `compare` length b) possibleSubs
        newHyp <- holeExprToExpr $ applySubstitution finalSub e'
        
        if isPrefix deepestBox hypBoxNumber then
            updateHyp (hypBoxNumber, hypInd) newHyp tab
        else
            addHyp deepestBox newHyp tab

-- Helper function in the minimal-info version of equivalence moves. This seeks
-- a list of substitutions and mappings that would equate the list of conditions
-- and hypotheses provided.
findConsistentSubs :: [(Int, HoleExpr)] -> [(Int, Expr)] -> [(Substitution, [(Int, Int)])]
findConsistentSubs [] _ = [([], [])]
findConsistentSubs conds@((condIndex, h1):remainingConds) labelledHypExprs
    | length conds > length labelledHypExprs = []
    | otherwise =
        let possibleH1Subs = mapMaybe (\(i, e) -> case (i, matchExpressions h1 e) of
                (n, Just sub) -> Just (n, sub)
                (n, Nothing) -> Nothing) labelledHypExprs

            -- Takes a substitution, and the hypothesis-index which has been matched
            -- along with the old conditions and old hypotheses, then generates a new set of
            -- conditions and hypotheses formed by removing the hypothesis/condition and substiuting as appropriate
            generateNewProblem :: [(Int, HoleExpr)] -> [(Int, Expr)] -> (Int, Substitution) -> ([(Int, HoleExpr)], [(Int, Expr)])
            generateNewProblem [] _ _ = ([], []) -- This pattern should never be matched because the empty condition case is dealt with
            -- There should never be more conditions than hypotheses because this is guarded out initially
            generateNewProblem (_:newCondsPreSub) oldLabelledHyps (ij, sj) =
                -- Do all the substitutions and get rid of first condition and relevant, ij-th, hyp
                let newLabelledHyps = filter (\(n, exp) -> n /= ij) oldLabelledHyps
                    newConds = map (\(n, exp) -> (n, applySubstitution sj exp)) newCondsPreSub
                in (newConds, newLabelledHyps)

            -- These are the remaining problems to solve. We store them as pairs, the first part reprsenting the substitution done (given by a substitution and the hypothesis-index matched)
            -- The second part reprsenting the remaining problem after applying that substitution.
            remainingProblems = map (\s -> (s, generateNewProblem conds labelledHypExprs s)) possibleH1Subs

            -- This takes a remaining problem, recursively finds the solution, and combines it with the initial substitution to give us the final result
            findFutureCombinedSolutions :: ((Int, Substitution), ([(Int, HoleExpr)], [(Int, Expr)])) -> [(Substitution, [(Int, Int)])]
            findFutureCombinedSolutions newProblem =
                let ((i1, s1), (newConds, newLabelledHyps)) = newProblem
                    futureSolutions = findConsistentSubs newConds newLabelledHyps
                    combinedFutureSolutions = mapMaybe (\(s, mapping) -> case mergeSubstitutions s1 s of
                        Just sub -> Just (sub, (condIndex, i1):mapping)
                        _ -> Nothing) futureSolutions
                in combinedFutureSolutions

        -- The final result can be obtained from any of the remainingProblems we generated, thus we need to concatMap.
        in concatMap findFutureCombinedSolutions remainingProblems




-- <<< FORWARD REASONING >>>
-- Much like equivalences, there is a lot of information that needs to be specified
-- with forward reasoning. This time, we don't need to specify an expression we'd
-- like to use it on, or which "equivalents" we want to trade between. However,
-- we still need to specify a condition map and substitution. Thus, we will write
-- the same portfolio of functions allowing us to specify less.

-- | All information required.
libForwardReasoningFull:: LibraryImplication -> [(Int, (BoxNumber, Int))] -> Substitution -> Tableau -> Maybe Tableau
libForwardReasoningFull (LibraryImplication libQZone conditions consequents)
    condMap substitution tab@(Tableau qZone rootBox)
    | any ((\i -> i < 0 || i >= length conditions) . fst) condMap = Nothing
    | otherwise = do
        let hypIndsWithConds = map (\(condInd, (hypBoxNumber, hypInd)) -> ((hypBoxNumber, hypInd), conditions!!condInd)) condMap
        (hypsWithConds, deepestBoxNumber) <- getHypsWithData hypIndsWithConds tab
        guard $ all (\(hyp, cond) -> holeExprToExpr (applySubstitution substitution cond) == Just hyp) hypsWithConds

        let subedConsequents = mapMaybe (holeExprToExpr . applySubstitution substitution) consequents
        addHyps (zip (repeat deepestBoxNumber) subedConsequents) tab

-- | Only condition map required.
libForwardReasoningCondMap :: LibraryImplication -> [(Int, (BoxNumber, Int))] -> Tableau -> Maybe Tableau
libForwardReasoningCondMap (LibraryImplication libQZone conditions consequents)
    condMap tab@(Tableau qZone rootBox)
    | any ((\i -> i < 0 || i >= length conditions) . fst) condMap = Nothing
    | otherwise = do
        let hypIndsWithConds = map (\(condInd, (hypBoxNumber, hypInd)) -> ((hypBoxNumber, hypInd), conditions!!condInd)) condMap
        (hypsWithConds, deepestBoxNumber) <- getHypsWithData hypIndsWithConds tab
        let subs = map (\(hyp, cond) -> matchExpressions cond hyp) hypsWithConds
        guard $ all isJust subs
        let -- Attempt to merge substitutions
            foldFunction :: Maybe Substitution -> Maybe Substitution -> Maybe Substitution
            foldFunction subA subB = do
                a <- subA
                b <- subB
                mergeSubstitutions a b
            finalSubMaybe = foldl' foldFunction (Just []) subs
        finalSub <- finalSubMaybe

        let subedConsequents = mapMaybe (holeExprToExpr . applySubstitution finalSub) consequents
        addHyps (zip (repeat deepestBoxNumber) subedConsequents) tab

-- | Only substitution required.
libForwardReasoningSub :: LibraryImplication -> Substitution -> Tableau -> Maybe Tableau
libForwardReasoningSub (LibraryImplication libQZone conditions consequents)
    substitution tab@(Tableau qZone rootBox) = do
        let subedMaybeConditions = map (holeExprToExpr . applySubstitution substitution) conditions
        guard $ all isJust subedMaybeConditions

        let subedConditions = catMaybes subedMaybeConditions
        let deepestBoxNumbers = checkHypsExistCompatibly subedConditions tab
        guard $ not $ null deepestBoxNumbers
        let (deepestBoxNumber:_) = sortBy (\a b -> length a `compare` length b) deepestBoxNumbers

        let subedConsequents = mapMaybe (holeExprToExpr . applySubstitution substitution) consequents
        addHyps (zip (repeat deepestBoxNumber) subedConsequents) tab

-- | Neither substitution or condition map required.
libForwardReasoning :: LibraryImplication -> Tableau -> Maybe Tableau
libForwardReasoning (LibraryImplication libQZone conditions consequents) tab@(Tableau qZone rootBox) = do
    let possibleSolutions = exploreTree [] conditions [] (rootBox, [])
    guard $ not $ null possibleSolutions
    let ((finalSub, deepestBoxNumber):_) = sortBy (\a b -> snd a `compare` snd b) possibleSolutions
        subedConsequents = mapMaybe (holeExprToExpr . applySubstitution finalSub) consequents
    addHyps (zip (repeat deepestBoxNumber) subedConsequents) tab

-- | Finds all the possible substitutions one can make in matching the given list of 
-- conditions with the given list of expressions. This includes, for instance, the
-- trivial substitution which doesn't attempt to match any non-equal terms. The 
-- reason we include this is that we might want to "save" terms to be matched further
-- down the tree, so forcing potential matches immediately isn't necessarily right.
findAllPossibleSubs :: Substitution -> [HoleExpr] -> [Expr] -> [(Substitution, ([HoleExpr], [Expr]))]
findAllPossibleSubs startSub condsToMatch hyps = let
    trivialSub = (startSub, (condsToMatch, hyps))
    allCombinations = catMaybes [case matchExpressions cond hyp of
        Just sub -> Just (sub, (filter (/=cond) condsToMatch, filter (/=hyp) hyps))
        Nothing -> Nothing
        | cond <- condsToMatch, hyp <- hyps]
    filteredCombinations = mapMaybe (\(s, b) -> case mergeSubstitutions s startSub of
        Just newSub -> Just (newSub, b)
        Nothing -> Nothing) allCombinations
    finalCombinations = map
        (\(sub, (holeExprs, exprs)) -> (sub, (map (applySubstitution sub) holeExprs, exprs)))
        filteredCombinations
    futurePossibilities = concatMap (\(s, (a, b)) -> findAllPossibleSubs s a b) finalCombinations
    in nub $ trivialSub:futurePossibilities

-- Given a substitution we have decided to use thus far and a list of conditions to
-- match, finds all the possible substitutions which match all the conditions with
-- all the hypotheses in a consistent way. As usual, we also return the deepest
-- box number for each substitution.
exploreTree :: Substitution -> [HoleExpr] -> BoxNumber -> BoxZipper Expr -> [(Substitution, BoxNumber)]
exploreTree currentSub [] currentBoxNumber _ = [(currentSub, currentBoxNumber)]
exploreTree currentSub condsToMatch currentBoxNumber boxZipper@(Box hyps targs, _) = do
    (newSub, (newConds, _)) <- findAllPossibleSubs currentSub condsToMatch hyps
    if null newConds then [(newSub, currentBoxNumber)]
    else do
        (BoxTarg boxTarg, targInd) <- zip targs [0..]
        let newBoxNumber = currentBoxNumber++[targInd]
        case toBoxNumberFromZipper [targInd] boxZipper of
            Just newBoxZipper -> exploreTree newSub newConds newBoxNumber newBoxZipper
            Nothing -> []

-- <<< BACKWARD REASONING >>>
-- The situation with backward reasoning is more complex, because in backward reasoning
-- the entire point is that some conditions are NOT matched, and these unmatched conds
-- replace the target we want to prove. Furthermore, the library implication we use
-- may have many consequences, and some of these may be irrelevant problem. The result
-- is that we don't insist on matching all of the conditions OR consequents of the lib
-- implication. As a result, we need to specify:
-- A) The library implication we want to use
-- B) Which conditions and hypotheses we want to match
-- C) Which consequents and targets we want to match
-- D) What subsitution we believe draws the analogy between library impl and prob state

-- All of the last three are laboursome to specify, so we will write functions to avoid
-- these.


-- | Must specify all information.
libBackwardReasoningFull :: LibraryImplication -> [(Int, (BoxNumber, Int))] -> [(Int, (BoxNumber, Int))] -> Substitution -> Tableau -> Maybe Tableau
libBackwardReasoningFull (LibraryImplication libQZone conditions consequents)
    condMap targMap substitution tab@(Tableau qZone rootBox)
    | any ((\i -> i < 0 || i >= length conditions) . fst) condMap || any ((\i -> i < 0 || i >= length consequents) . fst) targMap = Nothing
    | otherwise = do
        (targsWithConsequents, targsShallowestBox) <- getTargsWithData (map (\(consInd, b) -> (b, consequents!!consInd)) targMap) tab
        (hypsWithConditions, hypsDeepestBox) <- getHypsWithData (map (\(condInd, b) -> (b, conditions!!condInd)) condMap) tab
        guard $ isPrefix hypsDeepestBox targsShallowestBox
        guard $ all (\(targ, cons) -> holeExprToExpr (applySubstitution substitution cons) == Just targ) targsWithConsequents
        guard $ all (\(hyp, cond) -> holeExprToExpr (applySubstitution substitution cond) == Just hyp) hypsWithConditions

        let missingSubedMaybeConds = [holeExprToExpr $ applySubstitution substitution (conditions!!condInd) | condInd <- [0..length conditions-1], condInd `notElem` map fst condMap]
        guard $ all isJust missingSubedMaybeConds

        let missingSubedConds = catMaybes missingSubedMaybeConds
        let targIndsToRemove = map snd targMap
        removePureTargs targIndsToRemove tab >>= addPureTargs (zip (repeat targsShallowestBox) missingSubedConds)

-- | Only need to specify the map between conds/hyps and consequents/targs
libBackwardReasoningCondMapTargMap :: LibraryImplication -> [(Int, (BoxNumber, Int))] -> [(Int, (BoxNumber, Int))] -> Tableau -> Maybe Tableau
libBackwardReasoningCondMapTargMap (LibraryImplication libQZone conditions consequents)
    condMap targMap tab@(Tableau qZone rootBox)
    | any ((\i -> i < 0 || i >= length conditions) . fst) condMap || any ((\i -> i < 0 || i >= length consequents) . fst) targMap = Nothing
    | otherwise = do
        (targsWithConsequents, targsShallowestBox) <- getTargsWithData (map (\(consInd, b) -> (b, consequents!!consInd)) targMap) tab
        (hypsWithConditions, hypsDeepestBox) <- getHypsWithData (map (\(condInd, b) -> (b, conditions!!condInd)) condMap) tab
        guard $ isPrefix hypsDeepestBox targsShallowestBox
        let subs = map (\(hyp, cond) -> matchExpressions cond hyp) hypsWithConditions ++ map (\(targ, cons) -> matchExpressions cons targ) targsWithConsequents

        let -- Attempt to merge substitutions
            foldFunction :: Maybe Substitution -> Maybe Substitution -> Maybe Substitution
            foldFunction subA subB = do
                a <- subA
                b <- subB
                mergeSubstitutions a b
            finalSubMaybe = foldl' foldFunction (Just []) subs
        finalSub <- finalSubMaybe
        
        let missingSubedMaybeConds = [holeExprToExpr $ applySubstitution finalSub (conditions!!condInd) | condInd <- [0..length conditions-1], condInd `notElem` map fst condMap]
        guard $ all isJust missingSubedMaybeConds
        let missingSubedConds = catMaybes missingSubedMaybeConds
        let targIndsToRemove = map snd targMap
        removePureTargs targIndsToRemove tab >>= addPureTargs (zip (repeat targsShallowestBox) missingSubedConds)


-- | Only need to specify the desired substitution. Will replace as many targets as
-- possible with as few conditions as possible
libBackwardReasoningSub :: LibraryImplication -> Substitution -> Tableau -> Maybe Tableau
libBackwardReasoningSub (LibraryImplication libQZone conditions consequents) substitution tab@(Tableau qZone rootBox) = do
    let subedMaybeConditions = map (holeExprToExpr . applySubstitution substitution) conditions
    guard $ all isJust subedMaybeConditions
    let subedConditions = catMaybes subedMaybeConditions

    let subedMaybeConsequents = map (holeExprToExpr . applySubstitution substitution) consequents
    guard $ all isJust subedMaybeConsequents
    let subedConsequents = catMaybes subedMaybeConsequents

    let targsToMatch = getDeepestTargFromList subedConsequents tab
    guard $ not $ null targsToMatch

    let hypMatches = mapMaybe (\(targsOnLevel, boxNumber) -> case getHypsUsableInBoxNumber boxNumber rootBox of
            Nothing -> Nothing
            Just hyps -> case filter (`elem` hyps) subedConditions of
                [] -> Nothing
                matchedConds -> Just (matchedConds, (targsOnLevel, boxNumber)))
            targsToMatch
    guard $ not $ null hypMatches
    let ((matchedConds, (matchedTargs, targBoxNumber)):_) = sortBy
            (\a b -> (length $ fst b) `compare` (length $ fst a)) hypMatches
        unmatchedConds = filter (`notElem` matchedConds) subedConditions
        targIndsToRemove = map snd matchedTargs

    removePureTargs (zip (repeat targBoxNumber) targIndsToRemove) tab >>= addPureTargs (zip (repeat targBoxNumber) unmatchedConds)



getDeepestMatchingTargs :: [HoleExpr] -> Tableau -> [([(HoleExpr, Expr, Substitution, Int)], BoxNumber)]
getDeepestMatchingTargs consequentsToMatch tab@(Tableau qZone rootBox@(Box rootHyps rootTargs)) = let
    getDeepestMatchingTargsZipper :: [HoleExpr] -> BoxNumber -> BoxZipper Expr -> [([(HoleExpr, Expr, Substitution, Int)], BoxNumber)]
    getDeepestMatchingTargsZipper consequentsToMatch boxNumber boxZipper@(Box hyps targs, _) = do
        let matchesAtThisLevel = catMaybes [case targs!!targInd of
                BoxTarg _ -> Nothing
                PureTarg targ -> case matchExpressions cons targ of
                    Just sub -> Just (cons, targ, sub, targInd)
                    Nothing -> Nothing
                | cons <- consequentsToMatch, targInd <- [0..length targs-1]]

        let deeperTargs = filter (not . null) $ map (\targInd -> case toBoxNumberFromZipper [targInd] boxZipper of
                Nothing -> []
                Just newZipper ->
                    getDeepestMatchingTargsZipper consequentsToMatch (boxNumber++[targInd]) newZipper)
                [0..length targs-1]
        if null deeperTargs then [(matchesAtThisLevel, boxNumber)]
        else concat deeperTargs
    
    in getDeepestMatchingTargsZipper consequentsToMatch [] (rootBox, [])

-- | NB: currently this function is a bit of a mess. Have another at implementing
-- and improve.
-- We first search for all targets which can match with consequents, and find the
-- deepest possible matches (as these have more hypotheses to match conditions with).
-- After this, we find the single target-consequent match which will maximise the
-- number of matched conditions, then choose this.
libBackwardReasoning :: LibraryImplication -> Tableau -> Maybe Tableau
libBackwardReasoning libImpl@(LibraryImplication libQZone conditions consequents) tab@(Tableau qZone rootBox) = do
    let
        extractBestSub :: [(Substitution, ([HoleExpr], [Expr]))] -> Maybe (Substitution, ([HoleExpr], [Expr]))
        extractBestSub [] = Nothing
        extractBestSub listOfSubs = let
            (best:_) = sortBy (\(_, (unmatchedCondsA, _)) (_, (unmatchedCondsB, _)) -> 
                length unmatchedCondsA `compare` length unmatchedCondsB)
                listOfSubs
            in Just best

        getBestMatchFromLevel :: ([(HoleExpr, Expr, Substitution, Int)], BoxNumber) ->
            Maybe ((HoleExpr, Expr, Substitution, Int), Int)
        getBestMatchFromLevel ([], _) = Nothing
        getBestMatchFromLevel (matches, boxNumber) = do
            usableHyps <- getHypsUsableInBoxNumber boxNumber rootBox
            let bestCandidates = mapMaybe (\(matchedCons, matchedTarg, initialSub, targInd) ->
                    case extractBestSub (findAllPossibleSubs initialSub conditions usableHyps) of
                        Nothing -> Nothing
                        Just bestSub -> Just (bestSub, (matchedCons, matchedTarg, targInd)))
                    matches
            guard $ not $ null bestCandidates
            -- Looks horrible but it's basically just extractBestSub
            let (((finalSub, (condsMatched, _)),(consMatched, targMatched, targInd)):_) = sortBy
                    (\((_,(a,_)),_) ((_,(b,_)),_) -> length a `compare` length b)
                    bestCandidates
            Just ((consMatched, targMatched, finalSub, targInd), length condsMatched)

    let deepestMatchingTargs = getDeepestMatchingTargs consequents tab
        candidatesPerLevel = mapMaybe (\level@(_, boxNumber) -> case getBestMatchFromLevel level of
                Just bestMatch -> Just (bestMatch, boxNumber)
                Nothing -> Nothing) deepestMatchingTargs
    guard $ not $ null candidatesPerLevel
    let (bestCandidate:_) = sortBy (\a b -> snd (fst a) `compare` snd (fst b)) candidatesPerLevel
    let (((matchedCons, matchedTarg, targSub, matchedTargInd), _), targBoxNumber) = bestCandidate
    
    -- At this point we've found the best target to match and the substitution to do
    -- it. It remains now to match as many conditions as possible, then check if we
    -- have also matched additional targets collaterally.
    
    usableHyps <- getHypsUsableInBoxNumber targBoxNumber rootBox
    (Box _ targs,_) <- toBoxNumberFromRoot targBoxNumber rootBox
    let conditionSubs = findAllPossibleSubs targSub conditions usableHyps
    guard $ not $ null conditionSubs
    let (bestSub:_) = sortBy (\(_, (a, _)) (_, (b, _)) -> length a `compare` length b) conditionSubs
        (finalSub, _) = bestSub
        subedCondsMaybe = map (holeExprToExpr . applySubstitution finalSub) conditions
        subedConsequents = mapMaybe (holeExprToExpr . applySubstitution finalSub) consequents
    guard $ all isJust subedCondsMaybe
    guard $ not $ null subedConsequents
    let subedConds = catMaybes subedCondsMaybe
        remainingConds = filter (`notElem` usableHyps) subedConds
        targIndsToRemove = filter (\targInd -> case targs!!targInd of
            PureTarg targ -> targ `elem` subedConsequents
            _ -> False)
            [0..length targs-1]
    
    removePureTargs (zip (repeat targBoxNumber) targIndsToRemove) tab >>= addPureTargs (zip (repeat targBoxNumber) remainingConds)

-- <<< Library Moves that act at the subexpression level >>>

-- Instead of Maybe, we work with lists to keep track of different
-- possibilities that can occur. These can easily be converted to
-- Maybes later, and Haskell's laziness should (hopefully) mean that
-- dealing with lists isn't wasting computational resources.
subLibraryEquivalence :: LibraryEquivalence -> (Int, Int) -> ExprType ->
    (BoxNumber, Int) -> ExprDirections -> Tableau -> [Tableau]
-- First argument is the library equivalence we want to apply.
-- Second argument is the indices of the two equivalents we will use.
-- Third argument indicates whether we are applying the equivalence
-- in a target or a hypothesis. Fourth argument is address of the
-- expression. Fifth argument is directions to the relevant subExpression
subLibraryEquivalence (LibraryEquivalence _ conditions equivalents) (i, j) exprType
    address@(boxNumber, index) directions tab
    | i < 0 || i >= length equivalents || j < 0 || j >= length equivalents = []
    | otherwise = do
        let originalEquivalent = equivalents !! i
        let newEquivalent = equivalents !! j
        rootExpr <- maybeToList $ case exprType of
            H -> getHyp address tab
            T -> getPureTarg address tab
        -- Start with the NBI sustitution that matches the original
        -- equivalent to the subExpression. We use id 0 for the
        -- root expression and id -1 for the original equivalent.
        startingSubstitution <- maybeToList $ matchSubExpression (rootExpr, 0)
            directions (originalEquivalent, -1)
        let hyps = concat $ maybeToList $ getHypsUsableInBoxNumber boxNumber
                $ getRootBox tab
        -- Provide ids starting at 1 for our conditions
        let numberedConditions = zip [1..] conditions
        -- Steps to find all consistent matchings
        -- 1) find all individual matches for conditions
        let matchings :: [[NBISub]]
            matchings = map (\(i, holeExpr) -> mapMaybe
                (\h -> matchExpression (h, i) holeExpr) hyps) numberedConditions
        -- 2) Order them by fewest matchings first (Not strictly
        -- necessary, but include this for efficiency)
        let sortedMatchings = sortBy (\l1 l2 -> length l1 `compare` length l2) matchings
        -- 3) recursively try to merge matchings
        let finalSubs :: [NBISub]
            finalSubs = foldl (\currentSubList possibleNextSubList -> do
                    -- in list monad
                    currentSub <- currentSubList
                    nextSub <- possibleNextSubList
                    maybeToList $ mergeNBISubstitutions currentSub nextSub
                ) [startingSubstitution] sortedMatchings
        nbiSub <- finalSubs

        sub <- maybeToList $ mapM (\(exprDirections, nm) -> do
            -- Only substitutions which specify all the holes in
            -- newEquivalent will succeed
            nbiExpr <- lookup nm nbiSub
            -- the new equivalent is assigned id -2
            expr <- nbiExprToExpr nbiExpr [(exprDirections, -2), (directions, 0)]
            return (exprDirections, expr)) $ getHoleDirections newEquivalent

        newHoleExpr <- maybeToList $ foldM (\currentHoleExpr (exprDirections, expr) ->
            instantiateOneHole currentHoleExpr exprDirections expr)
            newEquivalent sub
        newSubExpr <- maybeToList $ holeExprToExpr newHoleExpr
        
        newExpr <- maybeToList $ (do
                (_, crumbs) <- zFollowDirections (rootExpr, []) directions
                return $ unzipper (newSubExpr, crumbs)
            )
        case exprType of
            H -> maybeToList $ updateHyp address newExpr tab
            T -> maybeToList $ updatePureTarg address newExpr tab
