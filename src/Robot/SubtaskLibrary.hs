module Robot.SubtaskLibrary where

import Robot.LibraryMoves
import Robot.HoleExpr
import Robot.Parser
import Robot.Subtasks
import Robot.TableauFoundation
import Robot.BasicMoves
import Robot.AutomationData

import Data.Function
import Data.Maybe
import Control.Monad

import qualified Data.HashMap.Lazy as M
import Data.Hashable

-- The index allows us to find library results based on a search term.
-- Implemented as a HashMap for efficiency.
type Index = M.HashMap IndexKey [IndexValue]

data IndexKey = CreateKey HoleExpr | CreateAllKey HoleExpr
    deriving (Eq, Show)

instance Hashable IndexKey where
    hashWithSalt n (CreateKey holeExpr) = hashWithSalt n ('1':show holeExpr)
    hashWithSalt n (CreateAllKey holeExpr) = hashWithSalt n ('2':show holeExpr)

-- When we find a match with a library equivalence, we are also given
-- a pair of equivalents which achieve the searched for task
data IndexValue = EquivalenceValue LibraryEquivalence (Int, Int)

subtaskSearch :: Index -> Subtask -> [IndexValue]
subtaskSearch index subtask@(Subtask subtaskType exprID pattern) =
    -- flip flag used for destroy targets: it requires the equivalence
    -- be applied in reverse
    let (searchTerm, flipFlag) = case subtaskTypeToSubtaskClass subtaskType of
            Create -> (CreateKey pattern, False)
            CreateAll -> (CreateAllKey pattern, False)
            Destroy -> (CreateKey pattern, True)
        flip :: IndexValue -> IndexValue
        flip (EquivalenceValue libraryEquivalence (n1, n2)) =
            EquivalenceValue libraryEquivalence (n2, n1) in
    case index M.!? searchTerm of
        Just indexValues -> if flipFlag then map flip indexValues else indexValues
        Nothing -> []

-- Given a destroy task which specifies an expression,
-- Attempt to achieve the subtask using results from the index
attemptDestroySubtask :: Index -> Subtask -> AutData -> Move
attemptDestroySubtask index task@(Subtask subtaskType exprID pattern) autData tab = do
    guard $ subtaskTypeToSubtaskClass subtaskType == Destroy
    let exprType = subtaskTypeToExprType subtaskType
    eid <- exprID
    address <- case exprType of
        H -> getHypFromID eid autData
        T -> getTargFromID eid autData
    let equivalences = subtaskSearch index task
    let invoker = case exprType of
            H -> libEquivHyp
            T -> libEquivTarg
    listToMaybe $ mapMaybe (\(EquivalenceValue result pair) ->
        invoker result pair address tab) equivalences

-- Intersection and union properties

Just intersectionPropQZone = parseQZone "forall A, forall B, forall x"
Just intersectionPrope = parseWithQZone intersectionPropQZone
    "element_of(x, intersection(A, B)"
Just intersectionPrope' = parseWithQZone intersectionPropQZone
    "and(element_of(x, A), element_of(x, B))"
intersectionProp = LibraryEquivalence intersectionPropQZone []
    (map holeFreeVars [intersectionPrope, intersectionPrope'])

Just unionPropQZone = parseQZone "forall A, forall B, forall x"
Just unionPrope = parseWithQZone unionPropQZone
    "element_of(x, union(A, B))"
Just unionPrope' = parseWithQZone unionPropQZone
    "or(element_of(x, A), element_of(x, B))"
unionProp = LibraryEquivalence unionPropQZone []
    (map holeFreeVars [unionPrope, unionPrope'])

-- Hand-made index for testing purposes. In future functions should be written
-- to populate the index automatically

index :: Index
index = M.empty & M.insert (CreateKey $ HoleCon "intersection")
                           [EquivalenceValue intersectionProp (1, 0)]
                & M.insert (CreateKey $ HoleCon "union")
                           [EquivalenceValue unionProp (1, 0)]
