module Robot.Subtasks where

import Robot.Lib
import Robot.TableauFoundation
import Robot.HoleExpr
import Robot.AutomationData
import Robot.BasicMoves
import Robot.BasicMoveHelpers
import Robot.HoleExpr
import Robot.MathematicianMonad

import Data.Maybe
import Control.Monad

data SubtaskType = CreateInTarg | CreateAllInTarg | DestroyInTarg
                 | CreateInHyp | CreateAllInHyp | DestroyInHyp
                 deriving (Eq, Show)

data SubtaskClass = Create | CreateAll | Destroy
                 deriving (Eq)

data Subtask = Subtask { getSubtaskType :: SubtaskType,
                 getExprID :: Maybe Int, -- currently HypIDs and TargIDs are Ints
                 getPattern :: HoleExpr }
                 deriving (Eq, Show)

subtaskTypeToExprType :: SubtaskType -> ExprType
subtaskTypeToExprType subtaskType =
    case subtaskType of
        CreateInTarg -> T
        CreateAllInTarg -> T
        DestroyInTarg -> T
        CreateInHyp -> H
        CreateAllInHyp -> H
        DestroyInHyp -> H

subtaskToExprType :: Subtask -> ExprType
subtaskToExprType subtask = subtaskTypeToExprType $ getSubtaskType subtask

subtaskTypeToSubtaskClass :: SubtaskType -> SubtaskClass
subtaskTypeToSubtaskClass subtaskType =
    case subtaskType of
        CreateInTarg -> Create
        CreateAllInTarg -> CreateAll
        DestroyInTarg -> Destroy
        CreateInHyp -> Create
        CreateAllInHyp -> CreateAll
        DestroyInHyp -> Destroy

subtaskToSubtaskClass :: Subtask -> SubtaskClass
subtaskToSubtaskClass subtask = subtaskTypeToSubtaskClass $ getSubtaskType subtask

subtaskAcheived :: Tableau -> AutData -> Subtask -> Bool
subtaskAcheived tab autData task =
    let exprIndsToCheck = case subtaskToExprType task of
            T -> case getExprID task of
                Nothing -> getAllTargInds tab
                Just targID -> case getTargFromID targID autData of
                    Just targ -> [targ]
                    Nothing -> []  -- The expression we're interested has been destroyed
            H -> case getExprID task of
                Nothing -> getAllHypInds tab
                Just hypID -> case getHypFromID hypID autData of
                    Just hyp -> [hyp]
                    Nothing -> [] -- The expression we're interested has been destroyed
        exprsToCheck = case subtaskToExprType task of
            T -> mapMaybe (\targ -> getPureTarg targ tab) exprIndsToCheck
            H -> mapMaybe (\hyp -> getHyp hyp tab) exprIndsToCheck in
    case subtaskToSubtaskClass task of
        Create -> any (matches $ getPattern task) exprsToCheck
        CreateAll -> any (matchesAll $ getPattern task) exprsToCheck
        Destroy -> not $ any (matches $ getPattern task) exprsToCheck


matchesAll :: HoleExpr -> Expr -> Bool
matchesAll h e = case matchExpressions h e of
    Just _ -> True
    Nothing -> False

matches :: HoleExpr -> Expr -> Bool
matches h e = matchesAll h e || (case e of
    (App e1 e2) -> matches h e1 || matches h e2
    (Abs _ (Sc e')) -> matches h e'
    _ -> False)

-- Given a general destroy subtask (target/hypothesis not specified),
-- returns a specific destroy subtask specifying where the destruction
-- needs to take place
specifyDestroy :: Tableau -> Subtask -> Mathematician Subtask
specifyDestroy tab subtask@(Subtask subtaskType exprID pattern) = do
    autData <- getAutData
    guard $ isNothing exprID
    guard $ subtaskTypeToSubtaskClass subtaskType == Destroy
    let exprType = subtaskTypeToExprType subtaskType
    let exprAddresses = case exprType of
            H -> getAllHypInds tab
            T -> getAllTargInds tab
    let getter = case exprType of
            H -> getHyp
            T -> getPureTarg
    address <- liftMaybe $ listToMaybe $ filter (\exprAddress ->
        case getter exprAddress tab of
            Just e -> matches pattern e
            Nothing -> False) exprAddresses
    let (newAutData, id) = case exprType of
            H -> registerHyp address autData
            T -> registerTarg address autData
    putAutData newAutData
    return $ Subtask subtaskType (Just id) pattern
