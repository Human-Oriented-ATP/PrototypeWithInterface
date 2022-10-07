module APICode.FunctionCaller where

import Robot.Lib
import Robot.TableauFoundation
import Robot.LibraryMoves
import Robot.BasicMoves
import Robot.Automation
import Robot.Testing
import Robot.ExistentialMoves
import Robot.PPrinting
import Robot.AutomationData

import APICode.JSONTypes
import APICode.HTMLGeneration

import Text.Blaze.Html.Renderer.Text (renderHtml)

import Data.List.Split

data AcceptableOutput = TableauOut Tableau | TabAndAutDataOut AutData Tableau | ExprOut Expr

performFunctionOnProblemState :: String -> ProblemState -> Maybe AcceptableOutput
performFunctionOnProblemState "" _ = Nothing
performFunctionOnProblemState str (ProblemState tab autData _ _ _) =
    let (functionToApply:rest) = words str
    in case functionToApply of
        "peelUniversalTarg" -> do
            [exprLoc] <- Just rest
            fmap TableauOut (peelUniversalTarg (read exprLoc :: (BoxNumber, Int)) tab)
        "peelExistentialTarg" -> do
            [exprLoc] <- Just rest
            fmap TableauOut (peelExistentialTarg (read exprLoc :: (BoxNumber, Int)) tab)
        "peelUniversalHyp" -> do
            [exprLoc] <- Just rest
            fmap TableauOut (peelUniversalHyp (read exprLoc :: (BoxNumber, Int)) tab)
        "peelExistentialHyp" -> do
            [exprLoc] <- Just rest
            fmap TableauOut (peelExistentialHyp (read exprLoc :: (BoxNumber, Int)) tab)
        
        "tidyImplInTarg" -> do
            [exprLoc] <- Just rest
            fmap TableauOut (tidyImplInTarg (read exprLoc :: (BoxNumber, Int)) tab)
        "commitToHyp" -> do
            [exprLoc] <- Just rest
            fmap TableauOut (commitToHyp (read exprLoc :: (BoxNumber, Int)) tab)
        
        "tidyAndInHyp" -> do
            [exprLoc] <- Just rest
            fmap TableauOut (tidyAndInHyp (read exprLoc :: (BoxNumber, Int)) tab)
        "tidyAndInTarg" -> do
            [exprLoc] <- Just rest
            fmap TableauOut (tidyAndInTarg (read exprLoc :: (BoxNumber, Int)) tab)
        
        "tidyEverything" -> do
            [] <- Just rest
            fmap TableauOut (tidyEverything tab)
        "modusPonens" -> do
            [h1, h2] <- Just rest
            fmap TableauOut (modusPonens (read h1 :: (BoxNumber, Int)) (read h2 :: (BoxNumber, Int)) tab)
        "modusPonensRaw" -> do
            [h1, h2] <- Just rest
            fmap TableauOut (rawModusPonens (read h1 :: (BoxNumber, Int)) (read h2 :: (BoxNumber, Int)) tab)
        
        "libEquivHyp" -> do
            [libEquivStr, swapToDo, exprLoc] <- Just rest
            libEquiv <- libEquivFromString libEquivStr
            fmap TableauOut (libEquivHyp libEquiv (read swapToDo :: (Int, Int)) (read exprLoc :: (BoxNumber, Int)) tab)
        "libEquivTarg" -> do
            [libEquivStr, swapToDo, exprLoc] <- Just rest
            libEquiv <- libEquivFromString libEquivStr
            fmap TableauOut (libEquivTarg libEquiv (read swapToDo :: (Int, Int)) (read exprLoc :: (BoxNumber, Int)) tab)
        "libForwardReasoning" -> do
            [libImplStr] <- Just rest
            libImpl <- libImplFromString libImplStr
            fmap TableauOut (libForwardReasoning libImpl tab)
        "libBackwardReasoning" -> do
            [libImplStr] <- Just rest
            libImpl <- libImplFromString libImplStr
            fmap TableauOut (libBackwardReasoning libImpl tab)
        "instantiateExistential" -> do
            let exprs = splitOn "->" $ unwords rest
            [varA, varB] <- Just exprs
            fmap TableauOut (instantiateExistential varA varB tab)

        "waterfall" -> do
            [] <- Just rest
            case waterfall autData tab of
                Just (newAutData, newTab) -> Just $ TabAndAutDataOut newAutData newTab
                Nothing -> Nothing
            
        _ -> Nothing

libImplFromString :: String -> Maybe LibraryImplication
libImplFromString "triIneq" = Just triIneq
libImplFromString "lesserThanTrans" = Just lesserThanTrans
libImplFromString _ = Nothing

libEquivFromString :: String -> Maybe LibraryEquivalence
libEquivFromString "continuousDef" = Just continuousDef
libEquivFromString "uniformLimDef" = Just uniformLimDef
libEquivFromString "sequenceOfFunctionsDef" = Just sequenceOfFunctionsDef
libEquivFromString "openSetDef" = Just openSetDef
libEquivFromString "intersectionDef" = Just intersectionDef
libEquivFromString _ = Nothing


testState :: ProblemState
testState = ProblemState { getTab = s1Tab, getAutData = startAutData,
    getTabHtml = renderHtml $ generateTabHtml $ prettifyTab s1Tab,
    getAllowedActions = [], getProofHistory = []}
