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
import Robot.MathematicianMonad

import APICode.JSONTypes
import APICode.HTMLGeneration

import Text.Blaze.Html.Renderer.Text (renderHtml)

import Data.List.Split

type Output = (Tableau, MathematicianState)

performFunctionOnProblemState :: String -> ProblemState -> Maybe Output
performFunctionOnProblemState "" _ = Nothing
performFunctionOnProblemState str (ProblemState tab state _ _) =
    let (functionToApply:rest) = words str
    in case functionToApply of
        "undo" -> do
            [] <- Just rest
            runMathematician (undo tab) state
        "peelUniversalTarg" -> do
            [exprLoc] <- Just rest
            runMathematician (peelUniversalTarg (read exprLoc :: (BoxNumber, Int)) tab) state
        "peelExistentialTarg" -> do
            [exprLoc] <- Just rest
            runMathematician (peelExistentialTarg (read exprLoc :: (BoxNumber, Int)) tab) state
        "peelUniversalHyp" -> do
            [exprLoc] <- Just rest
            runMathematician (peelUniversalHyp (read exprLoc :: (BoxNumber, Int)) tab) state
        "peelExistentialHyp" -> do
            [exprLoc] <- Just rest
            runMathematician (peelExistentialHyp (read exprLoc :: (BoxNumber, Int)) tab) state
        
        "tidyImplInTarg" -> do
            [exprLoc] <- Just rest
            runMathematician (tidyImplInTarg (read exprLoc :: (BoxNumber, Int)) tab) state
        "commitToHyp" -> do
            [exprLoc] <- Just rest
            runMathematician (commitToHyp (read exprLoc :: (BoxNumber, Int)) tab) state
        
        "tidyAndInHyp" -> do
            [exprLoc] <- Just rest
            runMathematician (tidyAndInHyp (read exprLoc :: (BoxNumber, Int)) tab) state
        "tidyAndInTarg" -> do
            [exprLoc] <- Just rest
            runMathematician (tidyAndInTarg (read exprLoc :: (BoxNumber, Int)) tab) state
        
        "tidyEverything" -> do
            [] <- Just rest
            runMathematician (tidyEverything tab) state
        "modusPonens" -> do
            [h1, h2] <- Just rest
            runMathematician (modusPonens (read h1 :: (BoxNumber, Int)) (read h2 :: (BoxNumber, Int)) tab) state
        "modusPonensRaw" -> do
            [h1, h2] <- Just rest
            runMathematician (rawModusPonens (read h1 :: (BoxNumber, Int)) (read h2 :: (BoxNumber, Int)) tab) state
        
        "libEquivHyp" -> do
            [libEquivStr, swapToDo, exprLoc] <- Just rest
            libEquiv <- libEquivFromString libEquivStr
            runMathematician (libEquivHyp libEquiv (read swapToDo :: (Int, Int)) (read exprLoc :: (BoxNumber, Int)) tab) state
        "libEquivTarg" -> do
            [libEquivStr, swapToDo, exprLoc] <- Just rest
            libEquiv <- libEquivFromString libEquivStr
            runMathematician (libEquivTarg libEquiv (read swapToDo :: (Int, Int)) (read exprLoc :: (BoxNumber, Int)) tab) state
        "libForwardReasoning" -> do
            [libImplStr] <- Just rest
            libImpl <- libImplFromString libImplStr
            runMathematician (libForwardReasoning libImpl tab) state
        "libBackwardReasoning" -> do
            [libImplStr] <- Just rest
            libImpl <- libImplFromString libImplStr
            runMathematician (libBackwardReasoning libImpl tab) state
        "instantiateExistential" -> do
            let exprs = splitOn "->" $ unwords rest
            [varA, varB] <- Just exprs
            runMathematician (instantiateExistential varA varB tab) state

        "waterfall" -> do
            [] <- Just rest
            runMathematician (waterfall tab) state
            
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

stateAndTabToProblemState :: (Tableau, MathematicianState) -> ProblemState
stateAndTabToProblemState (tab, state) = ProblemState { getTab = tab, getState = state,
    getTabHtml = renderHtml $ generateTabHtml $ prettifyTab tab,
    getAllowedActions = [] }

testState :: ProblemState
testState = stateAndTabToProblemState gResult
