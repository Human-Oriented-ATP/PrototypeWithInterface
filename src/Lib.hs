{-# LANGUAGE OverloadedStrings #-}

module Lib where

import Robot.PPrinting
import Robot.TableauFoundation
import Robot.LibraryMoves
import Robot.Testing

import APICode.CorsBoilerplate
import APICode.JSONTypes
import APICode.HTMLGeneration
import APICode.FunctionCaller

import Web.Scotty
import Network.Wai.Middleware.Static
import Text.Blaze.Html.Renderer.Text (renderHtml)
import Control.Monad.IO.Class


libMain :: IO ()
libMain = do
    putStrLn "Starting Server..."
    scotty 3000 $ do
        middleware corsified
        middleware allowCsrf
        middleware $ staticPolicy (noDots >-> addBase "static")

        get "/teststate" $ do
            json testState --change this for an alternative problem, e.g. mTestState

        post "/move" $ do
            ActionState action problemState@(ProblemState tab autData tabHtml allowedActions proofHistory) <- jsonData :: ActionM ActionState
            let result = performFunctionOnProblemState action problemState
            case result of
                Just (TableauOut newTab) -> json (ProblemState newTab autData (renderHtml $ generateTabHtml $ prettifyTab newTab) allowedActions
                    ((tab, autData, tabHtml):proofHistory))
                Just (TabAndAutDataOut newAutData newTab) -> json (
                    ProblemState newTab newAutData (renderHtml $ generateTabHtml $ prettifyTab newTab) allowedActions
                    ((tab, autData, tabHtml):proofHistory))
                _ -> json problemState

        post "/save" $ do
            problemState@(ProblemState _ _ _ allowedActions proofHistory) <- jsonData :: ActionM ProblemState
            liftIO (writeFile "saved_state.txt" (show problemState))
            json problemState


a :: IO (Maybe Tableau)
a = do
    file <- readFile "saved_state.txt"
    let ProblemState tab _ _ _ _ = read file
    let res = libBackwardReasoning lesserThanTrans tab
    return res