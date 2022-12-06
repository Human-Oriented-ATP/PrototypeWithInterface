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
            ActionState action problemState@(ProblemState tab state tabHtml allowedActions) <- jsonData :: ActionM ActionState
            let result = performFunctionOnProblemState action problemState
            case result of
                Just (newTab, newState) -> json (ProblemState newTab newState
                    (renderHtml $ generateTabHtml $ prettifyTab newTab) allowedActions)
                _ -> json problemState

        post "/save" $ do
            problemState <- jsonData :: ActionM ProblemState
            liftIO (writeFile "saved_state.txt" (show problemState))
            json problemState

{-
a :: IO (Maybe Tableau)
a = do
    file <- readFile "saved_state.txt"
    let ProblemState tab _ _ _ = read file
    let res = libBackwardReasoning lesserThanTrans tab
    return res
-}
