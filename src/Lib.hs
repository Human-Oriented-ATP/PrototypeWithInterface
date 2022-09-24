{-# LANGUAGE OverloadedStrings #-}

module Lib where

import Robot.PPrinting

import APICode.CorsBoilerplate
import APICode.JSONTypes
import APICode.HTMLGeneration
import APICode.FunctionCaller

import Web.Scotty
import Network.Wai.Middleware.Static
import qualified Data.Text.Internal.Lazy as LT
import Text.Blaze.Html.Renderer.Text (renderHtml)


libMain :: IO ()
libMain = do
    putStrLn "Starting Server..."
    scotty 3000 $ do
        middleware corsified
        middleware allowCsrf
        middleware $ staticPolicy (noDots >-> addBase "static")

        get "/teststate" $ do
            json testState

        post "/move" $ do
            ActionState action problemState@(ProblemState _ _ allowedActions proofHistory) <- jsonData :: ActionM ActionState
            let result = performFunctionOnProblemState action problemState
            case result of
                Just (TableauOut newTab) -> json (ProblemState newTab (renderHtml $ generateTabHtml $ prettifyTab newTab) allowedActions proofHistory)
                _ -> json problemState
