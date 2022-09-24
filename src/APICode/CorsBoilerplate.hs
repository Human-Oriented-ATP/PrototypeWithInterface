{-# LANGUAGE OverloadedStrings #-}

module APICode.CorsBoilerplate where

import Network.Wai.Middleware.Cors
import Network.Wai (Middleware)
import Network.Wai.Middleware.AddHeaders


corsified :: Middleware
corsified = cors (const $ Just appCorsResourcePolicy)

allowCsrf :: Middleware
allowCsrf = addHeaders [("Access-Control-Allow-Headers", "x-csrf-token,authorization")]

appCorsResourcePolicy :: CorsResourcePolicy
appCorsResourcePolicy = CorsResourcePolicy {
    corsOrigins        = Nothing
  , corsMethods        = ["OPTIONS", "GET", "PUT", "POST"]
  , corsRequestHeaders = ["Authorization", "Content-Type"]
  , corsExposedHeaders = Nothing
  , corsMaxAge         = Nothing
  , corsVaryOrigin     = False
  , corsRequireOrigin  = False
  , corsIgnoreFailures = False
}
