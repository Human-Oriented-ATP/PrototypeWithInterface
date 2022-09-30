{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use first" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Redundant $" #-}
{-# HLINT ignore "Redundant if" #-}
{-# HLINT ignore "Use bimap" #-}
{-# OPTIONS -Wno-unused-imports #-}

module Robot.Automation where

import Robot.Lib
import Robot.TableauFoundation
import Robot.Poset
import Robot.PPrinting
import Robot.BasicMoves
import Robot.LibraryMoves

import Data.Maybe
import Data.List
import Control.Monad
import Debug.Trace

autPeelUniversalTarg :: Tableau -> Maybe Tableau
autPeelUniversalTarg tab = Nothing
