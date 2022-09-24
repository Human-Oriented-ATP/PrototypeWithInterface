{-# LANGUAGE OverloadedStrings #-}

module APICode.HTMLGeneration where

import Robot.TableauFoundation
import Robot.PPrinting

import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import qualified Data.Text as T
import Data.Foldable

targHtml :: BoxNumber -> Int -> Targ String -> H.Html
targHtml boxNumber targInd (PureTarg str) = H.div H.! A.class_ "targ_container" $ H.div H.! A.class_ "targ" H.! A.id (H.toValue (show (boxNumber, targInd))) $
    do
        H.span H.! A.class_ "expression_label" $ H.toHtml (boxNumberToStr boxNumber++"."++show targInd++": ")
        H.toHtml str
targHtml boxNumber targInd (BoxTarg box) = boxHtml (boxNumber++[targInd]) box

generateHypsHtml :: BoxNumber -> [String] -> H.Html
generateHypsHtml _ [] = H.div H.! A.class_ "hyp" $ H.toHtml ("(empty)" :: T.Text)
generateHypsHtml boxNumber [hyp] = H.div H.! A.class_ "hyp" H.! A.id (H.toValue (show (boxNumber, 0 :: Int))) $
    do
        H.span H.! A.class_ "expression_label" $ H.toHtml (boxNumberToStr boxNumber++".0: ")
        H.toHtml hyp
generateHypsHtml boxNumber (firstHyp:rest) =  do
    H.div H.! A.class_ "hyp" H.! A.id (H.toValue (show (boxNumber, 0 :: Int))) $
        do
            H.span H.! A.class_ "expression_label" $ H.toHtml (boxNumberToStr boxNumber++".0: ")
            H.toHtml firstHyp
    for_ (zip [1..] rest) $ \(hypInd, hyp) -> do
        H.br
        H.div H.! A.class_ "hyp" H.! A.id (H.toValue (show (boxNumber, hypInd))) $
            do
                H.span H.! A.class_ "expression_label" $ H.toHtml (boxNumberToStr boxNumber++"."++show hypInd++": ")
                H.toHtml hyp

generateTargsHtml :: BoxNumber -> [Targ String] -> H.Html
generateTargsHtml _ [] = H.div H.! A.class_ "targ" $ H.toHtml ("(empty)" :: T.Text)
generateTargsHtml boxNumber [targ] = targHtml boxNumber 0 targ
generateTargsHtml boxNumber targs = let (last:rest) = reverse (zip [0..] targs) in do
    for_ (reverse rest) $ \(targInd, targ) -> do
        targHtml boxNumber targInd targ
        H.div H.! A.class_ "resizer" $ H.toHtml ("" :: T.Text)
    targHtml boxNumber (fst last) (snd last)

boxHtml :: BoxNumber -> Box String -> H.Html
boxHtml boxNumber (Box hyps targs) = do
    H.div H.! A.class_ "box v_resize" H.! A.id (H.toValue (show boxNumber)) $ do
        H.div H.! A.class_ "hyps" $ generateHypsHtml boxNumber hyps
        H.div H.! A.class_ "resizer" $ H.toHtml ("" :: T.Text)
        H.div H.! A.class_ "targs h_resize" $ generateTargsHtml boxNumber targs

generateTabHtml :: PrettyTableau -> H.Html
generateTabHtml (PrettyTableau qZone rootBox) = do
    H.div H.! A.id "qZone" $ H.toHtml qZone
    boxHtml [] rootBox
