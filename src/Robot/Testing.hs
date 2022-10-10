{-# OPTIONS -Wno-missing-signatures #-}
{-# OPTIONS -Wno-incomplete-uni-patterns #-}

module Robot.Testing where

import Robot.Lib
import Robot.TableauFoundation
import Robot.Poset
import Robot.BasicMoves
import Robot.LibraryMoves
import Robot.ExistentialMoves
import Robot.BasicMoves
import Robot.PPrinting
import Robot.HoleExpr
import Robot.Parser

import Data.Maybe
import Data.List
import Control.Monad
import Debug.Trace

-- Create a tableau with just one given target
exprToTab :: Expr -> Tableau
exprToTab e = Tableau (Poset [] []) (Box [] [PureTarg e])

-- Parse a string as an expression then turn it into a Tableau as above
stringToTab :: String -> Maybe Tableau
stringToTab s = do
    e <- parseSimple parseExpr s
    return $ exprToTab e

-- <<< MOVE TESTING >>>

-- IMPROVEMENT - have fixed the hacky need for negative InternalName's here using HoleExpr's, but this seemed to hit performance a bit
-- How can we improve this, and why does it affect performance?

openSetDefQZone = Poset [QVar "Forall" (Just $ ExternalName "M") (-1)
    , QVar "Forall" (Just $ ExternalName "d") (-2)
    , QVar "Forall" (Just $ ExternalName "A") (-3)] []
openSetDefH1 = holeFreeVars $ BApp "metric_on" (Free (-2)) (Free (-1))
openSetDefe = holeFreeVars $ TApp "open_in_metric" (Free (-3)) (Free (-2)) (Free (-1))
openSetDefe' = holeFreeVars $ forall (Just $ ExternalName "x") 0 $
    Implies (BApp "element_of" (Free 0) (Free (-3))) $
    exists (Just $ ExternalName "delta") 1 $
    And (BApp "real_greater_than" (Free 1) (Con "0")) $
    forall (Just $ ExternalName "y") 2 $
    Implies (BApp "element_of" (Free 2) (Free (-1))) $
    Implies (BApp "real_lesser_than" (App (App (Free (-2)) (Free 0)) (Free 2)) (Free 1)) $
    BApp "element_of" (Free 2) (Free (-3))
openSetDef = LibraryEquivalence openSetDefQZone [openSetDefH1] [openSetDefe, openSetDefe']

intersectionDefQZone = Poset [ QVar "forall" (Just $ ExternalName "x") (-1)
    , QVar "forall" (Just $ ExternalName "A") (-2)
    , QVar "forall" (Just $ ExternalName "B") (-3)] []
intersectionDefe = holeFreeVars $ BApp ( "element_of") (Free (-1)) (BApp ( "set_intersection") (Free (-2)) (Free (-3)))
intersectionDefe' = holeFreeVars $ And (BApp ( "element_of") (Free (-1)) (Free (-2))) (BApp ( "element_of") (Free (-1)) (Free (-3)))
intersectionDef = LibraryEquivalence intersectionDefQZone [] [intersectionDefe, intersectionDefe']

-- IMPROVEMENT - for now we're storing this as an equivalence because the above code would be identical for an implication, but
-- need to clarify how we want either to work and implement separately.
-- Probably the most sensible way is to store equivalences as suggested, except with a set rather than a pair. Then appropriate function should take two indices giving which two expressions we want to exchange, and the appropriate substitution
-- then checks this is correct and performs equivalence on the desired expression. I guess we also want to specify the condition/hypothesis-mapping, but have the option for it to compute this manually?
-- we could trust that the substitution works if provided, but this would allow the function to create non-sound moves, so probably best not to do this.
-- Similarly, one way implications can just be stored as Tableau's, and we can implement library forward-reasoning and backward-reasoning separately in a similar way?
Just lesserThanTransQZone = parseQZone "forall a, forall b, forall c"
Just lesserThanTransH1 = parseWithQZone lesserThanTransQZone "real_lesser_than(a, b)"
Just lesserThanTransH2 = parseWithQZone lesserThanTransQZone "real_leq(b, c)"
Just lesserThanTransT1 = parseWithQZone lesserThanTransQZone "real_lesser_than(a, c)"
lesserThanTrans = LibraryImplication lesserThanTransQZone
    (map holeFreeVars [lesserThanTransH1, lesserThanTransH2])
    (map holeFreeVars [lesserThanTransT1])

-- Intersection of open sets is open
f1 = forall (Just $ ExternalName "X") (0) $
    forall (Just $ ExternalName "d") (1) $
    forall (Just $ ExternalName "U") (2) $
    forall (Just $ ExternalName "V") (3) $
    Implies (TAnd
        (BApp ( "metric_on") (Free 1) (Free 0))
        (TApp ( "open_in_metric") (Free 2) (Free 1) (Free 0))
        (TApp ( "open_in_metric") (Free 3) (Free 1) (Free 0))) $
    TApp ( "open_in_metric") (BApp ( "set_intersection") (Free 2) (Free 3)) (Free 1) (Free 0)
fTab = exprToTab f1

Just fResult = Just 0

-- Sequence of functions
Just sequenceOfFunctionsQZone = parseQZone "forall X, forall Y, forall f_"
Just sequenceOfFunctionsT1 = parseWithQZone sequenceOfFunctionsQZone "sequence_of_functions(f_, X, Y)"
Just sequenceOfFunctionsT2 = parseWithQZone sequenceOfFunctionsQZone "forall n, implies(element_of(n, naturals), function(f_(n), X, Y))"
sequenceOfFunctionsDef = LibraryEquivalence sequenceOfFunctionsQZone
    (map holeFreeVars [])
    (map holeFreeVars [sequenceOfFunctionsT1, sequenceOfFunctionsT2])

-- Continuous in metric space
continuousDefQZone = Poset [QVar "Forall" (Just $ ExternalName "f") (-1)
    , QVar "Forall" (Just $ ExternalName "d_X") (-2)
    , QVar "Forall" (Just $ ExternalName "X") (-3)
    , QVar "Forall" (Just $ ExternalName "d_Y") (-4)
    , QVar "Forall" (Just $ ExternalName "Y") (-5)] []
continuousDefH1 = holeFreeVars $ BApp "metric_on" (Free (-2)) (Free (-3))
continuousDefH2 = holeFreeVars $ BApp "metric_on" (Free (-4)) (Free (-5))
continuousDefH3 = holeFreeVars $ TApp "function" (Free (-1)) (Free (-3)) (Free (-5))
continuousDefe = holeFreeVars $ PApp "continuous_in_metric_space" (Free (-1)) (Free (-2)) (Free (-3)) (Free (-4)) (Free (-5))
continuousDefe' = holeFreeVars $
    forall (Just $ ExternalName "x") 0 $ Implies (BApp "element_of" (Free 0) (Free (-3))) $
    forall (Just $ ExternalName "epsilon") 1 $ Implies (BApp "real_greater_than" (Free 1) (Con "0")) $
    exists (Just $ ExternalName "delta") 2 $ And (BApp "real_greater_than" (Free 2) (Con "0")) $
    forall (Just $ ExternalName "y") 3 $ Implies (BApp "element_of" (Free 3) (Free (-3))) $
    Implies (BApp "real_lesser_than" (App (App (Free (-2)) (Free 0)) (Free 3)) (Free 2)) $
    BApp "real_lesser_than" (App (App (Free (-4)) (App (Free (-1)) (Free 0))) (App (Free (-1)) (Free 3))) (Free 1)
continuousDef = LibraryEquivalence continuousDefQZone [continuousDefH1, continuousDefH2, continuousDefH3] [continuousDefe, continuousDefe']



-- IMPROVEMENT - think about exactly how much information we include. For example, do we really need things like "metric_on" as conditions, given that this is implicit from the uniform_limit_of_functions_metric_space? I don't know.
-- gonna exclude it for now
uniformLimDefQZone = Poset [QVar "Forall" (Just $ ExternalName "f_") (-1)
    , QVar "Forall" (Just $ ExternalName "f") (-2)
    , QVar "Forall" (Just $ ExternalName "X") (-3)
    , QVar "Forall" (Just $ ExternalName "d_Y") (-4)
    , QVar "Forall" (Just $ ExternalName "Y") (-5)] []
uniformLimDefe = holeFreeVars $ PApp ( "uniform_limit_of_functions_metric_space") (Free (-1)) (Free (-2)) (Free (-3)) (Free (-4)) (Free (-5))
uniformLimDefe' = holeFreeVars $ forall (Just $ ExternalName "theta") (0) $ Implies (BApp ( "real_greater_than") (Free 0) (Con "0")) $
    exists (Just $ ExternalName "N") (1) $ And (BApp ( "element_of") (Free 1) (Con $  "naturals")) $
    forall (Just $ ExternalName "n") (2) $ Implies (And (BApp ( "element_of") (Free 2) (Con $  "naturals")) (BApp ( "real_greater_than") (Free 2) (Free 1))) $
    forall (Just $ ExternalName "x") (3) $ Implies (BApp ( "element_of") (Free 3) (Free (-3))) $
    BApp ( "real_lesser_than") (App (App (Free (-4)) (App (App (Free (-1)) (Free 2)) (Free 3))) (App (Free (-2)) (Free 3))) (Free 0)
uniformLimDef = LibraryEquivalence uniformLimDefQZone [] [uniformLimDefe, uniformLimDefe']


-- Triangle inequality version
Just triIneqQZone = parseQZone "forall X, forall d, forall w, forall x, forall y, forall z, forall a, forall b, forall c"
Just triIneqH1 = parseWithQZone triIneqQZone "metric_on(d, X)"
Just triIneqH2 = parseWithQZone triIneqQZone "real_lesser_than(d(w, x), a)"
Just triIneqH3 = parseWithQZone triIneqQZone "real_lesser_than(d(z, y), b)"
Just triIneqH4 = parseWithQZone triIneqQZone "real_lesser_than(d(w, z), c)"
Just triIneqT1 = parseWithQZone triIneqQZone "real_lesser_than(d(x, y), real_plus(a, real_plus(b, c)))"
triIneq = LibraryImplication triIneqQZone
    (map holeFreeVars [triIneqH1, triIneqH2, triIneqH3, triIneqH4])
    (map holeFreeVars [triIneqT1])


-- Uniform limit of cts functions is cts
g1 = forall (Just $ ExternalName "X") (0) $
    forall (Just $ ExternalName "Y") (1) $
    forall (Just $ ExternalName "d_X") (2) $
    forall (Just $ ExternalName "d_Y") (3) $
    forall (Just $ ExternalName "f") (4) $
    forall (Just $ ExternalName "f_") (5) $
    Implies (HAnd
        (BApp ( "metric_on") (Free 2) (Free 0))
        (BApp ( "metric_on") (Free 3) (Free 1))
        (TApp ( "function") (Free 4) (Free 0) (Free 1))
        (TApp ( "sequence_of_functions") (Free 5) (Free 0) (Free 1))
        (PApp ( "uniform_limit_of_functions_metric_space") (Free 5) (Free 4) (Free 0) (Free 3) (Free 1))
        (forall (Just $ ExternalName "n") (6) $ Implies (BApp ( "element_of") (Free 6) (Con $  "naturals")) (PApp ( "continuous_in_metric_space") (App (Free 5) (Free 6)) (Free 2) (Free 0) (Free 3) (Free 1))))$
    PApp ( "continuous_in_metric_space") (Free 4) (Free 2) (Free 0) (Free 3) (Free 1)

gTab = exprToTab g1

Just gResult = peelUniversalTarg ([], 0) gTab >>= peelUniversalTarg ([], 0) >>= peelUniversalTarg ([], 0) >>= peelUniversalTarg ([], 0) >>= peelUniversalTarg ([], 0) >>= peelUniversalTarg ([], 0)
    >>= tidyImplInTarg ([], 0) >>= tidyAndInHyp ([], 0) >>= tidyAndInHyp ([], 0) >>= tidyAndInHyp ([], 0) >>= tidyAndInHyp ([], 0) >>= tidyAndInHyp ([], 0)
    >>= libEquivTarg continuousDef (0, 1) ([], 0) >>= peelUniversalTarg ([], 0)
    >>= tidyImplInTarg ([], 0) >>= peelUniversalTarg ([], 0) >>= tidyImplInTarg ([], 0)
    >>= peelExistentialTarg ([], 0) >>= tidyAndInTarg ([], 0)
    >>= peelUniversalTarg ([], 1) >>= tidyImplInTarg ([], 1)
    >>= tidyImplInTarg ([1], 0) >>= libEquivHyp uniformLimDef (0, 1) ([], 2)
    >>= peelUniversalHyp ([], 2) >>= commitToHyp ([], 8)
    >>= peelExistentialHyp ([1], 0) >>= tidyAndInHyp ([1], 0) >>= peelUniversalHyp ([1], 1)
    >>= commitToHyp ([1], 2) >>= modusPonens ([1,1], 0) ([1,1,1], 0)
    >>= modusPonens ([1,1], 0) ([], 6) >>= peelUniversalHyp ([], 1)
    >>= commitToHyp ([], 9) >>= libEquivHyp sequenceOfFunctionsDef (0, 1) ([], 3)
    >>= peelUniversalHyp ([], 3) >>= commitToHyp ([], 10)
    >>= instantiateExistential "b" "a"
    >>= libEquivHyp continuousDef (0, 1) ([1, 1], 0)
    >>= modusPonens ([1,1], 0) ([], 6) >>= peelUniversalHyp ([1,1], 1)
    >>= commitToHyp ([1,1], 2) >>= peelExistentialHyp ([1,1,1], 0) >>= tidyAndInHyp ([1,1,1], 0)
    >>= modusPonens ([1,1,1], 1) ([1,1,1,1,1,1], 0) >>= instantiateExistential "delta" "c"
    >>= rawModusPonens ([1,1,1,1,1,1], 3) ([1,1,1,1,1,1], 1)
    >>= instantiateExistential "a" "n" >>= libForwardReasoning triIneq
    >>= instantiateExistential "b" "theta"

at1 = exists (Just $ ExternalName "x") 0 (forall (Just $ ExternalName "y") 0 (exists (Just $ ExternalName "z") 1 (Eq (Free 0) (Free 1))))
aBox = Box [] [PureTarg at1]
aQZone = Poset [] []
aTab = Tableau aQZone aBox
Just aResult = Just 0



-- Universal modus ponens with hyp
bh1 = forall (Just $ ExternalName "x") 0 $
    Implies (Eq (UApp ( "succ") (Free 0)) (Con ( "1"))) (Eq (Free 0) (Con ( "0")))

bh2= Eq (UApp ( "succ") (Free 1)) (Con ( "1"))

bTestHead = Poset [QVar "Forall" (Just $ ExternalName "y") 1] []
bTestBox = Box [bh1, bh2] []
Just bResult = Just 0


-- Implication in target tidy
ct1 = Implies (Eq (UApp ( "succ") (Free 0)) (UApp ( "succ") (Free 1))) (Eq (Free 0) (Free 1))
cTestHead = Poset [QVar "Forall" (Just $ ExternalName "x") 0, QVar "Forall" (Just $ ExternalName "y") 1] []
cTestBox = Box [] [PureTarg ct1]
cTestQBox = (cTestHead, cTestBox)
cTestTab = Tableau cTestHead cTestBox
Just cResult = Just 0



-- Forwards and backwards reasoning
Just xQZone' = parseQZone "forall M, forall d, forall U, forall V"
Just xh1 = parseWithQZone xQZone' "metric_on(d, M)"
Just xh2 = parseWithQZone xQZone' "open_in_metric(U, d, M)"
Just xh3 = parseWithQZone xQZone' "open_in_metric(V, d, M)"
Just xt1 = parseWithQZone xQZone' "open_in_metric(set_intersection(U, V), d, M)"
forwardReasoningTestLib = LibraryImplication xQZone'
    (map holeFreeVars [xh1, xh2, xh3])
    (map holeFreeVars [xt1])

Just xQZone = parseQZone "forall M, forall d, forall U, forall V"
Just xhh1 = parseWithQZone xQZone "metric_on(d, M)"
Just xhh2 = parseWithQZone xQZone "open_in_metric(U, d, M)"
Just xhh3 = parseWithQZone xQZone "open_in_metric(V, d, M)"
Just xtt1 = parseWithQZone xQZone "open_in_metric(set_intersection(U, V), d, M)"
xTab = Tableau xQZone (Box [xhh1, xhh2, xhh3] [PureTarg xtt1])

Just a' = Just 0
Just b' = Just 0

-- Library definitions for testing purposes only (created by Matei for
-- testing the tracking system)

-- Testing tracking of tidyImplInTarg

-- an alias for implication that forces us to use a library equivalence
Just mimpliesQZone = parseQZone "forall A, forall B"
Just mimpliese = parseWithQZone mimpliesQZone "mimplies(A, B)"
Just mimpliese' = parseWithQZone mimpliesQZone "implies(A, B)"
mimplies = LibraryEquivalence mimpliesQZone []
    (map holeFreeVars [mimpliese, mimpliese'])

-- an alias for quantification that forces us to use a library equivalence
Just mforallQZone = parseQZone "forall P"
Just mforalle = parseWithQZone mforallQZone "mforall(P)"
Just mforalle' = parseWithQZone mforallQZone "forall x, P(x)"
mforall = LibraryEquivalence mforallQZone []
    (map holeFreeVars [mforalle, mforalle'])

Just mTab = stringToTab "implies(forall x, Q(x), and(mimplies(mforall(P), mforall(Q)), implies(forall x, P(x), forall x, Q(x))))"


-- Testing tracking of commitToHyp
Just nTab = stringToTab "implies(and(implies(P, forall x, Q(x)), implies(P, R)), S)"

-- Test problem state for subtask development

s1 = "forall A, forall B, forall C, forall D, " ++
    "implies(and(exists x, element_of(x, A), " ++
                "and(forall x, implies(element_of(x, A), element_of(x, B)), " ++
                    "forall x, implies(element_of(x, intersection(A, B)), element_of(x, C)))), " ++
    "exists x, element_of(x, union(C, D)))"
Just s1Tab = stringToTab s1 >>= tidyEverything >>= peelExistentialTarg ([], 0)
