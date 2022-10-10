module SubtaskTests (subtaskTests) where

import Robot.Subtasks
import Robot.SubtaskLibrary
import Robot.AutomationData
import Robot.HoleExpr
import Robot.Testing (s1Tab)

import Test.HUnit

subtaskTests :: Test
subtaskTests = TestLabel "Subtask Tests" $ (TestList [subtaskTest1, subtaskTest2,
    subtaskTest3, subtaskTest4])

s1AutData :: AutData
s1AutData = startAutData

subtask1 :: Subtask
subtask1 = Subtask DestroyInTarg Nothing (HoleCon "union")

subtask2 :: Subtask
subtask2 = Subtask CreateInHyp Nothing (HoleCon "element_of")

subtask3 :: Subtask
subtask3 = Subtask CreateAllInHyp Nothing (HoleCon "element_of")

subtask4 :: Subtask
subtask4 = Subtask CreateAllInHyp Nothing
    (HoleApp (HoleApp (HoleCon "element_of") (Hole 0)) (Hole 1))


subtaskTest1 :: Test
subtaskTest1 = TestCase (assertEqual "subtask1 for problemState1" False
    (subtaskAcheived s1Tab s1AutData subtask1))

subtaskTest2 :: Test
subtaskTest2 = TestCase (assertEqual "subtask1 for problemState1" True
    (subtaskAcheived s1Tab s1AutData subtask2))

subtaskTest3 :: Test
subtaskTest3 = TestCase (assertEqual "subtask1 for problemState1" False
    (subtaskAcheived s1Tab s1AutData subtask3))

subtaskTest4 :: Test
subtaskTest4 = TestCase (assertEqual "subtask1 for problemState1" True
    (subtaskAcheived s1Tab s1AutData subtask4))
