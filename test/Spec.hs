import SubtaskTests
import SubexpressionMatchingTests
import PositionTests
import Test.HUnit

main :: IO ()
main = do
    runTestTT subtaskTests
    runTestTT subexpressionMatchingTests
    runTestTT positionTests
    putStrLn "end of tests"
