import SubtaskTests
import SubexpressionMatchingTests
import Test.HUnit

main :: IO ()
main = do
    runTestTT subtaskTests
    runTestTT subexpressionMatchingTests
    putStrLn "end of tests"
