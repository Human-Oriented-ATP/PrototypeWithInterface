import SubtaskTests
import Test.HUnit

main :: IO ()
main = do
    runTestTT subtaskTests
    putStrLn "end of tests"
