module Tests

import Data.Vect

import Core
import Executer
import Primitives

%access public export

-- tests intentionally taken from original Yampa

testSF1 : SF [C Double] [C Double] _ -> Vect 25 Double
testSF1 sf =
  let (_, res) = runSF input sf
  in map (\[x] => x) res
  where
    input : Vect 25 (SVRep [C Double], DTime)
    -- is it correct place to handle t0? original yampa seem to handle it in the core,
    -- but this implementation is currently without uninitialized signals
    input = map (\a => ([fromInteger a], if a == 0 then 0 else 0.25)) (fromList [0..24])

testSF2 : SF [C Double] [C Double] _ -> Vect 25 Double
testSF2 sf =
  let (_, res) = runSF input sf
  in map (\[x] => x) res
  where
    input : Vect 25 (SVRep [C Double], DTime)
    input = map (\a => ([cast (a `div` 5)], if a == 0 then 0 else 0.25)) (fromList [0..24])

assert : (Eq a, Show a) => String -> a -> a -> IO ()
assert name res expected = do
  putStr "Testing "
  putStr name
  putStr "..."
  if res == expected
    then putStrLn "OK"
    else do
      putStrLn "FAILED!!!"
      putStr "Expected: "
      putStrLn $ show expected
      putStr "Got: "
      putStrLn $ show res

basics : IO ()
basics = do
  assert "identity" (testSF1 identity) $ map fromInteger (fromList [0..24])
  assert "constant" (testSF1 (constant 42.0)) $ map (const 42.0) (fromList [0..24])
  -- localTime
  assert "time" (testSF1 time)
    [0.0, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 1.75, 2.0, 2.25,
     2.5, 2.75, 3.0, 3.25, 3.5, 3.75, 4.0, 4.25, 4.5, 4.75,
     5.0, 5.25, 5.5, 5.75, 6.0]
  -- assert "initially" (testSF1 (initially 42.0))
  --   [42.0, 1.0,  2.0,  3.0,  4.0,  5.0,  6.0,  7.0,  8.0,  9.0,
  --    10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0, 17.0, 18.0, 19.0,
  --    20.0, 21.0, 22.0, 23.0, 24.0]

comp : IO ()
comp = do
  assert "comp_t0" (testSF1 $ pure (+1) >>> pure (+2))
    [3.0,4.0,5.0,6.0,7.0,8.0,9.0,10.0,11.0,12.0,13.0,14.0,15.0,16.0,17.0,
     18.0,19.0,20.0,21.0,22.0,23.0,24.0,25.0,26.0,27.0]
  assert "comp_t1" (testSF2 $ pure (+1) >>> (pure (+2)))
    [3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0,5.0,5.0,5.0,5.0,5.0,
     6.0,6.0,6.0,6.0,6.0,7.0,7.0,7.0,7.0,7.0]
  assert "comp_t2" (testSF1 $ constant 5.0 >>> pure (+1))
    [6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,
    6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0]
  assert "comp_t3" (testSF2 $ constant 5.0 >>> pure (+1))
    [6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,
     6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0]
  assert "comp_t4" (testSF1 $ constant 2.0 >>> integral)
    [0.0,0.5,1.0,1.5,2.0,2.5,3.0,3.5,4.0,4.5,5.0,5.5,6.0,6.5,7.0,7.5,8.0,8.5,
     9.0,9.5,10.0,10.5,11.0,11.5,12.0]
  assert "comp_t5" (testSF2 $ constant 2.0 >>> integral)
    [0.0,0.5,1.0,1.5,2.0,2.5,3.0,3.5,4.0,4.5,5.0,5.5,6.0,6.5,7.0,7.5,8.0,8.5,
     9.0,9.5,10.0,10.5,11.0,11.5,12.0]
