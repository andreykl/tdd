module Main

import Data.Primitives.Views

%default total

randoms : Int -> Stream Int
randoms seed = let seed' = 1664242 * seed - 1888934 in (seed' `shiftR` 2) :: randoms seed'

bound : Stream Int -> Stream Int
bound (value :: xs) with (divides value 12)
  bound (((12 * div) + rem) :: xs) | (DivBy prf) = rem + 1 :: bound xs
  
inputArith : Int -> Stream Int
inputArith seed = bound (randoms seed)

data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

data Ever = More (Lazy Ever)

partial
forever : Ever
forever = More forever

run : Ever -> InfIO -> IO ()
run (More next) (Do m cont) = 
  do x <- m
     run next (cont x)

quiz : Int -> Stream Int -> InfIO
quiz scores (num1 :: num2 :: nums) = 
  Do (do putStrLn ("Scores: " ++ show scores)
         putStr (show num1 ++ " * " ++ show num2 ++ "? ")
         answer <- getLine
         let scores1 = if cast answer == num1 * num2 
                       then scores + 1 
                       else scores 
         pure scores1)
     (\scores => quiz scores nums)

partial
main : IO ()
main = run forever (quiz 0 $ inputArith 12345)
