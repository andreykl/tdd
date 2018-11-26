module Main

import Data.Primitives.Views

quiz : Stream Integer -> Integer -> IO ()
quiz (num1 :: num2 :: nums) score = 
  do putStrLn $ "Очки: " ++ show score
     putStr $ "Сколько будет " ++ show num1 ++ " * " ++ show num2 ++ "? "
     answer <- getLine
     if cast answer == num1 * num2
     then
       do putStrLn "Верно!"
          quiz nums (score + 1)
     else
       do putStrLn $ "Неверно! Правильный ответ: " ++ show (num1 * num2)
          quiz nums score

randoms : Int -> Stream Integer
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   cast (seed `shiftR` 2) :: randoms seed'

                
arithInputs : Stream Integer -> Stream Integer
arithInputs xs = map bound xs where
  bound : Integer -> Integer
  bound x with (divides x 12)
    bound ((12 * div) + rem) | (DivBy prf) = rem + 1


main : IO ()
main = quiz (arithInputs $ randoms 12345) 0
