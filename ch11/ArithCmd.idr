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

data Forever = More (Lazy Forever)

partial
forever : Forever
forever = More forever

data Input = QuitCmd | AnswerCmd Int

data Command : Type -> Type where
  PutStr : String -> Command ()
  PutStrLn : String -> Command ()
  GetString : Command String
  
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b
  
-- Functor Command where
--   map f (PutStr x) = PutStr (f x)
--   map f (PutStrLn x) = PutStrLn (f x)
--   map f GetString = 
--   map f (Pure x) = Pure (f x)
--   -- map f (Bind x g) = 
  
  
data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b


namespace ConsoleIO
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind
  
readInput : (prompt : String) -> Command Input
readInput prompt = 
  do PutStr prompt
     input <- GetString
     if toLower input == "quit" 
       then Pure QuitCmd 
       else Pure $ AnswerCmd (cast input)

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand (PutStrLn x) = putStrLn x
runCommand GetString = getLine
runCommand (Pure a) = pure a
runCommand (Bind c k) = 
  do res <- runCommand c 
     runCommand (k res)

run : Forever -> ConsoleIO a -> IO a
run _ (Quit y) = pure y
run (More next) (Do c cont) = 
  do a <- runCommand c
     run next (cont a)
{-
data RunIO : Type -> Type where
  Quit : a -> RunIO a
  Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b


run : Forever -> RunIO a -> IO a
run _ (Quit y) = pure y
run (More next) (Do m cont) =
  do a <- m
     run next (cont a)
-}


quit : ConsoleIO ()
quit = do PutStrLn "bye-bye"
          Quit ()
mutual
  correct : Int -> Int -> Stream Int -> ConsoleIO ()
  correct tryes scores nums = do PutStrLn "Right!"
                                 quiz (tryes + 1) (scores + 1) nums
  
  wrong : Int -> Int -> Int -> Stream Int -> ConsoleIO ()
  wrong tryes scores answer nums = do PutStrLn $ "No.. correct answer: " ++ show answer
                                      quiz (tryes + 1) scores nums
    
  quiz : Int -> Int -> Stream Int -> ConsoleIO ()
  quiz tryes scores (num1 :: num2 :: nums) = 
    do PutStrLn ("Tryes/Scores: " ++ show tryes ++ "/" ++ show scores)
       input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
       case input of
         QuitCmd => quit
         (AnswerCmd answer) => 
           do -- PutStrLn $ "answer read : " ++ show answer
              let rightAnswer = num1 * num2
              if answer == rightAnswer
              then
                correct tryes scores nums
              else
                wrong tryes scores rightAnswer nums

partial
main : IO ()
main = run forever (quiz 0 0 $ inputArith 12345)
