module Main

import Data.Primitives.Views

%default total

record Score where
  constructor MkScore
  attempted : Int
  correct : Int

record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int

data Command : Type -> Type where
  GetStr : Command String
  PutStr : String -> Command ()
  PutStrLn : String -> Command ()
  
  GetRandom : Command Int
  
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()
  
  Pure : a -> Command a
  Bind : Command a -> (a -> Command b) -> Command b

Functor Command where
  map f ca = Bind ca (\a => Pure $ f a)

Applicative Command where
  pure = Pure
  (<*>) cf ca = Bind cf (\f => Bind ca (\a => Pure $ f a))

Monad Command where
  (>>=) = Bind

data Forever = More Forever

partial
forever : Forever
forever = More forever

data ConsoleIO : Type -> Type where
  QuitCmd : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleIO
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

limit : Int -> Int -> Int
limit r mx with (divides r mx)
  limit r 0 | DivByZero = 1
  limit ((mx * div) + rem) mx | (DivBy prf) = abs rem + 1


runCommand : Stream Int -> GameState -> Command a -> IO (a, Stream Int, GameState)
runCommand xs st GetStr = map (\a => (a, xs, st)) getLine
runCommand xs st (PutStr s) = map (\a => (a, xs, st)) $ putStr s
runCommand xs st (PutStrLn s) = map (\a => (a, xs, st)) $ putStrLn s
runCommand (x::xs) st GetRandom = pure (limit x (difficulty st), xs, st)
runCommand xs st GetGameState = pure (st, xs, st)
runCommand xs st (PutGameState st') = pure ((), xs, st')
runCommand xs st (Pure x) = pure (x, xs, st)
runCommand xs st (Bind ca f) = do (a', xs', st') <- runCommand xs st ca
                                  runCommand xs' st' (f a')

run : Forever -> Stream Int -> GameState -> ConsoleIO a -> IO (a, Stream Int, GameState)
run _ xs st (QuitCmd a) = pure (a, xs, st)
run (More frvr) xs st (Do ca next) = do (a', xs', st') <- runCommand xs st ca
                                        run frvr xs' st' (next a')

data Input : Type where
  Quit : Input
  Answer : Int -> Input

readInput : String -> Command Input
readInput prompt =
  do PutStr prompt
     a <- GetStr
     if a == "quit" then Pure Quit else Pure (Answer $ cast a)

Show GameState where
  show st = (show (correct (score st))) ++ "/" ++ (show (attempted (score st))) ++ "\nDifficulty: " ++ show (difficulty st)

randoms : Int -> Stream Int
randoms seed = let seed' = 1633494 * seed + 8377621234 in (seed' `shiftR` 2) :: randoms seed'

initState : GameState
initState = MkGameState (MkScore 0 0) 12

quiz : ConsoleIO GameState
quiz =
  do a <- GetRandom
     b <- GetRandom
     st <- GetGameState
     
     PutStrLn $ "Current state: " ++ show st
     ans <- readInput (show a ++ " * " ++ show b ++ " = ? ")
     case ans of
       Quit => QuitCmd st
       (Answer v) => if a * b == v 
                        then 
                          do PutStrLn "Correct!"
                             PutGameState (record { score->attempted $= (+1), score->correct $= (+1) } st)
                             quiz
                        else 
                          do PutStrLn $ "Wrong. Correct answer is " ++ show (a * b)
                             PutGameState (record { score->attempted $= (+1) } st)
                             quiz

partial 
main : IO ()
main =
  do (_, _, st) <- run forever (randoms 255) initState quiz
     putStrLn $ "Final score: " ++ show st
