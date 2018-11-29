module Main

import Data.Primitives.Views

%default total

record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int

initState : GameState
initState = MkGameState (MkScore 0 0) 12

Show GameState where
  show st = show (correct $ score st) ++ "/" ++
            show (attempted $ score st) ++ "\n" ++
            "Difficulty: " ++ show (difficulty st)

addWrong : GameState -> GameState
addWrong = record { score->attempted $= (+1) }

addCorrect : GameState -> GameState
addCorrect = record { score->attempted $= (+1), score->correct $= (+1) }

data Command : Type -> Type where
  PutStr : String -> Command ()
  PutStrLn : String -> Command ()
  GetStr : Command String
  
  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()
  
  Pure : a -> Command a
  Bind : Command a -> (a -> Command b) -> Command b

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleIO
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

Functor Command where
  map f (Bind ca1 k) = (Bind ca1 (\a1 => Bind (k a1) (\a => Pure $ f a)))
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

f2vsg : {rnds : Stream Int, st : GameState} -> a1 -> (a1, Stream Int, GameState)
f2vsg {rnds} {st} x = (x, rnds, st)

limit : Int -> Int -> Int
limit r mx with (divides r mx)
  limit r 0 | DivByZero = 1
  limit ((mx * div) + rem) mx | (DivBy prf) = abs rem + 1


runCommand : (rnds : Stream Int) -> (st : GameState) -> Command a -> IO (a, Stream Int, GameState)
runCommand rnds st (PutStr x) = map (f2vsg {rnds} {st}) $ putStr x
runCommand rnds st (PutStrLn x) = map (f2vsg {rnds} {st}) $ putStrLn x
runCommand rnds st GetStr = map (f2vsg {rnds} {st}) $ getLine
runCommand (x::rnds) st GetRandom = map (f2vsg {rnds} {st}) $ pure (limit x (difficulty st))
runCommand rnds st GetGameState = map (f2vsg {rnds} {st}) $ pure st
runCommand rnds st (PutGameState x) = pure ((), rnds, x)
runCommand rnds st (Pure x) = map (f2vsg {rnds} {st}) $ pure x
runCommand rnds st (Bind x f) = do (a1, rnds1, state1) <- runCommand rnds st x
                                   runCommand rnds1 state1 $ f a1

run : Forever -> Stream Int -> GameState -> ConsoleIO a -> IO (a, Stream Int, GameState)
run _ rnds st (Quit x) = pure (x, rnds, st)
run (More more) rnds st (Do ca next) = (runCommand rnds st ca) >>= (\(a1, rnds1, state1) => run more rnds1 state1 (next a1))

randoms : Int -> Stream Int
randoms seed = let seed' = seed * 1664525 + 1013904223 in (seed' `shiftR` 2) :: randoms seed'

data Input : Type where
  QuitCmd : Input
  Answer : Int -> Input
  
readInput : String -> Command Input
readInput str =
  do PutStr str
     ans <- GetStr
     if ans == "quit" then Pure QuitCmd else Pure $ Answer (cast ans)

mutual
  correct : ConsoleIO GameState
  correct =
    do PutStrLn "Correct!"
       st <- GetGameState
       PutGameState (addCorrect st)
       quiz

  wrong : Int -> ConsoleIO GameState
  wrong v =
    do PutStrLn $ "No.. correct answer is " ++ show v
       st <- GetGameState
       PutGameState (addWrong st)
       quiz

  quiz : ConsoleIO GameState
  quiz = do a <- GetRandom
            b <- GetRandom
            st <- GetGameState
            PutStrLn (show st)
            
            input <- readInput (show a ++ " * " ++ show b ++ " = ? ")
            case input of
              Answer answer => if answer == a * b
                                  then correct
                                  else wrong (a * b)
              QuitCmd => Quit st

partial
main : IO ()
main =
  do (_, _, st) <- run forever (randoms 25) initState quiz
     putStrLn $ "Final score: " ++ show st
