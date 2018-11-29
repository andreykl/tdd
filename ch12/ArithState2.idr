module Main

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

runCommand : Command a -> IO a
runCommand GetRandom = pure 3
runCommand GetGameState = pure ?state
runCommand (PutGameState x) = ?hole
runCommand (PutStr x) = putStr x
runCommand (PutStrLn x) = putStrLn x
runCommand GetStr = getLine
runCommand (Pure x) = pure x
runCommand (Bind x f) = do a1 <- runCommand x
                           runCommand $ f a1

run : Forever -> ConsoleIO a -> IO a
run _ (Quit x) = pure x
run (More more) (Do ca next) = (runCommand ca) >>= (\a => run more (next a))

data Input : Type where
  QuitCmd : Input
  Answer : Int -> Input

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

  readInput : String -> Command Input
  readInput s = ?readInput_rhs

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
