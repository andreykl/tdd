module Main

import Data.Primitives.Views

import public Lightyear.Core
import public Lightyear.Char
import public Lightyear.Strings
import public Lightyear.Combinators

%default total

data Difficulty = Easy | Medium | Hard

data Forever = More Forever

partial
forever : Forever
forever = More forever

record Score where
  constructor MkScore
  corrects : Int
  attempts : Int

record GameState where
  constructor MkGame
  score : Score
  difficulty : Difficulty

data Command : Type -> Type where
  PutStr : String -> Command ()
  PutStrLn : String -> Command ()
  GetLine : Command String

  GetRandom : Command Int
  PutGameState : GameState -> Command ()
  GetGameState : Command GameState

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

data Input : Type where
  QuitCmd : Input
  AnswerCmd : Int -> Input
  DfcltyCmd : Maybe Difficulty -> Input

Show Difficulty where
  show Easy = "easy"
  show Medium = "medium"
  show Hard = "hard"

Functor Command where
  -- map func (Bind x f) = Bind (Bind x f) (\a => Pure (func a))
  map func c = Bind c (\v => Pure (func v))
  

Applicative Command where
  pure = Pure
  (<*>) f' a' = Bind f' (\f => Bind a' (\a => Pure (f a)))

Monad Command where
  (>>=) = Bind

namespace ConsoleIO
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

randoms : Int -> Stream Int
randoms seed = let seed' = 1668424 * seed + 63332199 in (seed' `shiftR` 2) :: randoms seed'

bound : Stream Int -> Stream Int
bound (x :: xs) with (divides x 12)
  bound (((12 * div) + rem) :: xs) | (DivBy prf) = rem + 1 :: bound xs


arithInput : Stream Int
arithInput = bound $ randoms 123

dfcltyToMax : Difficulty -> Int
dfcltyToMax Easy = 7
dfcltyToMax Medium = 12
dfcltyToMax Hard = 16


getRandom : Int -> Int -> Int
getRandom x max with (divides x max)
  getRandom x 0 | DivByZero = 1
  getRandom ((max * div) + rem) max | (DivBy prf) = rem + 1


runCommand : Stream Int -> GameState -> Command a -> IO (a, Stream Int, GameState)
runCommand xs st (PutStr x) = do putStr x; pure ((), xs, st)
runCommand xs st (PutStrLn x) = do putStrLn x; pure ((), xs, st)
runCommand xs st GetLine = do line <- getLine; pure (line, xs, st)
runCommand (x::xs) st GetRandom = pure (getRandom x (dfcltyToMax $ difficulty st), xs, st)
runCommand xs st (PutGameState st') = pure ((), xs, st')
runCommand xs st GetGameState = pure (st, xs, st)
runCommand xs st (Pure x) = pure (x, xs, st)
runCommand xs st (Bind c f) = do (c', xs', st') <- runCommand xs st c
                                 runCommand xs' st' (f c')

run : Forever -> GameState -> Stream Int -> ConsoleIO a -> IO a
run frvr st xs (Quit y) = pure y
run (More nxt) st xs (Do cmd f) = do (a1, xs1, st1) <- runCommand xs st cmd
                                     run nxt st1 xs1 (f a1)

partial
pcquit : Parser Input
pcquit = do lexeme $ string "quit"
            pure QuitCmd

partial
pdlevel : Parser Difficulty
pdlevel = (do lexeme $ string "hard"
              pure Hard) 
          <|>
          (do lexeme $ string "normal"
              pure Medium) 
          <|>
          (do lexeme $ string "easy"
              pure Easy)

partial
pcdifficulty : Parser Input
pcdifficulty = do lexeme $ string "difficulty"
                  (do level <- pdlevel
                      pure (DfcltyCmd $ Just level)) <|> pure (DfcltyCmd Nothing)

partial
pcanswer : Parser Input
pcanswer = do v <- lexeme integer
              pure (AnswerCmd v)

-- partial
-- pfilename : Parser String
-- pfilename = map pack $ some $ satisfy (/= ' ')

-- partial           
-- pccopy : Parser Input
-- pccopy = do lexeme $ string "copy"
--             source <- pfilename
--             spaces
--             destination <- pfilename
--             pure (CCopy source destination)

partial
pcommand : Parser Input
pcommand = pcquit <|> pcdifficulty <|> pcanswer

partial
readInput : String -> Command (Either String Input)
readInput prompt =
  do PutStr prompt
     commstr <- GetLine
     case parse pcommand commstr of
       (Left l) => Pure (Left $ "Unrecognized command: " ++ commstr)
       (Right r) => Pure (Right r)
       
addCorrect : GameState -> GameState
addCorrect st = record { score->attempts $= (+1), score->corrects $= (+1) } st

addWrong : GameState -> GameState
addWrong st = record { score->attempts $= (+1) } st

updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = GetGameState >>= (\st => PutGameState (f st))

partial
quiz : ConsoleIO GameState
quiz = do
  st <- GetGameState
  num1 <- GetRandom
  num2 <- GetRandom
  input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
  case input of
    (Left l) => do PutStrLn l
                   quiz
    (Right QuitCmd) => Quit st
    (Right (AnswerCmd x)) => if x == num1 * num2 
                             then
                               do PutStrLn "Right!"
                                  updateGameState addCorrect
                                  quiz
                             else
                               do PutStrLn ("No.. answer is " ++ show (num1 * num2) ++ ".")
                                  updateGameState addWrong
                                  quiz
    (Right (DfcltyCmd Nothing)) => do PutStrLn ("Current difficulty level: " ++ show (difficulty st))
                                      quiz
    (Right (DfcltyCmd (Just d))) => do PutGameState (record { difficulty = d } st)
                                       quiz

record Votes where
  constructor MkVotes
  upvotes : Integer
  downvotes : Integer

record Article where
  constructor MkArticle
  title : String
  url : String
  score : Votes

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

badSite : Article
badSite = MkArticle "Bad Page" "http://example.com/bad" (MkVotes 5 47)

goodSite : Article
goodSite = MkArticle "Good Page" "http://example.com/good" (MkVotes 101 7)

getScore : Article -> Integer
getScore a = let sc = score a in upvotes sc - downvotes sc

addUpvote : Article -> Article
addUpvote a = record { score->upvotes $= (+1) } a

addDownvote : Article -> Article
addDownvote a = record { score->downvotes $= (+1) } a

partial
main : IO ()
main = do st <- run forever (MkGame (MkScore 0 0) Easy) arithInput quiz
          putStrLn ("Your final scores: " ++ show (corrects (score st)) ++ "/" ++ show (attempts (score st)))

-- Local Variables:
-- idris-load-packages: ("lightyear")
-- End:
