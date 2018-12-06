module Main

import Data.Vect

%default total

data GameState : Type where
  NotRunning : GameState
  Running : (guesses : Nat) -> (letters : Nat) -> GameState
  
data GuessResult = Correct | Incorrect

letters : String -> List Char
letters str = nub (map toUpper $ unpack str)

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
  NewGame : (word : String) -> (guesses : Nat) -> GameCmd () NotRunning (const $ Running guesses (length $ letters word))
  Guess : (c : Char) -> GameCmd GuessResult (Running (S guesses) (S letters)) 
                              (\res => case res of
                                         Correct => Running (S guesses) letters
                                         Incorrect => Running guesses (S letters))
  Won : GameCmd () (Running (S guesses) Z) (const NotRunning)
  Lost : GameCmd () (Running Z (S letters)) (const NotRunning)
  
  ShowState : GameCmd String state (const state)
  Message : String -> GameCmd () state (const state)
  ReadGuess : GameCmd Char state (const state)

  Pure : (res : ty) -> GameCmd ty (state_fn res) state_fn
  (>>=) : GameCmd a state1 state2_fn -> ((res : a) -> GameCmd b (state2_fn res) state3_fn) -> GameCmd b state1 state3_fn

namespace Loop
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    (>>=) : GameCmd a state1 state2_fn -> ((res : a) -> Inf (GameLoop b (state2_fn res) state3_fn)) -> GameLoop b state1 state3_fn
    Exit : GameLoop () NotRunning (const NotRunning)

gameLoop : GameLoop () (Running (S guesses) (S letters)) (const NotRunning)
gameLoop {guesses} {letters} = do
  ShowState
  g <- ReadGuess
  Correct <- Guess g 
    | Incorrect => 
        do case guesses of
             Z => do ShowState
                     Message "Game is lost. Try again."
                     Lost
                     Exit
             (S k) => do Message "Incorrect"
                         gameLoop 
  case letters of
    Z => do ShowState
            Won
            Exit
    (S k) => do Message "Right!"
                gameLoop
  
hangman : GameLoop () NotRunning (const NotRunning)
hangman = do NewGame "testing" 6
             gameLoop

data Game : GameState -> Type where
  GameStart : Game NotRunning
  GameWin : (word : String) -> Game NotRunning
  GameLost : (word : String) -> Game NotRunning
  InProgress : (word : String) -> (guesses : Nat) -> (missing : Vect letters Char) -> Game (Running guesses letters)

Show (Game g) where
  show GameStart = "Starting"
  show (GameWin word) = "Player has won, word is " ++ word
  show (GameLost word) = "Player has lost, word is " ++ word
  show (InProgress word guesses missing)
    = "\n" ++ pack (map hideMissing $ unpack word) ++
      "\n" ++ show guesses ++ " guesses left"
    where
      hideMissing : Char -> Char
      hideMissing x = if x `elem` missing then '-' else x

data Forever = More Forever

partial 
forever : Forever
forever = More forever

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
  OK : (res : ty) -> Game (outstate_fn res) -> GameResult ty outstate_fn

run : Forever -> Game instate -> GameLoop ty instate outstate_fn -> IO (GameResult ty outstate_fn)
