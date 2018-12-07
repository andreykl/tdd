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
  
  ShowState : GameCmd () state (const state)
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
             Z => do Lost
                     ShowState
                     Exit
             (S k) => do Message "Incorrect..."
                         gameLoop 
  case letters of
    Z => do Won
            ShowState
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
    = --"\n(missing: " ++ show missing ++ ")" ++
      "\n" ++ pack (map hideMissing $ unpack word) ++
      "\n" ++ show guesses ++ " guesses left"
    where
      hideMissing : Char -> Char
      hideMissing x = if toUpper x `elem` missing then '-' else x

data Forever = More Forever

partial 
forever : Forever
forever = More forever

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
  OK : (res : ty) -> Game (outstate_fn res) -> GameResult ty outstate_fn

ok : (res : ty) -> Game (outstate_fn res) -> IO (GameResult ty outstate_fn)
ok res g = pure $ OK res g

runCmd : Forever -> Game instate -> GameCmd ty instate outstate_fn -> IO (GameResult ty outstate_fn)
runCmd frvr st (NewGame word guesses) = ok () (InProgress word guesses (fromList $ letters word))
runCmd frvr (InProgress word (S guesses) missing) (Guess c) =
  case isElem c missing of
    (Yes prf) => ok Correct (InProgress word (S guesses) (dropElem missing prf))
    (No contra) => ok Incorrect (InProgress word guesses missing)  
runCmd frvr (InProgress word _ _) Won = ok () (GameWin word)
runCmd frvr (InProgress word _ _) Lost = ok () (GameLost word)
runCmd frvr st ShowState = do printLn st; ok () st
runCmd frvr st (Message str) = do putStrLn str; ok () st
runCmd (More frvr) st ReadGuess = 
  do putStr "Guess: "
     guess <- getLine
     case map toUpper $ unpack guess of
       [c] => if isAlpha c
                 then ok c st
                 else do putStrLn "Incorrect guess: please enter charachter from alphabet"
                         runCmd frvr st ReadGuess
       _   => do putStrLn "Incorrect guess: please enter one character"
                 runCmd frvr st ReadGuess
runCmd frvr st (Pure res) = ok res st
runCmd (More frvr) st (x >>= f) = do (OK res' st') <- runCmd frvr st x
                                     runCmd frvr st' (f res')

run : Forever -> Game instate -> GameLoop ty instate outstate_fn -> IO (GameResult ty outstate_fn)
run (More frvr) st (loop >>= next) = do (OK res newSt) <- runCmd frvr st loop
                                        run frvr newSt (next res)
run (More frvr) st Exit = ok () st

partial
main : IO ()
main = do run forever GameStart hangman
          pure ()
