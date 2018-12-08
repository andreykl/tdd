module Main

import Data.Vect

data Forever = More Forever

data GameState : Type where
  NotRunning : GameState
  Running : (guesses : Nat) -> (letters : Nat) -> GameState

cNotRunning : a -> GameState
cNotRunning = const NotRunning

letters : String -> List Char
letters = nub . map toUpper . unpack

data CheckResult = GuessCorrect | GuessIncorrect

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
  NewGame : (word : String) -> (guesses : Nat) -> GameCmd () NotRunning (const $ Running guesses (length $ letters word))
  Won : GameCmd () (Running (S guesses) Z) (const NotRunning)
  Lost : GameCmd () (Running Z (S letters)) (const NotRunning)
  
  ReadGuess : GameCmd Char (Running (S guesses) (S letters)) (const (Running (S guesses) (S letters)))
  CheckGuess : Char -> GameCmd CheckResult (Running (S guesses) (S letters))
                                           (\res => case res of
                                              GuessCorrect => Running (S guesses) letters
                                              GuessIncorrect => Running guesses (S letters))
  Message : String -> GameCmd () state (const state)
  ShowState : GameCmd () state (const state)

  Pure : (res : ty) -> GameCmd ty (state_fn res) state_fn
  (>>=) : GameCmd a state1 state2_fn -> ((res : a) -> GameCmd b (state2_fn res) state3_fn) -> GameCmd b state1 state3_fn


namespace GameLoop
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    (>>=) : GameCmd a state1 state2_fn -> ((res : a) -> Inf (GameLoop b (state2_fn res) state3_fn)) -> GameLoop b state1 state3_fn
    Exit : GameLoop () NotRunning (const NotRunning)
  
gameLoop : GameLoop () (Running (S guesses) (S letters)) (const NotRunning)
gameLoop {guesses} {letters} = do
  ShowState
  c <- ReadGuess
  GuessCorrect <- CheckGuess c
    | GuessIncorrect => 
      case guesses of
        Z => do Lost
                ShowState
                Exit
        (S k) => do Message "No..."
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
  NotStarted : Game NotRunning
  InProgress : (res : ty) -> (word : String) -> (guesses : Nat) -> (Vect letters Char) -> Game (Running guesses letters)
  GameWon : String -> Game NotRunning
  GameLost : String -> Game NotRunning  

  

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
  OK : (res : ty) -> (Game (outstate_fn res)) -> GameResult ty outstate_fn

ok : (res : ty) -> Game (outstate_fn res) -> IO (GameResult ty outstate_fn)
ok res st = pure $ OK res st

Show (Game g) where
  show NotStarted = "this game is not started"
  show (InProgress res word guesses missing) = 
      "\nguesses: " ++ show guesses ++
      "\n" ++ pack (map hideMissing $ unpack word) ++ "\n"
    where
      hideMissing : Char -> Char
      hideMissing c = if toUpper c `elem` missing then '-' else c
  show (GameWon x) = "player has won. word is " ++ x
  show (GameLost x) = "player has lost. word is " ++ x


runCmd : Forever -> (Game instate) -> GameCmd a instate state_fn -> IO (GameResult a state_fn)
runCmd _ inst (NewGame word guesses) = 
  pure (OK () (InProgress () word guesses (fromList $ letters word)))
runCmd _ (InProgress _ word _ _) Won = ok () (GameWon word)
runCmd _ (InProgress _ word _ _) Lost = ok () (GameLost word)
runCmd (More frvr) inst ReadGuess = 
  do putStr "Guess: "
     s <- getLine
     case unpack s of
       [c] => if isAlpha c
              then ok c inst
              else do putStrLn "Please enter a letter"
                      runCmd frvr inst ReadGuess
       _   => do putStrLn "Please enter one char"
                 runCmd frvr inst ReadGuess
runCmd _ (InProgress _ word (S guesses) cs) (CheckGuess c)
  = case isElem (toUpper c) cs of
      (Yes prf) => ok GuessCorrect (InProgress GuessCorrect word _ (dropElem cs prf))
      (No contra) => ok GuessIncorrect (InProgress GuessIncorrect word _ cs)
runCmd _ inst (Message msg) = do putStrLn msg; ok () inst
runCmd _ inst ShowState = do printLn inst; ok () inst
runCmd _ inst (Pure res) = ok res inst
runCmd (More frvr) inst (cmd >>= next) = 
  do (OK res' st') <- runCmd frvr inst cmd
     runCmd frvr st' (next res')

run : Forever -> (Game instate) -> GameLoop a instate state_fn -> IO (GameResult a state_fn)
run (More frvr) inst (cmd >>= next) = do (OK res' st') <- runCmd frvr inst cmd
                                         run frvr st' (next res')
run frvr inst Exit = ok () NotStarted

partial
forever : Forever
forever = More forever

partial
main : IO ()
main = do (OK _ _) <- run forever NotStarted hangman
          pure ()
          
