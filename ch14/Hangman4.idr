module Main

import Data.Vect

%default total

data Forever = More Forever

data GameState : Type where
  NotRunning : GameState
  Running : Nat -> Nat -> GameState

letters : String -> List Char
letters = nub . map toUpper . unpack

data CheckResult = GuessCorrect | GuessIncorrect

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
  NewGame : (word : String) -> (guesses : Nat) -> GameCmd () NotRunning (const (Running guesses (length $ letters word)))
  Won : GameCmd () (Running (S guesses) Z) (const NotRunning)
  Lost : GameCmd () (Running Z (S letters)) (const NotRunning)
  
  ShowState : GameCmd () st (const st)
  Message : String -> GameCmd () st (const st)
  ReadGuess : GameCmd Char (Running (S guesses) (S letters)) (const (Running (S guesses) (S letters)))
  CheckGuess : Char -> GameCmd CheckResult (Running (S guesses) (S letters))
                                           (\res => case res of
                                                      GuessCorrect => Running (S guesses) letters
                                                      GuessIncorrect => Running guesses (S letters))
  Pure : (res : ty) -> GameCmd ty (state_fn res) state_fn
  (>>=) : GameCmd a state1 state2_fn -> ((res : a) -> GameCmd b (state2_fn res) state3_fn) -> GameCmd b state1 state3_fn

namespace GameLoop
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    (>>=) : GameCmd a state1 state2_fn -> 
            ((res : a) -> Inf (GameLoop b (state2_fn res) state3_fn)) ->
            GameLoop b state1 state3_fn
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
          (S k) => do Message "Wrong, sorry"
                      gameLoop
  case letters of
    Z => do Won
            ShowState
            Exit
    (S k) => do Message "Correct"
                gameLoop

hangman : GameLoop () NotRunning (const NotRunning)
hangman = do NewGame "testing" 6
             gameLoop

data Game : GameState -> Type where
  NotStarted : Game NotRunning
  InProgress : (word : String) -> (guesses : Nat) -> (missing : Vect letters Char) -> Game (Running guesses letters)
  GameWon : String -> Game NotRunning
  GameLost : String -> Game NotRunning
  
data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
  OK : (res : ty) -> Game (state_fn res) -> GameResult ty state_fn

ok : (res : ty) -> Game (state_fn res) -> IO (GameResult ty state_fn)
ok res st = pure (OK res st)

Show (Game st) where
  show NotStarted = "this game is not started"
  show (InProgress word guesses missing) =
    "\n" ++ (pack $ map hideMissing $ unpack word) ++
    "\nGuesses: " ++ show guesses ++ "\n"
    where
      hideMissing : Char -> Char
      hideMissing c = if toUpper c `elem` missing
                      then '-'
                      else c
  show (GameWon x) = "Player has won the game."
  show (GameLost x) = "Player has lost the game. Word was " ++ x

runCmd : Forever -> Game instate -> GameCmd ty instate state_fn -> IO (GameResult ty state_fn)
runCmd _ inst (NewGame word guesses) = ok () (InProgress word guesses (fromList $ letters word))
runCmd _ (InProgress word (S guesses) missing) Won = ok () (GameWon word)
runCmd _ (InProgress word Z missing) Lost = ok () (GameLost word)
runCmd _ inst ShowState = do printLn inst; ok () inst
runCmd _ inst (Message msg) = do putStrLn msg; ok () inst
runCmd (More frvr) inst ReadGuess = do
  putStr "Guess: "
  s <- getLine
  case unpack s of
    [c] => if isAlpha c
           then ok c inst
           else do putStrLn "Invalid guess. Enter a letter."
                   runCmd frvr inst ReadGuess
    _   => do putStrLn "Invalid guess. Enter one character."
              runCmd frvr inst ReadGuess
runCmd _ (InProgress word (S guesses) missing) (CheckGuess c) = 
  case isElem (toUpper c) missing of
    (Yes prf) => ok GuessCorrect (InProgress word _ (dropElem missing prf))
    (No contra) => ok GuessIncorrect (InProgress word _ missing)
runCmd _ inst (Pure res) = ok res inst
runCmd (More frvr) inst (cmd >>= next) = do (OK res' st') <- runCmd frvr inst cmd
                                            runCmd frvr st' (next res')
run : Forever -> Game instate -> GameLoop () instate state_fn -> IO (GameResult () state_fn)
run (More frvr) inst (cmd >>= next) = do (OK res' st') <- runCmd frvr inst cmd
                                         run frvr st' (next res')
run _ inst Exit = ok () inst

partial
forever : Forever
forever = More forever

partial
main : IO ()
main = do ok <- run forever NotStarted hangman 
          pure ()
