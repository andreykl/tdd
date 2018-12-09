module Main

import Data.Vect

data Forever = More Forever

data GameState : Type where
  NotRunning : GameState
  Running : Nat -> Nat -> GameState

data CheckResult = GuessCorrect | GuessIncorrect

letters : String -> List Char
letters = nub . map toUpper . unpack

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
  NewGame : (word : String) -> (guesses : Nat) -> GameCmd () NotRunning 
                                                  (const (Running guesses (length $ letters word)))
  Won : GameCmd () (Running (S guesses) Z) (const NotRunning)
  Lost : GameCmd () (Running Z (S letters)) (const NotRunning)
  CheckGuess : Char -> GameCmd CheckResult (Running (S guesses) (S letters))
                               (\res => case res of
                                          GuessCorrect => Running (S guesses) letters
                                          GuessIncorrect => Running guesses (S letters))
  ReadGuess : GameCmd Char (Running (S guesses) (S letters)) (const (Running (S guesses) (S letters)))
  Message : String -> GameCmd () st (const st)
  ShowState : GameCmd () st (const st)
  
  Pure : (res : ty) -> GameCmd ty (state_fn res) state_fn
  (>>=) : GameCmd a state1 state2_fn -> ((res : a) -> GameCmd b (state2_fn res) state3_fn) -> GameCmd b state1 state3_fn
 
namespace GameLoop
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    (>>=) : GameCmd a state1 state2_fn -> 
            Inf ((res : a) -> GameLoop b (state2_fn res) state3_fn) ->
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
        S k => do Message "Incorrect guess"
                  gameLoop
  case letters of
    Z => do Won
            ShowState
            Exit
    S k => do Message "Correct"
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

Show (Game g) where
  show NotStarted = "game is not started"
  show (InProgress word guesses missing) = 
    "\nGuesses: " ++ show guesses ++
    "\n" ++ (pack $ map hideMissing (unpack word))
    where
      hideMissing : Char -> Char
      hideMissing c = if toUpper c `elem` missing
                      then '-'
                      else c
  show (GameWon x) = "Player won. Word is " ++ x
  show (GameLost x) = "Player lost the game. Word is " ++ x

ok : (res : ty) -> Game (state_fn res) -> IO (GameResult ty state_fn)
ok res gst = pure $ OK res gst

runCmd : Forever -> Game instate -> GameCmd a instate state_fn -> IO (GameResult a state_fn)
runCmd _ inst (NewGame word guesses) = ok () (InProgress word guesses (fromList $ letters word))
runCmd _ (InProgress word (S guesses) missing) Won = ok () (GameWon word)
runCmd _ (InProgress word Z missing) Lost = ok () (GameLost word)
runCmd _ (InProgress word (S guesses) missing) (CheckGuess x) = do
  case isElem (toUpper x) missing of
    (Yes prf) => ok GuessCorrect (InProgress word _ (dropElem missing prf))
    (No contra) => ok GuessIncorrect (InProgress word _ missing)
runCmd (More frvr) inst ReadGuess = do putStr "Guess: "
                                       s <- getLine
                                       case unpack s of
                                         [c] => if isAlpha c
                                                then ok c inst
                                                else do putStrLn "invalid guess. please enter a letter"
                                                        runCmd frvr inst ReadGuess
                                         _   => do putStrLn "invalid guess. please enter exactly one char"
                                                   runCmd frvr inst ReadGuess
runCmd _ inst (Message x) = do putStrLn x; ok () inst
runCmd _ inst ShowState = do printLn inst; ok () inst
runCmd _ inst (Pure res) = ok res inst
runCmd (More frvr) inst (cmd >>= next) = do (OK res' st') <- runCmd frvr inst cmd
                                            runCmd frvr st' (next res')

run : Forever -> Game instate -> GameLoop () instate state_fn -> IO (GameResult () state_fn)
run (More frvr) instate (cmd >>= next) = do (OK res' st') <- runCmd frvr instate cmd
                                            run frvr st' (next res')
run (More frvr) instate Exit = ok () NotStarted

partial
forever : Forever
forever = More forever

partial
main : IO ()
main = do ok <- run forever NotStarted hangman
          pure ()
