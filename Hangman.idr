module Main

import Data.Vect

data GameState : Nat -> Nat -> Type where
  MkData : (gss : Nat) -> (Vect msgss Char) -> GameState gss msgss

data FinishedGame : Type where
  Won : GameState (S gss) Z -> FinishedGame
  Lost : GameState Z (S mss) -> FinishedGame
  
data NonEmpty : String -> Type where
  NEString : (x : String) -> {auto prf: not (x == "") = True} -> NonEmpty x

emptyIsEmpty : NonEmpty "" -> Void
emptyIsEmpty (NEString "" {prf=Refl}) impossible

isNonEmpty : (s: String) -> Dec (NonEmpty s)
isNonEmpty "" = No emptyIsEmpty
isNonEmpty s = Yes (NEString s {prf=?holeNEString})

letters : {s : String} -> NonEmpty s -> (n ** Vect (S n) Char)
letters (NEString s {prf}) = 
  let
    xs = nub (unpack s)
    (S n) = length xs
    v = the (Vect (S n) Char) (believe_me (fromList xs))
  in (_ ** v)
  

-- data ValidGame : Type where
--   VGame : (word : String) -> (state : GameState (S g) (S m)) -> ValidGame

-- newGame : (word : String) ->
--           (guesses : Nat) ->
--           {auto neword : NonEmpty word} ->
--           {auto prf : LTE 1 guesses} ->          
--           Type
-- newGame word guesses {neword} = 
--   let 
--     (mss ** mssg) = letters neword 
--     (S gss) = guesses
--     st = MkData (S gss) mssg
--   in (VGame word st)

data ValidGuess : List Char -> Type where
  Letter : (c : Char) -> ValidGuess [c]

readValidGuess : IO (c ** ValidGuess [c])
readValidGuess = do putStr "Please enter a gueess (a char): "
                    line <- getLine
                    case unpack (trim line) of
                      [c] => pure (c ** (Letter c))
                      cs  => do putStrLn "Invalid guess! You need enter only one charachter."
                                readValidGuess

processGuess : ValidGuess cs -> (GameState (S gss) (S mss)) -> Either (GameState gss (S mss)) (GameState (S gss) mss)
processGuess (Letter c) (MkData (S gss) (x :: xs)) with (isElem c (x :: xs))
  processGuess (Letter c) (MkData (S gss) (x :: xs)) | (Yes prf) = Right (MkData (S gss) (dropElem (x :: xs) prf))
  processGuess (Letter c) (MkData (S gss) (x :: xs)) | (No _) = Left (MkData gss (x :: xs))


game : GameState (S gss) (S mss) -> IO FinishedGame
game gamestate = 
  do (c ** prf) <- readValidGuess
     case processGuess prf gamestate of
        (Left s@(MkData Z (x :: mss))) => pure (Lost s)
        (Left s@(MkData (S k) (x :: mss))) => 
          do putStrLn ("no such letter, guesses left: " ++ show (S k))
             game s
        (Right s@(MkData (S gss) [])) => pure (Won s)
        (Right s@(MkData {msgss=S len} (S gss) (x :: xs))) => 
          do putStrLn ("good shoot! letters left: " ++ show (S len))
             game s
 
main : IO ()
main = 
  do let nes = NEString "hello"
     let (_ ** lts) = letters nes
     case !(game (MkData 6 lts)) of
       (Won x) => putStrLn "Cool! You won!"
       (Lost x) => putStrLn "Oh, you loose.."
