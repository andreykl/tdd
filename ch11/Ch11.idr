module Ch11

import Data.Primitives.Views

data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

%name InfList xs, ys, zs

Functor InfList where
  map f (x :: xs) = f x :: map f xs

countFrom : Integer -> InfList Integer
countFrom x = x :: Delay (countFrom $ x + 1)

getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z xs = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs

every_other : Stream a -> Stream a
every_other (_ :: (x :: xs)) = x :: every_other xs


data Face = Tails | Heads

getFace : Int -> Face
getFace x with (divides x 2)
  getFace ((2 * div) + rem) | (DivBy prf) = if rem == 0 then Heads else Tails


coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips count xs = map getFace $ take count xs

square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx = let approx' = (approx + number / approx) / 2 in 
                                       approx' :: square_root_approx number approx'

square_root_bound : (max : Nat) -> (number : Double) -> (bound : Double) ->
                    (approxs : Stream Double) -> Double
square_root_bound Z number bound (value :: xs) = value
square_root_bound (S k) number bound (value :: xs) = 
  if abs (number - value * value) <= bound then value else square_root_bound k number bound xs

square_root : (number : Double) -> Double
square_root number = square_root_bound 100 number 0.00000000001
                                 (square_root_approx number number)

data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

printLoop : String -> InfIO
printLoop msg = Do (putStrLn msg)
                   (\_ => printLoop msg)

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

run : Fuel -> InfIO -> IO ()
run (More x) (Do m f) =
  do a <- m
     run x (f a)
run Dry _ = putStrLn "run out of fuel" 

totalREPL : (prompt : String) -> (action : String -> String) -> InfIO
totalREPL prompt action = Do (do putStr prompt
                                 res <- getLine
                                 putStrLn $ action res) (\_ => totalREPL prompt action)

