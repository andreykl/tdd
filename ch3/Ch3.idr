module Main

import Data.Vect

total
transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = replicate _ []
transposeMat (row :: matrix) = zipWith (::) row (transposeMat matrix)

total
allLengths : Vect m String -> Vect m Nat
allLengths [] = []
allLengths (x :: xs) = length x :: allLengths xs

total
insSort : Ord elem => Vect m elem -> Vect m elem
insSort [] = []
insSort (x :: xs) = ins x (insSort xs) where
  ins : Ord elem => (x : elem) -> (xs : Vect len elem) -> Vect (S len) elem
  ins x [] = [x]
  ins x (y :: xs) = if x < y then x :: y :: xs else y :: ins x xs

total
addMatrix : (Num numType) => 
            Vect rows (Vect cols numType) ->
            Vect rows (Vect cols numType) ->
            Vect rows (Vect cols numType)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = (zipWith (+) x y) :: addMatrix xs ys

total
multTransposed : Num numType => Vect m (Vect n numType) -> Vect p (Vect n numType) -> Vect m (Vect p numType)
multTransposed [] mtx2 = []
multTransposed (row :: mtx1) mtx2 = mkrow row mtx2 :: multTransposed mtx1 mtx2 where
  mkrow : Vect n numType -> Vect p (Vect n numType) -> Vect p numType
  mkrow xs ys = map (\yys => sum (zipWith (*) xs yys)) ys


total
multMatrix : (Num numType) =>
             Vect m (Vect n numType) ->
             Vect n (Vect p numType) ->
             Vect m (Vect p numType)
multMatrix mtx1 mtx2 = multTransposed mtx1 $ transposeMat mtx2
    

