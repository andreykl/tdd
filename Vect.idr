module Vect

%default total

data Vect : (n : Nat) -> (elem : Type) -> Type where
  Nil : Vect Z elem
  (::) : (x : elem) -> Vect n elem -> Vect (S n) elem

%name Vect xs, ys, zs, ws

append : Vect n elem -> Vect m elem -> Vect (n + m) elem
append [] ys = ys
append (elem :: xs) ys = elem :: append xs ys

zip : Vect n a -> Vect n b -> Vect n (a, b)
zip [] [] = []
zip (a :: xs) (b :: ys) = (a,b) :: zip xs ys

vectTake : (n : Nat) -> Vect (n + m) elem -> Vect n elem
vectTake Z xs = []
vectTake (S k) (x::xs) = x :: vectTake k xs

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
-- sumEntries pos xs ys {n = Z} = Nothing
-- sumEntries pos (x :: xs) (y :: ys) {n = (S k)} = if pos == 0 then Just (x+y) else sumEntries (pos-1) xs ys
