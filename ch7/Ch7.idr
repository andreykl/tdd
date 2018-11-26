module Main

import Data.Vect

occurrences : Eq ty => (item : ty) -> (items : List ty) -> Nat
occurrences item [] = Z
occurrences item (x :: xs) = let occs = occurrences item xs in if x == item then (S occs) else occs

data Shape = Triangle Double Double
             | Rectangle Double Double
             | Circle Double

square : Shape -> Double
square (Triangle x y) = x * y / 2
square (Rectangle x y) = x * y
square (Circle x) = pi * (x * x)

Eq Shape where
  (Triangle x y) == (Triangle z w) = x == z && y == w
  (Rectangle x y) == (Rectangle z w) = x == z && y == w
  (Circle x) == (Circle y) = x == y
  _ == _ = False

Ord Shape where
  compare sh1 sh2 = compare (square sh1) (square sh2)
  
testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4,
              Rectangle 2 7]

data Expr : (num : Type) -> Type where
  Val : num -> Expr num
  Add : Expr num -> Expr num -> Expr num
  Mul : Expr num -> Expr num -> Expr num
  Sub : Expr num -> Expr num -> Expr num
  Div : Expr num -> Expr num -> Expr num
  Mod : Expr num -> Expr num -> Expr num
  Abs : Expr num -> Expr num

eval : (Abs num, Integral num, Neg num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Mul x y) = eval x * eval y
eval (Sub x y) = eval x - eval y
eval (Div x y) = eval x `div` eval y
eval (Mod x y) = eval x `mod` eval y
eval (Abs x) = abs (eval x)

Num a => Num (Expr a) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Abs a => Abs (Expr a) where
  abs = Abs

Integral a => Integral (Expr a) where
  div = Div
  mod = Mod

totalLength : List String -> Nat
totalLength xs = foldr (\s, acc => length s + acc) 0 xs

data Tree : (elem: Type) -> Type where
  Empty : Tree elem
  Node : (left: Tree elem) -> elem -> (right: Tree elem) -> Tree elem
  
Functor Tree where
  map f Empty = Empty
  map f (Node left x right) = Node (map f left) (f x) (map f right)

Foldable Tree where
  foldr func acc Empty = acc
  foldr func acc (Node left x right) = foldr func (func x (foldr func acc left)) right

data EqNat : (n : Nat) -> (m : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

-- checkEqNat : (n : Nat) -> (m : Nat) -> Maybe (EqNat n m)
-- checkEqNat Z Z = Just $ Same _
-- checkEqNat Z (S k) = Nothing
-- checkEqNat (S k) Z = Nothing
-- checkEqNat (S k) (S j) = 
--   let ih = checkEqNat k j
--   in map (\(Same n) => Same (S n)) ih

same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons Refl = Refl

same_lists : {xs : List a} -> {ys : List a} -> xs = ys -> x = y -> x :: xs = y :: ys
same_lists Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
  ThreeSame : (v: a) -> ThreeEq v v v

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x (ThreeSame x) = ThreeSame (S x)

myReverse' : Vect n a -> Vect m a -> Vect (n + m) a
myReverse' [] ys {n=Z} = ys
myReverse' (x::xs) ys {n=S k} {m} = rewrite plusSuccRightSucc k m in myReverse' xs (x::ys)

myReverse : Vect n elem -> Vect n elem
myReverse xs {n} = rewrite sym $ plusZeroRightNeutral n in myReverse' xs []

myPlusCommutes0N : n = plus n 0
myPlusCommutes0N {n = Z} = Refl
myPlusCommutes0N {n = (S k)} = 
  let
    ih = myPlusCommutes0N {n=k}
  in rewrite ih in Refl

sPlusKNisPlusNSK : (k : Nat) -> (n : Nat) -> S (plus n k) = plus n (S k)
sPlusKNisPlusNSK k Z = Refl
sPlusKNisPlusNSK k (S j) = 
  let
    ih = sPlusKNisPlusNSK k j
  in rewrite ih in Refl

myPlusCommutes : (m, n : Nat) -> (m + n) = (n + m)
myPlusCommutes Z n = myPlusCommutes0N
myPlusCommutes (S k) n = 
  let
    ih = myPlusCommutes k n
  in (rewrite ih in (sPlusKNisPlusNSK k n))

twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

loop : Void
loop = loop

xNotSucc : (x : Nat) -> x = S x -> Void
xNotSucc _ Refl impossible

zNotSk : (0 = S k) -> Void
zNotSk Refl impossible

sKnotZ : (S k = 0) -> Void
sKnotZ Refl impossible

contraS : (contra : (k = j) -> Void) -> (S k = S j) -> Void
contraS contra Refl {j} = contra (Refl {x=j})

checkEqNat : (x, y : Nat) -> Dec (x = y)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No zNotSk
checkEqNat (S k) Z = No sKnotZ
checkEqNat (S k) (S j) = 
  case checkEqNat k j of
    (Yes Refl) => Yes Refl
    (No contra) => No (contraS contra)

data Vec : (n: Nat) -> (elem: Type) -> Type where
  VNil : Vec Z elem
  VCons : elem -> Vec n elem -> Vec (S n) elem

headUnequal : DecEq a => {xs : Vec n a} -> {ys : Vec n a} ->
       (contra : (x = y) -> Void) -> ((VCons x xs) = (VCons y ys)) -> Void   
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vec n a} -> {ys : Vec n a} ->
       (contra : (xs = ys) -> Void) -> ((VCons x xs) = (VCons y ys)) -> Void
tailUnequal contra Refl = contra Refl

DecEq a => DecEq (Vec n a) where
  decEq VNil VNil = Yes Refl
  decEq (VCons x xs) (VCons y ys) = 
    case decEq x y of
      (Yes Refl) => 
        case decEq xs ys of
          (Yes Refl) => Yes Refl
          (No contra) => No (tailUnequal contra)
      (No contra) => No (headUnequal contra)
