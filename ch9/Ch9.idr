module Main

import Data.Vect
import Data.List

removeElem1: DecEq a => (value : a) -> Vect (S n) a -> Vect n a
removeElem1 value (x :: xs) {n=S k} = 
  case decEq value x of
    (Yes prf) => xs
    (No contra) => x :: removeElem1 value xs

-- removeElem : DecEq a => (value : a) -> (xs : Vect (S n) a) -> Vect n a
-- removeElem value (x :: xs) = case decEq value x of
--                                   Yes prf => xs
--                                   No contra => x :: removeElem value xs

maryInVector : Elem "Mary" (the (Vect _ _) ["Peter", "Paul", "Mary"])
maryInVector = There (There Here)

removeElem : (elem : a) -> (vect: Vect (S n) a) -> Elem elem vect -> Vect n a
removeElem elem (elem :: xs) Here = xs
removeElem {n = Z} elem (y :: []) (There later) = absurd later
removeElem {n = (S k)} elem (y :: xs) (There later) = y :: removeElem elem xs later

Uninhabited (2 + 2 = 5) where
  uninhabited Refl impossible
  
noThereNoHere : {a: Type} -> {xs: Vect n a} -> {elem: a} -> (contra : elem = x -> Void) -> (contra1 : Elem elem xs -> Void) -> Elem elem (x::xs) -> Void
noThereNoHere eqcontra therecontra Here = eqcontra Refl
noThereNoHere eqcontra therecontra (There later) = therecontra later

isElem1 : DecEq a => (elem : a) -> (xs: Vect n a) -> Dec (Elem elem xs)
isElem1 elem [] = No absurd
isElem1 elem (x :: xs) with (decEq elem x)
  isElem1 x (x :: xs) | (Yes Refl) = Yes Here
  isElem1 elem (x :: xs) | (No neqc) with (isElem1 elem xs)
    isElem1 elem (x :: xs) | (No neqc) | (Yes prf) = Yes (There prf)
    isElem1 elem (x :: xs) | (No neqc) | (No noThereContra) = No (noThereNoHere neqc noThereContra)


noTailNoEqNoList : {a : Type} -> {elem : a} -> {xs : List a} -> (contra : (elem = x) -> Void) -> (f : Elem elem xs -> Void) -> Elem elem (x :: xs) -> Void
noTailNoEqNoList contra f Here = contra Refl
noTailNoEqNoList contra f (There later) = f later

isElem2 : DecEq a => (elem : a) -> (xs : List a) -> Dec (Elem elem xs)
isElem2 elem [] = No absurd
isElem2 elem (x :: xs) with (decEq elem x)
  isElem2 x (x :: xs) | (Yes Refl) = Yes Here
  isElem2 elem (x :: xs) | (No contra) with (isElem2 elem xs)
    isElem2 elem (x :: xs) | (No contra) | (Yes prf) = Yes (There prf)
    isElem2 elem (x :: xs) | (No contra) | (No f) = No (noTailNoEqNoList contra f)

data Last : List a -> a -> Type where
     LastOne : Last [value] value
     LastCons : (prf : Last xs value) -> Last (x :: xs) value

noEmpty : Last [] value -> Void
noEmpty LastOne impossible
noEmpty (LastCons _) impossible

noEmptyNoXEqVal : (contra1 : (x = value) -> Void) -> (contra : Last [] value -> Void) -> Last [x] value -> Void
noEmptyNoXEqVal contra1 contra LastOne = contra1 Refl
noEmptyNoXEqVal contra1 contra (LastCons prf) = contra prf

noSmallerNoBigger : (contra : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
noSmallerNoBigger contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No noEmpty
isLast (x :: xs) value with (isLast xs value)
  isLast (x :: xs) value | (Yes prf) = Yes (LastCons prf)
  isLast (x :: []) value | (No contra) = 
    case decEq x value of
      (Yes Refl) => Yes LastOne
      (No contra1) => No (noEmptyNoXEqVal contra1 contra)
  isLast (x :: (y::xs)) value | (No contra) = No (noSmallerNoBigger contra)

listXnoValue : (contra : (x = value) -> Void) -> Last [x] value -> Void
listXnoValue contra LastOne = contra Refl
listXnoValue _ (LastCons LastOne) impossible
listXnoValue _ (LastCons (LastCons _)) impossible

isLast1 : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast1 [] value = No noEmpty
isLast1 (x :: []) value with (decEq x value)
  isLast1 (value :: []) value | (Yes Refl) = Yes LastOne
  isLast1 (x :: []) value | (No contra) = No (listXnoValue contra)
isLast1 (x :: (y :: xs)) value with (isLast1 (y :: xs) value)
  isLast1 (x :: (y :: xs)) value | (Yes prf) = Yes (LastCons prf)
  isLast1 (x :: (y :: xs)) value | (No contra) = No (noSmallerNoBigger contra)


