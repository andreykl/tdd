module Ch10

import Data.Vect
import Data.Vect.Views

import Data.List.Views

import Data.Nat.Views

data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)
  
takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S Z) [] = Fewer
takeN (S Z) (x :: xs) = Exact [x]
takeN (S k)     [] = Fewer
takeN (S k) (x :: xs) = 
  case takeN k xs of
    Fewer => Fewer
    (Exact k_xs) => Exact (x::k_xs)

groupByN : Nat -> List a -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

halves : List a -> (List a, List a)
halves xs with (takeN ((length xs) `div` 2) xs)
  halves xs | Fewer = ([], xs)
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)

isSuffix : Eq a => List a -> List a -> Bool
isSuffix xs ys with (snocList xs)
  isSuffix [] ys | Empty = True
  isSuffix (zs ++ [x]) ys | (Snoc rec) with (snocList ys)
    isSuffix (zs ++ [x]) [] | (Snoc rec) | Empty = False
    isSuffix (zs ++ [x]) (xs ++ [y]) | (Snoc rec) | (Snoc z) = if x == y 
                                                                  then isSuffix zs xs | rec | z
                                                                  else False

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec) = merge (mergeSort lefts | lrec) (mergeSort rights | rrec)

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys with (snocList xs)
  equalSuffix [] ys | Empty = []
  equalSuffix (zs ++ [x]) ys | (Snoc rec) with (snocList ys)
    equalSuffix (zs ++ [x]) [] | (Snoc rec) | Empty = []
    equalSuffix (zs ++ [x]) (xs ++ [y]) | (Snoc rec) | (Snoc z) = 
      if x == y 
        then equalSuffix zs xs | rec | z ++ [x]
        else []
          

mergeSortV : Ord a => Vect n a -> Vect n a
mergeSortV xs with (splitRec xs)
  mergeSortV [] | SplitRecNil = []
  mergeSortV [x] | SplitRecOne = [x]
  mergeSortV (ys ++ zs) | (SplitRecPair lrec rrec) = merge (mergeSortV ys | lrec) (mergeSortV zs | rrec)

toBinary : Nat -> String
toBinary Z = "0"
toBinary k = reverse (toBinaryHelper k)
  where
    toBinaryHelper : Nat -> String
    toBinaryHelper k with (halfRec k)
      toBinaryHelper Z | HalfRecZ = ""
      toBinaryHelper (n + n) | (HalfRecEven rec) = "0" ++ toBinaryHelper n | rec
      toBinaryHelper (S (n + n)) | (HalfRecOdd rec) = "1" ++ toBinaryHelper n | rec

palindrome : List Char -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec) = x == y && palindrome ys | rec


export
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

export
triangle : Double -> Double -> Shape
triangle = Triangle

export
rectangle : Double -> Double -> Shape
rectangle = Rectangle

export 
circle : Double -> Shape
circle = Circle

data ShapeView : Shape -> Type where
  STriangle : ShapeView (triangle base height)
  SRectangle : ShapeView (rectangle width height)
  SCircle : ShapeView (circle r)

shapeView : (shape : Shape) -> ShapeView shape
shapeView (Triangle x y) = STriangle
shapeView (Rectangle x y) = SRectangle
shapeView (Circle x) = SCircle


area : Shape -> Double
area shape with (shapeView shape)
  area (triangle base height) | STriangle = 0.5 * base * height
  area (rectangle width height) | SRectangle = width * height
  area (circle r) | SCircle = pi * (r * r)


