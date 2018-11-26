module Main

import Data.Vect

%default total

Position : Type
Position = (Double, Double)

Polygon : Nat -> Type
Polygon k = Vect k Position


tri : Polygon 3
tri = [(0, 0), (3, 0), (0, 4)]

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStingOrInt : (isInt : Bool) -> StringOrInt isInt
getStingOrInt False = "ninety four"
getStingOrInt True = 94

valToString : (isInt : Bool) -> (case isInt of
                                      False => String
                                      True => Int) -> String
valToString False x = trim x
valToString True x = cast x

AdderType : Nat -> Type
AdderType Z = Int
AdderType (S k) = Int -> AdderType k

mkadder : (k : Nat) -> Int -> AdderType k
mkadder Z acc = acc
mkadder (S k) acc = \i => mkadder k (acc + i)

adder : (n : Nat) -> AdderType n
adder n = mkadder n 0

data PrintFFormat = PFInt PrintFFormat 
                  | PFBool PrintFFormat 
                  | PFString (List Char) PrintFFormat 
                  | PFDouble PrintFFormat
                  | PFChar PrintFFormat
                  | PFEnd

PrintFType : PrintFFormat -> Type
PrintFType (PFInt fmt) = (i: Int) -> PrintFType fmt
PrintFType (PFBool fmt) = (b: Bool) -> PrintFType fmt
PrintFType (PFDouble fmt) = (d: Double) -> PrintFType fmt
PrintFType (PFChar fmt) = (c: Char) -> PrintFType fmt
PrintFType (PFString xs fmt) = PrintFType fmt
PrintFType PFEnd = String

stringToFormat : (format: String) -> PrintFFormat
stringToFormat format = strtofmt (unpack format) where
  strtofmt : List Char -> PrintFFormat
  strtofmt [] = PFEnd
  strtofmt ('%' :: 'i' :: xs) = PFInt (strtofmt xs)
  strtofmt ('%' :: 'b' :: xs) = PFBool (strtofmt xs)
  strtofmt ('%' :: 'c' :: xs) = PFChar (strtofmt xs)
  strtofmt ('%' :: 'f' :: xs) = PFDouble (strtofmt xs)  
  strtofmt (x :: xs) = 
    case strtofmt xs of
      (PFString cs fmt) => PFString (x :: cs) fmt
      fmt               => PFString [x] fmt


mkbody : (fmt: PrintFFormat) -> String -> PrintFType fmt
mkbody (PFInt fmt) acc = \i => mkbody fmt (acc ++ show i)
mkbody (PFBool fmt) acc = \b => mkbody fmt (acc ++ show b)
mkbody (PFDouble fmt) acc = \d => mkbody fmt (acc ++ show d)
mkbody (PFChar fmt) acc = \c => mkbody fmt (acc ++ show c)
mkbody (PFString xs fmt) acc = mkbody fmt (acc ++ (pack xs))
mkbody PFEnd acc = acc

printf : (format: String) -> PrintFType (stringToFormat (format))
printf format = mkbody _ ""

Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Double)

testMatrix : Matrix 2 3
testMatrix = [[0, 0, 0], [0, 0, 0]]

TupleVect : (size : Nat) -> (ty : Type) -> Type
TupleVect Z ty = ()
TupleVect (S k) ty = (ty, TupleVect k ty)

test : TupleVect 4 Nat
test = (1,2,3,4,())
