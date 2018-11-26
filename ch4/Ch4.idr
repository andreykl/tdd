module Main

import Data.Vect

data Tree a = Empty | Node (Tree a) a (Tree a)

%name Tree t, t1, t2

insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x node@(Node left y right) = 
  case compare x y of
    LT => Node (insert x left) y right
    EQ => node
    GT => Node left y (insert x right)

listToTree : Ord elem => List elem -> Tree elem
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs)

treeToList : Tree elem -> List elem
treeToList Empty = []
treeToList (Node t x t1) = treeToList t ++ [x] ++ treeToList t1

data Expr = EInt Int | EAdd Expr Expr | ESub Expr Expr | EMult Expr Expr
%name Expr expr, expr1, expr2

evaluate : Expr -> Int
evaluate (EInt x) = x
evaluate (EAdd expr expr1) = evaluate expr + evaluate expr1
evaluate (ESub expr expr1) = evaluate expr - evaluate expr1
evaluate (EMult expr expr1) = evaluate expr * evaluate expr1

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe x y = max <$> x <*> y

data Shape : Type where
     Triangle : Double -> Double -> Shape
     Rectangle : Double -> Double -> Shape
     Circle : Double -> Shape
     
data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture
             
biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive (Triangle x y)) = Just ((x * y) / 2)
biggestTriangle (Primitive (Rectangle x y)) = Nothing
biggestTriangle (Primitive (Circle x)) = Nothing
biggestTriangle (Combine x y) = maxMaybe (biggestTriangle x) (biggestTriangle y)
biggestTriangle (Rotate x y) = biggestTriangle y
biggestTriangle (Translate x y z) = biggestTriangle z

testPic1 : Picture
testPic1 = Combine (Primitive (Triangle 2 3))
                   (Primitive (Triangle 2 4))

testPic2 : Picture
testPic2 = Combine (Primitive (Rectangle 1 3))
                   (Primitive (Circle 4))

tryIndex : Integer -> Vect n a -> Maybe a
tryIndex x xs = map (flip index xs) (integerToFin x _)


data PowerSource = Pedal | Petrol | Electicity | Battery

data Vehicle : PowerSource -> Type where
  Unicyle : Vehicle Pedal
  Bicycle : Vehicle Pedal
  Motocycle : (fuel : Nat) -> Vehicle Petrol
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol
  Tram : Vehicle Electicity
  ElectricCar : (charge : Nat) -> Vehicle Battery

total
wheels : Vehicle power -> Int
wheels Unicyle = 1
wheels Bicycle = 2
wheels (Motocycle fuel) = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels Tram = 4
wheels (ElectricCar charge) = 4

total
refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Motocycle fuel) = Motocycle 20
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200

total 
recharge : Vehicle Battery -> Vehicle Battery
recharge (ElectricCar charge) = ElectricCar 300


sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries pos xs ys {n} = ((\f, g, i => f i + g i) (flip Vect.index xs) (flip Vect.index ys)) <$> (integerToFin pos n)
