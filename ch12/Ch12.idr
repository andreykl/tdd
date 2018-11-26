module Main

import Control.Monad.State

%default total

data Tree a = Leaf | Node (Tree a) a (Tree a)

-- %name t1, t2, t3

labelTree : Stream labelType -> Tree a -> Tree (labelType, a)
labelTree xs t = evalState (labelTreeHelper t) xs where
  labelTreeHelper : Tree a -> State (Stream labelType) (Tree (labelType, a))
  labelTreeHelper Leaf = pure Leaf
  labelTreeHelper (Node lt v rt) =
    do lt' <- labelTreeHelper lt
       (x :: xs) <- get
       put xs
       rt' <- labelTreeHelper rt
       pure (Node lt' (x, v) rt')
 

testTree : Tree String
testTree = Node (Node Leaf "One" Leaf) "Two" (Node (Node Leaf "Three" (Node Leaf "Four" Leaf)) "Five" (Node Leaf "Six" Leaf))

update : (stateType -> stateType) -> State stateType ()
update f = do v <- get
              put (f v)
              
increase : Nat -> State Nat ()
increase x = update (+x)

countEmpty : Tree a -> Nat
countEmpty x = execState (countEmptyHelper x) 0 where
  countEmptyHelper : Tree a -> State Nat ()
  countEmptyHelper Leaf = update (+1)
  countEmptyHelper (Node lt _ rt) = 
    do countEmptyHelper lt
       countEmptyHelper rt
 
countEmptyNode : Tree a -> (Nat, Nat)
countEmptyNode x = execState (countEmptyNodeHlpr x) (0, 0) where
  countEmptyNodeHlpr : Tree a -> State (Nat, Nat) ()
  countEmptyNodeHlpr Leaf = do (emp, nds) <- get
                               put (emp + 1, nds)
  countEmptyNodeHlpr (Node lt _ rt) = do countEmptyNodeHlpr lt
                                         (emp, nds) <- get
                                         put (emp, nds + 1)
                                         countEmptyNodeHlpr rt
crew : List String
crew = ["Lister", "Rimmer", "Kryten", "Cat"]

-- printCrew : List String -> IO ()
-- printCrew (x :: xs) = do putStrLn x
--                          printCrew xs
-- printCrew _ = pure ()

main : IO ()
main = do putStr "Dislpay crew? " 
          ans <- getLine
          when (ans == "yes") $
               traverse_ putStrLn crew
          putStrLn "Done"
