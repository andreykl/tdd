module Main

import ProcessLib

data Message = Add Nat Nat

AdderType : Message -> Type
AdderType (Add k j) = Nat

procAdder : Service AdderType ()
procAdder = do
  Respond (\(Add x y) => Pure (x + y*2))
  Loop procAdder

procMain : Client ()
procMain = do
  Just pid <- Spawn procAdder
    | Nothing => Action (putStrLn "unable to spawn")
  a <- Request pid (Add 5 4)
  Action (putStrLn $ "answer is " ++ show a)
