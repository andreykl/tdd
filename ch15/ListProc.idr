module ListProc

import ProcessLib

data ListAction : Type where
  Length : List elem -> ListAction
  Concat : List elem -> List elem -> ListAction

ListActionType : ListAction -> Type
ListActionType (Length _) = Nat
ListActionType (Concat _ _ {elem}) = List elem

procList : Service ListActionType ()
procList = do
  Respond (\msg => case msg of
                     (Length xs) => Pure (length xs)
                     (Concat xs ys) => Pure (xs ++ ys))
  Loop procList

procMain : Client ()
procMain = do
  Just pid <- Spawn procList
    | Nothing => Action (putStrLn "spawn failed")
  len <- Request pid (Length [1,2,3])
  Action (putStrLn $ "list len is " ++ show len)
  xs <- Request pid (Concat [1,2,4] [4,5,6])
  Action (putStrLn $ "concated list is " ++ show xs)

