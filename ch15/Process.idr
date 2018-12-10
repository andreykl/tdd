module Main

import System.Concurrency.Channels

data Message = Add Nat Nat

data MessagePID = MkMessage PID

data Process : Type -> Type where
  Action : IO a -> Process a
  Spawn : Process () -> Process (Maybe MessagePID)
  Request : MessagePID -> Message -> Process (Maybe Nat)
  Respond : ((msg : Message) -> Process Nat) -> Process (Maybe Message)
  
  Pure : a -> Process a
  (>>=) : Process a -> (a -> Process b) -> Process b

run : Process t -> IO t
run (Respond calc) = do
  Just ch <- listen 1
    | Nothing => pure Nothing
  Just msg <- unsafeRecv Message ch
    | Nothing => pure Nothing
  res <- run (calc msg)
  unsafeSend ch res
  pure (Just msg)
run (Request (MkMessage pid) msg) = do
  Just ch <- connect pid
    | Nothing => pure Nothing
  ok <- unsafeSend ch msg
  if ok
  then 
    do (Just a) <- unsafeRecv Nat ch
         | Nothing => pure Nothing
       pure (Just a)
  else
    pure Nothing
run (Spawn proc) = do
  Just pid <- spawn (run proc)
    | Nothing => pure Nothing
  pure (Just $ MkMessage pid)
run (Action x) = x
run (Pure x) = pure x
run (prc >>= next) = do
  res <- run prc
  run (next res)

procAdder : Process ()
procAdder = do
  Respond (\msg => case msg of
                     Add x y => Pure (x + y))
  procAdder

procMain : Process ()
procMain = do
  do Just adder <- Spawn procAdder
       | Nothing => Action (putStrLn "spawn failed")
     Just a <- Request adder (Add 5 7)
       | Nothing => Action (putStrLn "unable to send or receive")
     Action (printLn a)
