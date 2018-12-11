module Main

import System.Concurrency.Channels

data Message = Add Nat Nat

data MessagePID = MkMessage PID

data Process : Type -> Type where
  Action : IO ty -> Process ty
  Spawn : Process () -> Process (Maybe MessagePID)
  Request : (msg : Message) -> MessagePID -> Process (Maybe Nat)
  Respond : (Message -> Nat) -> Process (Maybe Message)
  
  Pure : a -> Process a
  (>>=) : Process a -> (a -> Process b) -> Process b


run : Process ty -> IO ty
run (Action act) = act
run (Spawn proc) = 
  do Just pid <- spawn (run proc)
       | Nothing => pure Nothing
     pure (Just $ MkMessage pid)
run (Request msg (MkMessage pid)) = 
  do Just chan <- connect pid
       | Nothing => pure Nothing
     pure (Just $ MkMessage pid)
     ok <- unsafeSend chan msg
     if ok
     then 
       do Just a <- unsafeRecv Nat chan
            | Nothing => pure Nothing
          pure $ Just a
     else 
       pure Nothing
run (Respond f) = 
  do Just chan <- listen 1
       | Nothing => pure Nothing
     Just msg <- unsafeRecv Message chan
       | Nothing => pure Nothing
     ok <- unsafeSend chan (f msg)
     if ok then pure (Just msg) else pure Nothing
run (Pure x) = pure x
run (x >>= f) = do x' <- run x
                   run (f x')

procAdder : Process ()
procAdder = do Respond (\msg => case msg of
                                  (Add k j) => k + j)
               procAdder

procMain : Process ()
procMain =
  do Just msgpid <- Spawn procAdder
       | Nothing => Action (putStrLn "unable to spawn")
     Just a <- Request (Add 5 3) msgpid
       | Nothing => Action (putStrLn "unable to request")
     Action (putStrLn $ "answer is " ++ show a)

Loop : Inf (Process a) -> Process a
