module Main

import System.Concurrency.Channels

data Forever = More Forever

data Message = Add Nat Nat

data MessagePID = MkMessage PID

data Process : Type -> Type where
  Spawn : Process () -> Process (Maybe MessagePID)
  Request : MessagePID -> Message -> Process (Maybe Nat)
  Respond : (Message -> Nat) -> Process (Maybe Message)
  Action : IO a -> Process a
  Loop : Inf (Process a) -> Process a
  
  Pure : a -> Process a
  (>>=) : Process a -> (a -> Process b) -> Process b


run : Forever -> Process a -> IO a
run (More frvr) (Spawn proc) =
  do Just pid <- spawn (run frvr proc)
       | Nothing => pure Nothing
     pure (Just $ MkMessage pid)
run _ (Request (MkMessage pid) msg) =
  do Just chan <- connect pid
       | Nothing => pure Nothing
     ok <- unsafeSend chan msg
     if ok
     then
       do
         Just a <- unsafeRecv Nat chan
           | Nothing => pure Nothing
         pure (Just a)
     else pure Nothing
run _ (Respond f) = 
  do Just chan <- listen 1
       | Nothing => pure Nothing
     Just (Add x y) <- unsafeRecv Message chan
       | Nothing => pure Nothing
     ok <- unsafeSend chan (x + y)
     if ok then pure (Just $ Add x y) else pure Nothing
run _ (Action x) = x
run (More frvr) (Loop x) = run frvr x
run _ (Pure x) = pure x
run (More frvr) (x >>= f) = do res <- run frvr x
                               run frvr (f res)

procAdder : Process ()
procAdder = do Respond (\msg => case msg of
                          Add x y => x + y)
               Loop procAdder

procMain : Process ()
procMain =
  do Just pid <- Spawn procAdder
       | Nothing => Action (putStrLn "unable to spawn")
     Just a <- Request pid (Add 8 12)
       | Nothing => Action (putStrLn "unable to request")
     Action (putStrLn $ "answer is " ++ show a)

partial
forever : Forever
forever = More forever

partial
runProc : Process () -> IO ()
runProc proc = do res <- run forever proc
                  pure ()
