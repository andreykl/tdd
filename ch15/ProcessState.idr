module Main

import System.Concurrency.Channels

%default total

data Forever = More Forever

data Message = Add Nat Nat

data MessagePID = MkMessage PID

data ProcessState = NoRequest | Sent | Complete


data Process : Type -> ProcessState -> ProcessState -> Type where
  Action : IO a -> Process a st st
  Spawn : (Process () NoRequest Complete) -> Process (Maybe MessagePID) st st
  Request : MessagePID -> Message -> Process Nat st st
  Respond : (Message -> Nat) -> Process (Maybe Message) NoRequest Sent
  Loop : Inf (Process a NoRequest Complete) -> Process a Sent Complete

  Pure : a -> Process a st st
  (>>=) : Process a st1 st2 -> (a -> Process b st2 st3) -> Process b st1 st3
  
Service : Type -> Type
Service a = Process a NoRequest Complete

Client : Type -> Type
Client a = Process a NoRequest NoRequest

procAdder : Service ()
procAdder = do
  Respond (\(Add k j) => k + j*2)
  Loop procAdder

procMain : Client ()
procMain = do
  Just pid <- Spawn procAdder
    | Nothing => Action (putStrLn "unable to spawn")
  a <- Request pid (Add 6 5)
  Action (putStrLn $ "answer is " ++ show a)

run : Forever -> Process a st1 st2 -> IO (Maybe a)
run _ (Action act) = Just <$> act
run frvr (Spawn proc) = do
  Just pid <- spawn (do run frvr proc; pure ())
    | Nothing => pure Nothing
  pure (Just $ Just (MkMessage pid))
run _ (Request (MkMessage pid) msg) = do
  Just chan <- connect pid
    | Nothing => pure Nothing
  True <- unsafeSend chan msg
    | False => pure Nothing
  Just a <- unsafeRecv Nat chan
    | Nothing => pure Nothing
  pure (Just a)
run _ (Respond f) = do
  Just chan <- listen 1
    | Nothing => pure Nothing
  Just msg <- unsafeRecv Message chan
    | Nothing => pure Nothing
  True <- unsafeSend chan (f msg)
    | False => pure Nothing
  pure (Just (Just msg))
run (More frvr) (Loop proc) = run frvr proc
run _ (Pure x) = pure (Just x)
run frvr (x >>= f) = do Just a <- run frvr x
                          | Nothing => pure Nothing
                        run frvr (f a)


partial
forever : Forever
forever = More forever

partial
runProc : Process t in_state out_state -> IO ()
runProc proc = do run forever proc
                  pure ()
