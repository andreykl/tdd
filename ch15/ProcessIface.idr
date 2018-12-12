module Main

import System.Concurrency.Channels

%default total

data Forever = More Forever

data ProcState = NoRequest | Sent | Complete

data Message = Add Nat Nat

data MessagePID : (iface : reqType -> Type) -> Type where
  MkMessage : PID -> MessagePID iface
  
data Process : (iface : reqType -> Type) -> Type -> (in_state : ProcState) -> (out_state : ProcState) -> Type where
  Action : IO a -> Process iface a st st
  Spawn : Process service_iface () NoRequest Complete -> Process iface (Maybe (MessagePID service_iface)) st st
  Request : MessagePID service_iface -> (msg : service_reqType) -> Process iface (service_iface msg) st st
  Respond : ((msg : reqType) -> Process iface (iface msg) NoRequest NoRequest) -> Process iface (Maybe reqType) st Sent
  Loop : Inf (Process iface a NoRequest Complete) -> Process iface a Sent Complete
  
  Pure : a -> Process iface a st st
  (>>=) : Process iface a state1 state2 -> (a -> Process iface b state2 state3) -> Process iface b state1 state3

AdderType : Message -> Type
AdderType (Add k j) = Nat

NoRecv : Void -> Type
NoRecv = const Void

Service : (iface : reqType -> Type) -> Type -> Type
Service iface a = Process iface a NoRequest Complete

Client : Type -> Type
Client a = Process NoRecv a NoRequest NoRequest

run : Forever -> Process iface a in_state out_state -> IO (Maybe a)
run _ (Action act) = Just <$> act
run frvr (Spawn proc) = do
  Just pid <- spawn (do run frvr proc; pure ())
    | Nothing => pure Nothing
  pure (Just (Just (MkMessage pid)))
run _ (Request (MkMessage pid) msg {service_iface}) = do
  Just chan <- connect pid
    | Nothing => pure Nothing
  True <- unsafeSend chan msg
    | False => pure Nothing
  Just a <- unsafeRecv (service_iface msg) chan
    | Nothing => pure Nothing
  pure (Just a)
run frvr (Respond p {reqType}) = do
  Just chan <- listen 1
    | Nothing => pure (Just Nothing)
  Just msg <- unsafeRecv reqType chan
    | Nothing => pure (Just Nothing)
  Just a <- run frvr (p msg)
    | Nothing => pure Nothing
  True <- unsafeSend chan a
    | False => pure (Just Nothing)
  pure (Just (Just msg))
run (More frvr) (Loop proc) = run frvr proc
run _ (Pure x) = pure (Just x)
run frvr (proc >>= cont) = do Just a <- run frvr proc
                                | Nothing => pure Nothing
                              run frvr (cont a)

procAdder : Service AdderType ()
procAdder = do
  Respond (\(Add x y) => Pure (x + y))
  Loop procAdder

procMain : Client ()
procMain = do
  Just pid <- Spawn procAdder
    | Nothing => Action (putStrLn "unable to spawn")
  a <- Request pid (Add 5 3)
  Action (putStrLn $ "answer is " ++ show a)

partial
forever : Forever
forever = More forever

partial
runProc : Process iface () in_state out_state -> IO ()
runProc proc = do run forever proc
                  pure ()
