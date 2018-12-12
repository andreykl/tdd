module ProcessLib

import System.Concurrency.Channels

%default total

public export
data Forever = More Forever

export partial
forever : Forever
forever = More forever

public export
data ProcState = NoRequest | Sent | Complete

export
data MessagePID : (iface : reqType -> Type) -> Type where
  MkMessage : PID -> MessagePID iface

public export  
data Process : (iface : reqType -> Type) -> Type -> (in_state : ProcState) -> (out_state : ProcState) -> Type where
  Action : IO a -> Process iface a st st
  Spawn : Process service_iface () NoRequest Complete -> Process iface (Maybe (MessagePID service_iface)) st st
  Request : MessagePID service_iface -> (msg : service_reqType) -> Process iface (service_iface msg) st st
  Respond : ((msg : reqType) -> Process iface (iface msg) NoRequest NoRequest) -> Process iface (Maybe reqType) st Sent
  Loop : Inf (Process iface a NoRequest Complete) -> Process iface a Sent Complete
  
  Pure : a -> Process iface a st st
  (>>=) : Process iface a state1 state2 -> (a -> Process iface b state2 state3) -> Process iface b state1 state3

export
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

public export
NoRecv : Void -> Type
NoRecv = const Void

public export
Service : (iface : reqType -> Type) -> Type -> Type
Service iface a = Process iface a NoRequest Complete

public export
Client : Type -> Type
Client a = Process NoRecv a NoRequest NoRequest

export partial
runProc : Process iface () in_state out_state -> IO ()
runProc proc = do run forever proc
                  pure ()
