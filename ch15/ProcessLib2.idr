module ProcessLib2

import System.Concurrency.Channels

%default total

public export
data Forever = More Forever

export partial
forever : Forever
forever = More forever

public export
data ProcessState = NoRequest | Sent | Complete

export
data MessagePID : (iface : reqType -> Type) -> Type where
  MkMessagePID : PID -> MessagePID iface

public export
data Process : (iface : reqType -> Type) -> Type ->
               ProcessState -> ProcessState -> Type where
  Spawn : (Process service_iface () NoRequest Complete) -> 
          Process iface (Maybe (MessagePID service_iface)) st st
  Request : MessagePID service_iface -> (msg : reqType) -> 
            Process iface (service_iface msg) st st
  Action : IO a -> Process iface a st st

  Respond : ((msg : reqType) -> 
            Process service_iface (service_iface msg) NoRequest NoRequest) -> 
            Process service_iface (Maybe reqType) NoRequest Sent
  Loop : Inf (Process service_iface reqType NoRequest Complete) ->
         Process service_iface reqType Sent Complete

  Pure : a -> Process iface a st st
  (>>=) : Process iface a state1 state2 -> (a -> Process iface b state2 state3) -> Process iface b state1 state3

export
run : Forever -> Process iface a instate outstate -> IO (Maybe a)
run frvr (Spawn proc) = do
  Just pid <- spawn (do run frvr proc; pure ())
    | Nothing => pure (Just Nothing)
  pure (Just $ Just $ MkMessagePID pid)
run _ (Request (MkMessagePID pid) msg {service_iface}) = do
  Just chan <- connect pid
    | Nothing => pure Nothing
  True <- unsafeSend chan msg
    | False => pure Nothing
  Just a <- unsafeRecv (service_iface msg) chan
    | Nothing => pure Nothing
  pure (Just a)
run _ (Action act) = Just <$> act
run frvr (Respond f {reqType}) = do
  Just chan <- listen 1
    | Nothing => pure (Just Nothing)
  Just msg <- unsafeRecv reqType chan
    | Nothing => pure (Just Nothing)
  Just res <- run frvr (f msg)
    | Nothing => pure Nothing
  True <- unsafeSend chan res
    | False => pure (Just Nothing)
  pure (Just $ Just msg)
run _ (Pure x) = pure (Just x)
run frvr (x >>= f) = do (Just res) <- run frvr x
                          | Nothing => pure Nothing
                        run frvr (f res)
run (More frvr) (Loop proc) = run frvr proc

export partial
runProc : Process iface a instate outstate -> IO ()
runProc proc = do run forever proc
                  pure ()

public export
Service : (iface : reqType -> Type) -> Type -> Type
Service iface a = Process iface a NoRequest Complete

public export
NoRecv : Void -> Type
NoRecv = const Void

public export
Client : Type -> Type
Client a = Process NoRecv a NoRequest NoRequest
