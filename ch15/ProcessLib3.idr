module ProcessLib3

import System.Concurrency.Channels

%default total

export
data Forever = More Forever

export partial
forever : Forever
forever = More forever

public export
data ProcState = NoRequest | Sent | Complete

public export
data MessagePID : (reqType -> Type) -> Type where
  MkMessagePID : PID -> MessagePID iface

public export
data Process : (reqType -> Type) -> Type -> ProcState -> ProcState -> Type where
  Spawn : Process service_iface () NoRequest Complete -> 
          Process iface (Maybe (MessagePID service_iface)) st st
  Action : IO a -> Process iface a st st
  Request : (MessagePID service_iface) -> (msg : reqType) ->
            Process iface (service_iface msg) st st

  Respond : ((msg : reqType) -> 
              Process iface (iface msg) NoRequest NoRequest) ->
            Process iface (Maybe reqType) st Sent
  Loop : Inf (Process iface a NoRequest Complete) -> Process iface a Sent Complete

  Pure : a -> Process iface a st st
  (>>=) : Process iface a st1 st2 -> (a -> Process iface b st2 st3) -> Process iface b st1 st3

export
run : Forever -> Process iface a st1 st2 -> IO (Maybe a)
run frvr (Spawn proc) = do 
  Just pid <- spawn (do run frvr proc; pure ())
    | Nothing => pure Nothing
  pure (Just $ Just $ MkMessagePID pid)
run _ (Action act) = Just <$> act
run _ (Request (MkMessagePID pid) msg {service_iface}) = do
  Just chan <- connect pid
    | Nothing => pure Nothing
  True <- unsafeSend chan msg
    | False => pure Nothing
  Just a <- unsafeRecv (service_iface msg) chan
    | Nothing => pure Nothing
  pure (Just a)
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
run (More frvr) (Loop proc) = run frvr proc
run _ (Pure x) = pure (Just x)
run frvr (x >>= f) = do Just res <- run frvr x
                          | Nothing => pure Nothing
                        run frvr (f res)

export partial
runProc : Process iface a st1 st2 -> IO ()
runProc proc = do run forever proc; pure ()

public export
Service : (reqType -> Type) -> Type -> Type
Service iface a = Process iface a NoRequest Complete

public export
NoRecv : Void -> Type
NoRecv = const Void

public export
Client : Type -> Type
Client a = Process NoRecv a NoRequest NoRequest
