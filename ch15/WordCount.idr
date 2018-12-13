module WordCount

import System
import ProcessLib

record WordCount where
  constructor MkWordCount
  Words : Nat
  Lines : Nat

Show WordCount where
  show (MkWordCount words lines) = "words: " ++ show words ++ ", lines: " ++ show lines

doCount : String -> WordCount
doCount str =
  let
    ws = words str
    ls = lines str
  in MkWordCount (length ws) (length ls)

data CounterMessage : Type where
  Count : String -> CounterMessage
  GetData : String -> CounterMessage

CounterType : CounterMessage -> Type
CounterType (Count _) = ()
CounterType (GetData _) = Maybe WordCount

countFile : (loaded : List (String, WordCount)) -> (fname : String) -> Process iface (List (String, WordCount)) st st
countFile loaded fname = do
  Right str <- Action (readFile fname)
    | Left err => do Action (putStrLn "error during reading file")
                     Pure loaded
  Pure ((fname, doCount str) :: loaded)

procCounter : (loaded : List (String, WordCount)) -> Service CounterType ()
procCounter loaded = do
  msg <- Respond (\msg => case msg of
                            (Count _) => Pure ()
                            (GetData fname) => Pure (lookup fname loaded))
  newLoaded <- case msg of
    (Just (Count fname)) => countFile loaded fname
    _                    => Pure loaded

  Loop (procCounter newLoaded)

filename : String
filename = "ProcessLib.idr"

procMain : Client ()
procMain = do
  Action (putStrLn "requesting to count file ProcessLib.idr")
  Just pid <- Spawn $ procCounter []
    | Nothing => Action (putStrLn "spawn failed")
  Request pid (Count filename)
  Action (putStrLn "processing our processes...")
  Action (usleep 1000)
  Action (putStrLn "now requesting results")
  Just ans <- Request pid (GetData filename)
    | Nothing => Action (putStrLn "unable to find data for file")
  Action (putStrLn "data for file:")
  Action (printLn ans)
