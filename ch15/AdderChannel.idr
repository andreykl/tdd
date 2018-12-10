module Main

import System.Concurrency.Channels

data Message = Add Nat Nat

adder : IO ()
adder = do
  Just ch <- listen 1
    | Nothing => adder
  Just (Add x y) <- unsafeRecv Message ch
    | Nothing => adder
  unsafeSend ch (x + y)
  adder
  
main : IO ()
main = do
  Just pid <- spawn adder
    | Nothing => putStrLn "unable to spawn"
  Just ch <- connect pid
    | Nothing => putStrLn "unable to connect"
  sent <- unsafeSend ch (Add 3 8)
  if sent
  then do
    putStrLn "message successfully sent, trying to receive an answer"
    (Just a) <- unsafeRecv Nat ch
      | Nothing => putStrLn "unable to receive the answer"
    putStrLn $ "answer is " ++ show a
  else
    putStrLn "unable to send message to adder"
