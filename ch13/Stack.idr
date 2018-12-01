module Main

import Data.Vect

%default total

data Forever = More Forever

partial
forever : Forever
forever = More forever

data StackCmd : Type -> (inputHeight : Nat) -> (outputHeight : Nat) -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)
  
  PutStr : String -> StackCmd () h h
  PutStrLn : String -> StackCmd () h h
  GetStr : StackCmd String h h
  
  Pure : a -> StackCmd a h h
  (>>=) : StackCmd a h1 h2 -> (a -> StackCmd b h2 h3) -> StackCmd b h1 h3

runStack : (stck : Vect inH Integer) -> StackCmd ty inH outH -> IO (ty, Vect outH Integer)
runStack stck (Push x) = pure ((), x :: stck)
runStack (x :: xs) Pop = pure (x, xs)
runStack (x :: xs) Top = pure (x, x :: xs)
runStack xs (PutStr str) = do putStr str; pure ((), xs)
runStack xs (PutStrLn str) = do putStrLn str; pure ((), xs)
runStack xs (GetStr) = do str <- getLine; pure (str, xs)
runStack stck (Pure x) = pure (x, stck)
runStack stck (x >>= f) = do (x', stck') <- runStack stck x 
                             runStack stck' (f x')

testAdd : StackCmd Integer 0 0
testAdd = 
  do Push 5
     Push 10
     a <- Pop
     b <- Pop
     Pure (a + b)

doBiOp : (Integer -> Integer -> Integer) -> StackCmd () (S (S height)) (S height)
doBiOp op = do a <- Pop; b <- Pop; Push (a `op` b)

biOp : (Integer -> Integer -> Integer) -> StackCmd a (S (S height)) (S height)

data StackIO : Nat -> Type where
  Do :    StackCmd a h1 h2 -> (a -> Inf (StackIO h2)) -> StackIO h1
  QuitCmd : (a : Nat) -> StackIO a

namespace StackDo
  (>>=) : StackCmd a h1 h2 -> (a -> Inf (StackIO h2)) -> StackIO h1
  (>>=) = Do

data Input : Type where
  INumber : Integer -> Input
  IAdd : Input
  ISub : Input
  IMult : Input
  IDisc : Input
  IDup : Input
  INeg : Input
--  IQuit : Input

parseInput : String -> Maybe Input
parseInput str = 
  case str of
    "" => Nothing
    "add" => Just IAdd
    "subtract" => Just ISub
    "multiply" => Just IMult
    "discard" => Just IDisc
    "neg" => Just INeg
    "dup" => Just IDup
    --"quit" => Just IQuit
    _      => if all isDigit $ unpack str then Just $ INumber (cast str) else Nothing
    
  

run : Forever -> Vect n Integer -> StackIO n -> IO ()
run _          _    (QuitCmd a) = pure ()
run (More far) stck (Do sa f)   = do (a', stck') <- runStack stck sa 
                                     run far stck' (f a')

mutual
  -- tryBiOp : (op : StackCmd () (S (S k)) (S k)) -> StackIO height
  -- tryBiOp op {height=S (S p)} = 
  --   do op 
  --      result <- Top
  --      PutStrLn $ show result
  --      stackCalc
  -- tryBiOp op = do PutStrLn "there are no enough elements to perform requested operation in stack"
  --                 stackCalc

  tryBiOp : Show a => String -> StackCmd a height ho  -> StackIO height
  tryBiOp _ op {height=S (S k)} =
    do a <- op
       PutStrLn $ show a
       stackCalc
  tryBiOp opVerb _ =
    do PutStrLn $ "no enough elements in stack to execute " ++ opVerb
       stackCalc
    
  trySub' : StackIO height
  trySub' = tryBiOp "subtract" (biOp (-))
      
  trySub : StackIO height
  trySub {height = S (S k)} =
    do doBiOp (-)
       result <- Top
       PutStrLn $ show result
       stackCalc
  trySub =
    do PutStrLn "no enough elements in stack to sub"
       stackCalc  
  
  tryMult : StackIO height
  tryMult {height = S (S k)} =
    do doBiOp (*)
       result <- Top
       PutStrLn $ show result
       stackCalc
  tryMult =
    do PutStrLn "no enough elements in stack to mult"
       stackCalc  
  
  tryAdd : StackIO height
  tryAdd {height = S (S k)} =
    do doBiOp (+)
       result <- Top
       PutStrLn $ show result
       stackCalc
  tryAdd =
    do PutStrLn "no enough elements in stack to add"
       stackCalc
       
  tryNeg : StackIO height
  tryNeg {height = S k} =
    do x <- Pop
       Push (-x)
       PutStrLn $ show (-x)
       stackCalc
  tryNeg =
    do PutStrLn "no elements in stack"
       stackCalc
  
  tryDuplicate : StackIO height
  tryDuplicate {height=S k} =
    do x <- Pop
       Push (2 * x)
       PutStrLn $ show (2 * x)
       stackCalc
  tryDuplicate =
    do PutStrLn "no elements in stack"
       stackCalc
  
  tryDiscard : StackIO height
  tryDiscard {height=S k} =
    do Pop
       PutStrLn "discarded"
       stackCalc
  tryDiscard = 
    do PutStrLn "no elements in stack"
       stackCalc
           
  stackCalc : StackIO height
  stackCalc = 
    do
      PutStr "> "
      inp <- GetStr
      case parseInput inp of
        Nothing => do PutStrLn "invalid input"; stackCalc
        (Just (INumber x)) => do Push x; stackCalc
        (Just IAdd) => tryAdd                        
        (Just ISub) => trySub
        (Just IMult) => tryMult
        (Just IDup) => tryDuplicate
        (Just INeg) => tryNeg
        (Just IDisc) => tryDiscard


partial
main : IO ()
main = run forever [] stackCalc
