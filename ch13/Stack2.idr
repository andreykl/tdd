module Main

import Data.Vect

data Forever = More Forever

partial
forever : Forever
forever = More forever

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () h (S h)
  Pop : StackCmd Integer (S h) h
  Top : StackCmd Integer (S h) (S h)
  
  PutStr : String -> StackCmd () h h
  PutStrLn : String -> StackCmd () h h
  GetStr : StackCmd String h h
  
  Pure : ty -> StackCmd ty h h
  (>>=) : StackCmd a h1 h2 -> (a -> StackCmd b h2 h3) -> StackCmd b h1 h3

runStack : StackCmd ty n hout -> Vect n Integer -> IO (ty, Vect hout Integer)
runStack (Push x) xs = pure ((), x :: xs)
runStack Pop (x :: xs) = pure (x, xs)
runStack Top (x :: xs) = pure (x, x :: xs)
runStack (PutStr x) xs = do putStr x; pure ((), xs)
runStack (PutStrLn x) xs = do putStrLn x; pure ((), xs)
runStack GetStr xs = do s <- getLine; pure (s, xs)
runStack (Pure x) xs = pure (x, xs)
runStack (x >>= f) xs = do (x', xs') <- runStack x xs
                           runStack (f x') xs'

data StackIO : Nat -> Type where
  Do : StackCmd a h1 h2 -> (a -> Inf (StackIO h2)) -> StackIO h1
  
namespace StackDo
  (>>=) : StackCmd a h1 h2 -> (a -> Inf (StackIO h2)) -> StackIO h1
  (>>=) = Do


partial
run : Forever -> Vect height Integer -> StackIO height -> IO ()
run (More frvr) xs (Do scmd f) = do (v', xs') <- runStack scmd xs
                                    run frvr xs' (f v')


data Input : Type where
  IPush : Integer -> Input
  IAdd : Input
  IDuplicate : Input
  
data UnaryOperation = UnOpDuplicate

parseInput : String -> Maybe Input
parseInput "" = Nothing
parseInput "add" = Just IAdd
parseInput "duplicate" = Just IDuplicate
parseInput str = if all isDigit $ unpack str then Just (IPush $ cast str) else Nothing

UnaryOpOutHeight : UnaryOperation -> Nat -> Nat
UnaryOpOutHeight UnOpDuplicate h = S (S h)

unaryOpByName : (op : UnaryOperation) -> StackCmd String (S h) (UnaryOpOutHeight op h)
unaryOpByName UnOpDuplicate = do v <- Top
                                 Push v
                                 Pure $ "Duplicated: " ++ show v

mutual
  tryBiOp : String -> (Integer -> Integer -> Integer) -> StackIO height
  tryBiOp _ op {height=S (S h)} = do a <- Pop
                                     b <- Pop
                                     let res = a `op` b
                                     Push res
                                     PutStrLn $ show res
                                     stackCalc
  tryBiOp str _                 = do PutStrLn $ "unable execute " ++ str ++ ": fewer then two elements on stack"
                                     stackCalc

  tryUnOp : String -> UnaryOperation -> StackIO height
  tryUnOp _ opname {height=S h} = do res <- unaryOpByName opname
                                     PutStrLn res
                                     stackCalc
  tryUnOp str _                 = do PutStrLn $ "unable to execute " ++ str ++ ": no elements on stack"
                                     stackCalc
                                     


  stackCalc : StackIO height
  stackCalc =
    do PutStr "> "
       inp <- GetStr
       case parseInput inp of
         Nothing => do PutStrLn "Invalid input"
                       stackCalc
         (Just (IPush x)) => do Push x; stackCalc
         (Just IAdd) => tryBiOp "add" (+)
         (Just IDuplicate) => tryUnOp "duplicate" UnOpDuplicate

partial
main : IO ()
main = run forever [] stackCalc
