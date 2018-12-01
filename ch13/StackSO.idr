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

data StackIO : Nat -> Type where
  Do :    StackCmd a h1 h2 -> (a -> Inf (StackIO h2)) -> StackIO h1
  QuitCmd : (a : Nat) -> StackIO a

namespace StackDo
  (>>=) : StackCmd a h1 h2 -> (a -> Inf (StackIO h2)) -> StackIO h1
  (>>=) = Do

data Input : Type where
  INumber : Integer -> Input
  IAdd : Input
  IDuplicate : Input
  IDiscard : Input

parseInput : String -> Maybe Input
parseInput str = 
  case str of
    "" => Nothing
    "add" => Just IAdd
    "duplicte" => Just IDuplicate
    "discard" => Just IDiscard
    _      => if all isDigit $ unpack str then Just (INumber $ cast str) else Nothing
    
  

run : Forever -> Vect n Integer -> StackIO n -> IO ()
run _          _    (QuitCmd a) = pure ()
run (More far) stck (Do sa f)   = do (a', stck') <- runStack stck sa 
                                     run far stck' (f a')
                                     
biOp : (Integer -> Integer -> Integer) -> StackCmd String (S (S height)) (S height)
biOp op = do a <- Pop 
             b <- Pop
             let res = a `op` b
             Push res
             Pure $ show res

discardUnOp : StackCmd String (S height) height
discardUnOp = do v <- Pop
                 Pure $ "Discarded: " ++ show v

duplicateUnOp : StackCmd String (S height) (S (S height))
duplicateUnOp = do v <- Top
                   Push v
                   Pure $ "Duplicated: " ++ show v

mutual
  tryBiOp : String -> (Integer -> Integer -> Integer) -> StackIO hin
  tryBiOp _      op {hin=S (S k)} = do res <- biOp op
                                       PutStrLn res
                                       stackCalc
  tryBiOp opName _                = do PutStrLn $
                                         "Unable to execute operation " ++ opName ++ ": fewer then two items on stack."
                                       stackCalc

  tryUnOp : Show a => String -> StackCmd a hIn hOut -> StackIO hIn
  tryUnOp _ op   {hIn=S h} = do res <- op
                                PutStrLn $ show res
                                stackCalc
  tryUnOp opName _         = do PutStrLn $ 
                                  "Unable to execute " ++ opName ++ " operation: no elements on stack."
                                stackCalc


  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 inp <- GetStr
                 case parseInput inp of
                   Nothing => do PutStrLn "invalid input"; stackCalc
                   (Just (INumber x)) => do Push x; stackCalc
                   (Just IAdd) => tryBiOp "add" (+)
                   (Just IDuplicate) => ?holedup
                   (Just IDiscard) => ?holedisc -- tryUnOp "discard" discardUnOp

partial
main : IO ()
main = run forever [] stackCalc
