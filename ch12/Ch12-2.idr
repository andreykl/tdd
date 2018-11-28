module Main

%default total

-- record Reader (r : Type) (a : Type) where
--   constructor MkReader
--   RunReader : r -> a

namespace Reader
  data Reader : (r : Type) -> (a : Type) -> Type where
    Pure : a -> Reader r a
    Bind : Reader r a -> (a -> Reader r b) -> Reader r b
    Ask : Reader r r

  (>>=) : Reader r a -> (a -> Reader r b) -> Reader r b
  (>>=) = Bind

  runReader : Reader r a -> r -> a
  runReader (Pure x) _ = x
  runReader (Bind rx f) r = runReader (f (runReader rx r)) r
  runReader Ask r = r

-- tom : Reader String String
-- tom = Bind (Pure "somebody") (\a => 
--  )                             


namespace Writer
  data Writer : logType -> (a : Type) -> Type where
    Pure : a -> Writer (List String) a
    Bind : Writer (List String) a -> (a -> Writer (List String) b) -> Writer (List String) b
    Tell : String -> Writer (List String) ()

  (>>=) : Writer (List String) a -> (a -> Writer (List String) b) -> Writer (List String) b
  (>>=) = Bind
  
  runWriter : Writer (List String) a -> (a, List String)
  runWriter (Tell s) = ((), [s])
  runWriter (Pure x) = (x, [])
  runWriter (Bind wa f) = 
    let
      (va, as) = runWriter wa
      (vb, bs) = runWriter (f va)
    in (vb, bs ++ as)
    
  
  execWriter : Writer (List String) a -> a
  execWriter = fst . runWriter

  tell : (a : String) -> Writer (List String) ()
  tell = Tell

  partial
  gcd : Int -> Int -> Writer (List String) Int
  gcd a 0 = tell ("finished with a = " ++ show a) >>= (\_ => Pure a)
  gcd a k = 
    do tell (show a ++ " `mod` " ++ show k ++ " = " ++ show (a `mod` k))
       gcd k (a `mod` k)

namespace State
  data State : stateType -> Type -> Type where
    Get : State stateType stateType
    Put : stateType -> State stateType ()
    
    Pure : a -> State stateType a
    Bind : State stateType a -> (a -> State stateType b) -> State stateType b

  runState : State stateType a -> stateType -> (a, stateType)
  runState (Pure x) st = (x, st)
  runState Get st = (st, st)
  runState (Put st') _ = ((), st')
  runState (Bind sta f) st = 
    let
      (v', st') = runState sta st
    in runState (f v') st'
      
        
Functor (Reader r) where
  map f r = Bind r (\a => Pure $ f a)

Applicative (Reader r) where
  pure x = Pure x
  (<*>) rf ra = Bind rf (\f => Bind ra (\a => Pure $ f a))

Monad (Reader r) where
  (>>=) = Bind

Functor (Writer (List String)) where
  map f wa = Bind wa (\a => Pure $ f a)

Applicative (Writer (List String)) where
  pure x = Pure x
  (<*>) wf wa = Bind wf (\f => Bind wa (\a => Pure $ f a))

Monad (Writer (List String)) where
  (>>=) = Bind

Functor (State stateType) where
  map f sa = Bind sa (\a => Pure $ f a)

Applicative (State sty) where
  pure = Pure
  (<*>) sf sa = Bind sf (\f => Bind sa (\a => Pure $ f a))

Monad (State sty) where
  (>>=) = Bind
