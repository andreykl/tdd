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
  data Writer : Type -> Type -> Type where
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
  gcd a 0 = 
    do tell ("finished with a = " ++ show a)
       Pure a
  gcd a k = 
    do tell (show a ++ " `mod` " ++ show k ++ " = " ++ show (a `mod` k))
       gcd k (a `mod` k)

namespace State
  data State : stateType -> Type -> Type where
    Get : State stateType stateType
    Put : stateType -> State stateType ()
    Bind : State stateType a -> (a -> State stateType b) -> State stateType b
    
