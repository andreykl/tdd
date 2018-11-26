module State

data State : (stateType : Type) -> Type -> Type where
  Get : State stateType stateType
  Put : stateType -> State stateType ()
  
  Pure : ty -> State stateType ty
  Bind : State stateType a -> (a -> State stateType b) -> State stateType b

Functor (State stateType) where
  map f st = Bind st (\a => Pure (f a))

Applicative (State stateType) where
  pure x = Pure x
  (<*>) x y = Bind x (\f => map f y)

Monad (State stateType) where
  (>>=) = Bind

runState : State stateType a -> stateType -> (stateType, a)
runState Get st = (st, st)
runState (Put x) st = (x, ())
runState (Pure x) st = (st, x)
runState (Bind x f) st = let (st', x') = runState x st in runState (f x') st'

get : State a a
get = Get

put : a -> State a ()
put = Put


addIfPositive : (val : Integer) -> State Integer Bool
addIfPositive val = let pos = val > 0 in
                      do when pos $
                              do c <- get
                                 put (c + val)
                         pure pos


addPositives : List Integer -> (Integer, Nat)
addPositives xs = runState (do bools <- traverse addIfPositive xs
                               pure (length (filter id bools)))
                           0
