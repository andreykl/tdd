module Main

-- data GuessCmd : Type -> Nat -> Nat -> Type where
--   Try : Integer -> GuessCmd Ordering (S k) k
  
--   Pure : ty -> GuessCmd ty st st
--   (>>=) : GuessCmd a st1 st2 -> (a -> GuessCmd b st2 st3) -> GuessCmd b st1 st3
  
-- threeGuesses: GuessCmd () 3 0
-- threeGuesses = do Try 10
--                   Try 20
--                   Try 15
--                   Pure ()

data Matter = Solid | Liquid | Gas


data MatterCmd : Type -> Matter -> Matter -> Type where
  Melt : MatterCmd () Solid Liquid
  Boil : MatterCmd () Liquid Gas
  Condense : MatterCmd () Gas Liquid
  Freeze : MatterCmd () Liquid Solid
  
  Pure : ty -> MatterCmd ty st st
  (>>=) : MatterCmd a st1 st2 -> (a -> MatterCmd b st2 st3) -> MatterCmd b st1 st3
  
iceSteam : MatterCmd () Solid Gas
iceSteam = do Melt
              Boil

steamIce : MatterCmd () Gas Solid
steamIce = do Condense
              Freeze


