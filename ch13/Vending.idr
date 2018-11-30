module Main

VendState : Type
VendState = (Nat, Nat)

data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

data MachineCmd : Type -> VendState -> VendState -> Type where
  InsertCoin : MachineCmd () (coins, chocs) (S coins, chocs)
  Vend       : MachineCmd () (S coins, S chocs) (coins, chocs) 
  GetCoins   : MachineCmd () (coins, chocs) (Z, chocs)
  Refill     : (bars : Nat) -> MachineCmd () (Z, chocs) (Z, bars + chocs)

  Display    : String -> MachineCmd () state state
  GetInput   : MachineCmd (Maybe Input) state state

  Pure       : ty -> MachineCmd ty state state
  (>>=)      : MachineCmd a state1 state2 -> (a -> MachineCmd b state2 state3) -> MachineCmd b state1 state3

data MachineIO : VendState -> Type where
  Do : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1

namespace MachineDo
  (>>=) : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1
  (>>=) = Do


mutual
  vend : MachineIO (pounds, chocs)
  vend {pounds = S p} {chocs = S ch} = 
    do Vend
       Display "Enjoy!"
       machineLoop
  vend {pounds = Z} = 
    do Display "Please insert a coin first"
       machineLoop
  vend {chocs = Z} =
    do Display "Sorry,  no more chocolate.."
       machineLoop
  
  refill : Nat -> MachineIO (pounds, chocs)
  refill k {pounds = Z} = do Refill k
                             Display "Refilled"
                             machineLoop

  refill k = do Display "There are coins inserted in machine"
                machineLoop

  machineLoop : MachineIO (pounds, chocs)
  machineLoop = 
    do Just x <- GetInput | Nothing => do Display "Invalid input"
                                          machineLoop
       case x of
         COIN => do InsertCoin
                    machineLoop
         VEND => vend
         CHANGE => do GetCoins
                      Display "Change is returned"
                      machineLoop
         (REFILL k) => refill k
