module Main

VendState : Type
VendState = (Nat, Nat)

data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

data CoinResult = Inserted | Rejected

data MachineCmd : (ty : Type) -> VendState -> (ty -> VendState) -> Type where
  InsertCoin : MachineCmd CoinResult (coins, chocs)
                                     (\res => case res of
                                                Inserted => (S coins, chocs)
                                                Rejected => (coins, chocs))
  Vend       : MachineCmd () (S coins, S chocs) (const (coins, chocs))
  GetCoins   : MachineCmd () (coins, chocs) (const (Z, chocs))
  Refill     : (bars : Nat) -> MachineCmd () (Z, chocs) (const (Z, bars + chocs))

  Display    : String -> MachineCmd () state (const state)
  GetInput   : MachineCmd (Maybe Input) state (const state)

  Pure       : (a : ty) -> MachineCmd ty (state_fn a) state_fn
  (>>=)      : MachineCmd a state1 state2_fn -> ((res : a) -> MachineCmd b (state2_fn res) state3_fn) -> MachineCmd b state1 state3_fn

data MachineIO : VendState -> Type where
  Do : MachineCmd a state1 state2_fn -> ((res : a) -> Inf (MachineIO (state2_fn res))) -> MachineIO state1

namespace MachineDo
  (>>=) : MachineCmd a state1 state2_fn -> ((res : a) -> Inf (MachineIO (state2_fn res))) -> MachineIO state1
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
         COIN => do Inserted <- InsertCoin 
                      | Rejected => do Display "something is wrong with coin, sorry"
                                       machineLoop
                    Display "coin accepted"
                    machineLoop
         VEND => vend
         CHANGE => do GetCoins
                      Display "Change is returned"
                      machineLoop
         (REFILL k) => refill k
