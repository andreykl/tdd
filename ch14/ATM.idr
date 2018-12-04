module Main

import Data.Vect

data ATMState = Ready | CardInserted | Session
data PINCheck = CorrectPIN | IncorrectPIN

data HasCard : ATMState -> Type where
  HasSession : HasCard Session
  HasCI : HasCard CardInserted

PIN : Type
PIN = Vect 4 Char

data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
  InsertCard : ATMCmd () Ready (const CardInserted)
  EjectCard : {auto prf : HasCard state} -> ATMCmd () state (const Ready)
  GetPIN : ATMCmd PIN CardInserted (const CardInserted)
  CheckPIN : PIN -> ATMCmd PINCheck CardInserted
                                        (\res => case res of
                                                   CorrectPIN => Session
                                                   IncorrectPIN => CardInserted)
  Dispense : Nat -> ATMCmd () Session (const Session)
  GetAmount : ATMCmd Nat st (const st)

  Message : String -> ATMCmd () st (const st)
  
  Pure : (res : ty) -> ATMCmd ty (state_fn res) state_fn
  (>>=) : ATMCmd a state1 state2_fn -> ((res : a) -> ATMCmd b (state2_fn res) state3_fn) -> ATMCmd b state1 state3_fn


testPIN : Vect 4 Char
testPIN = ['1', '2', '3', '4']

readVect : (n : Nat) -> IO (Vect n Char)
readVect Z = pure []
readVect (S k) = (::) <$> getChar <*> (readVect k)


atm : ATMCmd () Ready (const Ready)
atm = do InsertCard
         pin <- GetPIN
         CorrectPIN <- CheckPIN pin | IncorrectPIN => do Message "Pin is wrong"
                                                         EjectCard
         amount <- GetAmount
         Dispense amount
         EjectCard

runATM : ATMCmd res inState outState_fn -> IO res
runATM InsertCard = do putStr "Please insert your card (press enter)"
                       line <- getLine
                       pure ()
runATM EjectCard = do putStrLn "Please take your card"
                      pure ()
runATM GetPIN = do putStr "Your PIN: "
                   readVect 4
runATM (CheckPIN pin) = 
  if pin == testPIN 
     then
       pure CorrectPIN
     else
       pure IncorrectPIN
runATM (Dispense k) = do putStrLn $ "here is " ++ show k
                         pure ()
runATM GetAmount = do putStr "How much would you like? "
                      inp <- getLine
                      pure (cast inp)
runATM (Message msg) = putStrLn msg
runATM (Pure res) = pure res
runATM (x >>= f) = do x' <- runATM x
                      runATM (f x')
