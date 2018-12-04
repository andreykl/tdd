data Access = LoggedOut | LoggedIn
data PwdCheck = PWCorrect | PWIncorrect

data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
  Password : String -> ShellCmd PwdCheck LoggedOut
                                         (\res => case res of
                                                    PWCorrect => LoggedIn
                                                    PWIncorrect => LoggedOut)
  Logout : ShellCmd () LoggedIn (const LoggedOut)
  GetSecret : ShellCmd String LoggedIn (const LoggedIn)
  
  PutStr : String -> ShellCmd () st (const st)
  Pure : (x : ty) -> ShellCmd ty (state_fn x) state_fn
  (>>=) : ShellCmd a state1 state_fn2 -> ((x : a) -> ShellCmd b (state_fn2 x) state_fn3) -> ShellCmd b state1 state_fn3


session : ShellCmd () LoggedOut (const LoggedOut)
session = do PWCorrect <- Password "wurzel"
                  | PWIncorrect => PutStr "Wrong password"
             msg <- GetSecret
             PutStr ("Secret code: " ++ show msg ++ "\n")
             Logout

-- sessionBad : ShellCmd () LoggedOut (const LoggedOut)
-- sessionBad = do Password "wurzel"
--                 msg <- GetSecret
--                 PutStr ("Secret code: " ++ show msg ++ "\n")
--                 Logout

-- noLogout : ShellCmd () LoggedOut (const LoggedOut)
-- noLogout = do Correct <- Password "wurzel"
--                  | Incorrect => PutStr "Wrong password"
--               msg <- GetSecret
--               PutStr ("Secret code: " ++ show msg ++ "\n")
