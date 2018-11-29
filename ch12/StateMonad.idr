module Main

import Control.Monad.State

addIfPositive : Integer -> State Integer Bool
addIfPositive v = do when (v > 0) $
                       do cs <- get
                          put (cs + v)
                     pure (v > 0)

addPositives : List Integer -> State Integer Nat
addPositives xs = do added <- sequence $ map addIfPositive xs
                     pure (length $ filter id added)
