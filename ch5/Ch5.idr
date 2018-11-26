module Main

import Data.Vect

data VectUnknown : Type -> Type where
  MkVect : (len : Nat) -> Vect len a -> VectUnknown a

readVect : IO (n ** Vect n String)
readVect =
  do l <- getLine
     if length l == 0
     then 
       pure (_ ** [])
     else do
       (_ ** vect) <- readVect
       pure (_ ** l :: vect)

zipInputs : IO ()
zipInputs =
  do putStrLn "enter first vector:"
     (n ** vect) <- readVect
     putStrLn "enter second vector:"
     (m ** vect2) <- readVect
     case decEq m n of
       (Yes Refl) => do let v3 = zip vect vect2
                        printLn v3
                     
       (No contra) => do putStrLn "vectors lengths are different"
                         zipInputs
 
readToBlank : IO (List String)
readToBlank = 
  do line <- getLine
     if length line == 0
     then pure []
     else map (line ::) readToBlank

readAndSave : IO ()
readAndSave = 
  do putStrLn "Please enter strings to save (blank line to finish)"
     lines <- readToBlank
     putStr "Please enter a filename: "
     filename <- getLine
     Right h <- writeFile filename (unlines lines)
       | Left err => putStrLn (show err)
     pure ()




readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = 
  do Right h <- openFile filename Read 
     | Left err => do putStrLn (show err)
                      pure (_ ** [])
     readVectFileHelper h
  where
    readVectFileHelper : (h : File) -> IO (n : Nat ** Vect n String)
    readVectFileHelper h = do end <- fEOF h
                              if end
                              then pure (_ ** [])
                              else do Right line <- fGetLine h
                                        | Left err => do putStrLn (show err)
                                                         pure (_ ** [])
                                      (_ ** vect) <- readVectFileHelper h
                                      pure (_ ** line :: vect)
                




