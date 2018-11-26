module Main

import public Lightyear.Core
import public Lightyear.Char
import public Lightyear.Strings
import public Lightyear.Combinators

%default total

data Forever = More (Lazy Forever)

partial
forever : Forever
forever = More forever

data Command : Type -> Type where
  PutStrLn : String -> Command ()
  PutStr : String -> Command ()
  GetLine : Command String
  ReadFile : String -> Command (Either FileError String)
  WriteFile : String -> String -> Command (Either FileError ())

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace Command
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind
  
namespace ConsoleIO
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

runCommand : Command a -> IO a
runCommand (PutStrLn x) = putStrLn x
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (ReadFile filename) = readFile filename
runCommand (WriteFile filename content) = writeFile filename content
runCommand (Pure x) = pure x
runCommand (Bind c k) = do a <- runCommand c
                           runCommand (k a)


data Input = CExit | CCat String | CCopy String String

partial
pcexit : Parser Input
pcexit = do lexeme $ string "exit"
            pure CExit

partial
pfilename : Parser String
pfilename = map pack $ some $ satisfy (/= ' ')

partial
pccat : Parser Input
pccat = do lexeme $ string "cat"
           filename <- pfilename
           pure (CCat filename)

partial           
pccopy : Parser Input
pccopy = do lexeme $ string "copy"
            source <- pfilename
            spaces
            destination <- pfilename
            pure (CCopy source destination)

partial
pcommand : Parser Input
pcommand = pcexit <|> pccat <|> pccopy

partial
readInput : String -> Command (Either String Input)
readInput prompt =
  do PutStr prompt
     commstr <- GetLine
     case parse pcommand commstr of
       (Left l) => Pure (Left $ "Unrecognized command: " ++ commstr)
       (Right r) => Pure (Right r)

partial       
shell : Forever -> ConsoleIO ()
shell (More more) = 
  do case !(readInput "> ") of
       (Left error) => do PutStrLn error
                          shell more
       (Right command) => case command of
                            CExit => Quit ()
                            (CCat filename) => do case !(ReadFile filename) of
                                                    (Left _) => PutStrLn "error while reading file"
                                                    (Right content) => PutStrLn content
                                                  shell more
                            (CCopy src dest) => do case !(ReadFile src) of
                                                     (Left _) => PutStrLn "unable to read source file"
                                                     (Right content) => case !(WriteFile dest content) of
                                                                          (Left _) => PutStrLn "unable to write file"
                                                                          (Right _) => PutStrLn "OK"
                                                   shell more

partial
run : ConsoleIO () -> IO ()
run (Quit _) = putStrLn "bye-bye"
run (Do c cont) = do res <- runCommand c
                     run (cont res)

partial
main : IO ()
main = run (shell forever)

-- Local Variables:
-- idris-load-packages: ("lightyear")
-- End:
