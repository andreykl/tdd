module Main

import public Lightyear.Core
import public Lightyear.Char
import public Lightyear.Strings
import public Lightyear.Combinators

import DataStore


data Command : (schema : Schema) -> Type where
  Add : SchemaType schema -> Command schema
  Get : Maybe Integer -> Command schema
  Quit : Command schema
  Schemac : Maybe Schema -> Command schema


specialChar : Parser Char
specialChar = do
  c <- anyChar
  case c of
    '"' => pure c
    _   => fail "expected double quotes"

sstringq : Parser (List Char)
sstringq = (char '"' *!> pure []) <|> do
  c <- satisfy (/= '"')
  if c == '\\' 
    then map (::) specialChar <*> sstringq 
    else map (c ::) sstringq

sstring : Parser String
sstring = do
  char '"'
  res <- sstringq
  pure (pack res)


sint : Parser Integer
sint = integer

pschema : Parser (SchemaType schema)
pschema {schema = SString} = sstring
pschema {schema = SInt} = sint
pschema {schema = left .+. right} = 
  do le <- lexeme $ pschema {schema = left}
     comma
     ri <- lexeme $ pschema {schema = right}
     pure (le, ri)

pSInt : Parser Schema
pSInt = do lexeme $ string "Int"
           pure SInt

pSString : Parser Schema
pSString = do lexeme $ string "String"
              pure SString

pschemaType : Parser Schema
pschemaType = do opt comma
                 left <- (pSInt <|> pSString)
                 (do right <- pschemaType
                     pure (left .+. right)) <|> pure left
                 
pcommand : Parser String
pcommand = lexeme $ (string "add") <|> (string "get") <|> (string "quit") <|> (string "schema")

parseCommand : Parser (Command schema)
parseCommand = 
  do scommand <- pcommand 
     case scommand of
       "schema" => (do sc <- pschemaType
                       pure (Schemac $ Just sc))
                   <|> (pure $ Schemac Nothing)
       "add" => do value <- pschema
                   pure (Add value)
       "get" => (do index <- lexeme integer
                    pure (Get $ Just index))
                <|> (pure $ Get Nothing)
       "quit" => pure Quit
                    
displaySchema : SchemaType schema -> String
displaySchema value {schema} with (schema)
  displaySchema value | SString = "\"" ++ value ++ "\""
  displaySchema value | SInt = show value
  displaySchema (a, b) | (x .+. y) = displaySchema a ++ ", " ++ displaySchema b

displayStore : DataStore -> String
displayStore store = foldr (\value, acc => acc ++ displaySchema value ++ "\n") "" (getItems store)

get : Integer -> (store : DataStore) -> Maybe (SchemaType (getSchema store))
get ind store = index <$> (integerToFin ind $ getSize store) <*> (Just $ getItems store)

evalCommand : (store : DataStore) -> Command (getSchema store) -> Maybe (String, DataStore)
evalCommand store (Schemac Nothing) = Just ("Current schema: " ++ show (getSchema store), store)
evalCommand store (Schemac (Just sc)) = 
  case getSize store of
    Z => Just ("OK. New schema: " ++ show sc, empty sc)
    (S k) => Just ("Changing the schema is allowed for empty stores only.", store)             
evalCommand store (Add value) = Just ("OK. Index: " ++ show (getSize store), addToStore store value)
evalCommand store (Get Nothing) = Just (displayStore store, store)
evalCommand store (Get (Just i)) = 
  let 
    res = case (get i store) of
            Nothing => "Invalid index"
            (Just x) => displaySchema x
  in Just (res, store)
evalCommand store Quit = Nothing

driver : DataStore -> IO ()
driver store =
  do putStr "command: "
     input <- getLine
     case parse (parseCommand {schema=getSchema store}) (trim input) of
       (Left l) => do putStrLn "error during parsing command"
                      -- putStrLn l
                      driver store
       (Right c) => do case evalCommand store c of
                         Nothing => pure ()
                         (Just (result, store')) => do putStrLn result
                                                       driver store'

main : IO ()
main = 
  do putStrLn $ "Current schema: " ++ show SString
     driver $ empty SString


-- Local Variables:
-- idris-load-packages: ("lightyear")
-- End:
