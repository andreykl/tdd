module Main

import Prelude.Nat
import Data.Vect
import Data.So

%default total

infixr 5 .+.

data Schema = SString 
            | SInt
            | SChar
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore store x = MkData _ _ (addToData x (items store)) where
  addToData : SchemaType (schema store) -> Vect m (SchemaType (schema store)) -> Vect (S m) (SchemaType (schema store))
  addToData x [] = [x]
  addToData x (y :: xs) = y :: addToData x xs

{-
sumInputs : (s : Integer) -> (input : String) -> Maybe (String, Integer)
sumInputs s input = 
  let val = cast input in
    if val < 0
       then Nothing
       else
         let newval = s + val in
           Just ("You entered : " ++ show val ++ ", current sum : " ++ show newval ++ "\n", newval)
-}
           
data Command : Schema -> Type where
  SetSchema : (newschema : Schema) -> Command schema
  Add : (SchemaType schema) -> Command schema
  Get : Maybe Integer -> Command schema
  Quit : Command schema
  Size : Command schema
  -- | Search String

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString inp = getQuoted (unpack inp) where
  getQuoted : List Char -> Maybe (String, String)
  getQuoted ('"' :: xs) =
    case span (/= '"') xs of
      (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
      _                     => Nothing
  getQuoted _ = Nothing    
parsePrefix SInt inp = 
  case span isDigit inp of
    ("", _) => Nothing
    (int, rest) => Just (cast int, ltrim rest)
parsePrefix SChar inp =
  case unpack inp of
    (x :: xs) => Just (x, ltrim $ pack xs)
    _         => Nothing
parsePrefix (x .+. y) inp = 
  do (px, rest) <- parsePrefix x inp
     (py, rest') <- parsePrefix y rest
     pure ((px, py), rest')
     
parseSchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseSchema schema x = 
  do (res, "") <- parsePrefix schema x | Nothing
     pure res

parseNewSchema : List String -> Maybe Schema
parseNewSchema ("String" :: rest) = 
  case rest of
    [] => Just SString
    _  => map (SString .+.) (parseNewSchema rest)
parseNewSchema ("Int" :: rest) = 
  case rest of
    [] => Just SInt
    _  => map (SInt .+.) (parseNewSchema rest)
parseNewSchema ("Char" :: rest) = 
  case rest of
    [] => Just SChar
    _  => map (SChar .+.) (parseNewSchema rest)
parseNewSchema _ = Nothing
    

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand sc "schema" args = map SetSchema (parseNewSchema $ words args)
parseCommand sc "size"   args = Just Size
--parseCommand "search" args = if length args > 0
--                             then (Just $ Search args)
--                             else Nothing
parseCommand sc "add"    args = map Add (parseSchema sc args)
parseCommand sc "get"    args = let args' = unpack args
                                in if isNil args'
                                      then (Just $ Get Nothing)
                                      else
                                        if all isDigit args'
                                          then Just $ Get (Just $ cast args)
                                          else Nothing
parseCommand sc "quit" _      = Just Quit
parseCommand sc _      _      = Nothing

parse : (schema : Schema) -> String -> Maybe (Command schema)
parse schema input = 
  let (cmd, arg) = span (/= ' ') input 
  in parseCommand schema cmd (ltrim arg)

display : SchemaType schema -> String
display {schema = SString} rec = "\"" ++ rec ++ "\""
display {schema = SInt} rec = show rec
display {schema = SChar} rec = "'" ++ cast rec ++ "'"
display {schema = (x .+. y)} (iteml, itemr) = display iteml ++ ", " ++ display itemr

getEntry : (store: DataStore) -> Integer -> Maybe (String, DataStore)
getEntry store k = case integerToFin k (size store) of
  Nothing  => Just ("ID is out of range\n", store)
  (Just x) => Just (display (index x (items store)) ++ "\n", store)
  
predicate : {size: Nat} -> String -> (Fin size, String) -> Bool
predicate s1 (i, s) = isInfixOf s1 (toLower s)

noResults : String -> String
noResults s = "No results found for query '" ++ s ++ "'."

-- extractLTE1Size : {size: Nat} -> (So (1 <= size)) -> LTE 1 size
-- extractLTE1Size {size = Z} Oh impossible
-- extractLTE1Size {size = (S _)} _ = LTESucc LTEZero

vtake : (n : Nat) -> Stream a -> Vect n a
vtake Z xs = []
vtake (S k) (x::xs) =  x :: vtake k xs

entriesToString : Vect n (Int, SchemaType schema) -> String
entriesToString xs = buildHelper xs "" where
  buildHelper : Vect n (Int, SchemaType _) -> String -> String
  buildHelper [] acc = acc
  buildHelper ((id, x) :: xs) acc = buildHelper xs (acc ++ show id ++ ": " ++ display x ++ "\n")

getEntries : (store: DataStore) -> Maybe (String, DataStore)
getEntries store = 
  let 
    its = items store
    sz = size store
    entries = if sz > 0
              then entriesToString {schema=schema store} (zip (vtake sz [0..]) its)
              else "No entries found" ++ "\n"
              
              {-case isLTE 1 sz of
                   (Yes (LTESucc x)) => entriesToString {schema=schema store} {n=} its
                   (No contra) => 
                   -}
  in Just (entries, store)


{-
searchEntries : (store : DataStore) -> (s : String) -> Maybe (String, DataStore)
searchEntries store s = 
  let
    searchResults = case choose (1 <= size) of
      (Left l) => let
          -- v2 = vtake size [0..]
          pred = predicate {size=size} (toLower s)
          (n ** foundItems) = Vect.filter pred (zip (range {len=size}) items)
          results = case n of
            Z => noResults s 
            (S m) => buildSearchResults {n=m} foundItems
        in results
      (Right r) => 
        noResults s

  in 
    Just (searchResults ++ "\n", store) 
-}

updateSchema : (schema : Schema) -> DataStore
updateSchema schema = MkData schema _ []

storeDriver : DataStore -> String -> Maybe (String, DataStore) 
storeDriver store input =
  case parse (schema store) input of
    Nothing        => Just ("Invalid command\n", store)
    (Just (SetSchema newschema)) => if size store > 0
                                    then Just ("Can set schema for empty store only!\n", store)
                                    else Just ("OK\n", updateSchema newschema)
    (Just (Add x)) => Just ("ID: " ++ show (size store) ++ "\n", addToStore store x)
    (Just (Get mk)) => 
      case mk of
        (Just k) => getEntry store k
        Nothing  => getEntries store
    (Just Size)    => Just ("Size of store: " ++ (show (size store)) ++ "\n", store)
    -- (Just (Search s)) => searchEntries store s
    (Just Quit)    => Nothing

partial
main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt) _ []) "Command: " storeDriver

