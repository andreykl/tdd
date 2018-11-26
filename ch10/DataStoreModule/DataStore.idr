module DataStore

import Data.Vect
import Data.Vect.Views

infixl 5 .+.

public export
data Schema : Type where
  SString : Schema
  SInt : Schema
  (.+.) : Schema -> Schema -> Schema

export
Show Schema where
  show SString = "String"
  show SInt = "Int"
  show (x .+. y) = show x ++ ", " ++ show y

public export  
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Integer
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

export
record DataStore where
  constructor MkStore
  schema : Schema
  size : Nat   
  items : Vect size (SchemaType schema)

export
getSchema : DataStore -> Schema
getSchema store = schema store

export
addToStore : (store : DataStore) -> SchemaType (getSchema store) -> DataStore
addToStore (MkStore schema size items) value = MkStore schema _  (value :: items)

export 
getSize : DataStore -> Nat
getSize store = size store

public export
data StoreView : (store: DataStore) -> Type where
  SNil : StoreView (MkStore _ _ [])
  SAdd : (rec : StoreView store) -> StoreView (addToStore store value)

export
storeView : (store : DataStore) -> StoreView store
storeView (MkStore schema Z []) = SNil
storeView (MkStore schema _ (x :: xs)) = SAdd (storeView (MkStore schema _ xs))


addToStorePreserveSchemaType : (store : DataStore) -> (value : SchemaType (getSchema store)) -> (getSchema (addToStore store value)) = (getSchema store)
addToStorePreserveSchemaType (MkStore schema size items) _ = Refl

addToStoreSuccSize : (store : DataStore) -> (value : SchemaType (getSchema store)) -> getSize (addToStore store value) = (getSize store) + 1
addToStoreSuccSize (MkStore schema size items) _ = rewrite plusCommutative size 1 in Refl



export
getItems : (store: DataStore) -> Vect (getSize store) (SchemaType (getSchema store))
getItems store = getItemsHelper store [] where
  getItemsHelper : (store': DataStore) -> Vect n (SchemaType (getSchema store')) -> Vect (n + getSize store') (SchemaType (getSchema store'))
  getItemsHelper {n} store xs with (storeView store)
    getItemsHelper {n} (MkStore schema Z []) xs | SNil = rewrite plusZeroRightNeutral n in xs
    getItemsHelper {n} (addToStore st value) xs | (SAdd rec) = 
      let 
        xs' = the (Vect n (SchemaType (schema st))) (rewrite sym (addToStorePreserveSchemaType st value) in xs)
        ih = getItemsHelper st (value :: xs') | rec 
      in rewrite addToStoreSuccSize st value 
        in rewrite plusCommutative (getSize st) 1 
          in rewrite sym (plusSuccRightSucc n (getSize st)) 
            in rewrite addToStorePreserveSchemaType st value in ih


{-
  getItems (addToStore store value) ys | (SAdd view) = 
    let
      its = (getItems store | view) ++ [value]
    in rewrite addToStoreSuccSize {store=store} {value=value} 
       in rewrite addToStorePreserveSchemaType {store=store} {value=value} 
          in its
-}

export
empty : Schema -> DataStore
empty schema = MkStore schema Z []

public export
testSchema : Schema
testSchema = SInt .+. SString

export
testStore : DataStore
testStore = empty testSchema

