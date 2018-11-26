module Ch1

StringOrInt : (x: Bool) -> Type
StringOrInt x =
  case x of
    False => String
    True  => Int


getStringOrInt : (x : Bool) -> StringOrInt x
getStringOrInt x = 
  case x of
    False => "ninety four"
    True => 94

valueToString : (x: Bool) -> StringOrInt x -> String
valueToString x v = 
  case x of
    True  => cast v
    False => v
    


