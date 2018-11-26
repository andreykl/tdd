module Main

palindrome : Nat -> String -> Bool
palindrome len str = if length str < len then False else toLower str == reverse (toLower str)

counts : String -> (Nat, Nat)
counts str = (length $ words str, length str)

top_ten : Ord a => List a -> List a
top_ten = Prelude.List.take 10 . reverse . sort

over_length : Nat -> List String -> Nat
over_length k = length . filter (> k) . map length
-- over_length len xs = foldr (\str, acc => if length str > len then S acc else acc) 0 xs

main : IO ()
main = repl "Enter a string: " (\inp => show (palindrome 0 inp) ++ "\n")
