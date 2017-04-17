{-
  Synopsis
    Defines a collection of functions that can be
    used to split passages into sentences, strip
    out punctuation and special chars, and perform
    other operations that may be needed before the
    input can be tokenized.
-}
module Preprocess where

import Char

{-
  Synopsis
    Accepts a character, x, and returns true iff x
    is a terminal punctuation mark.
-}
isTerminalPunctuation :: Char -> Bool
isTerminalPunctuation x = x == '.' || x == '!' || x == '?'

{-
  Synopsis
    Accepts a string that represents a passage and
    returns a list of the sentences contained
    within it. 
-}
sentences :: String -> [String]
sentences "" = []
sentences (x:xs) =
    if isTerminalPunctuation x || null ys
      then [x] : ys
      else (x:(head ys)):(tail ys)
  where
    ys = sentences xs 

{-
  Synopsis
    Accepts a string and removes all of the
    punctuation marks and special characters.
-}
stripPunctuation :: String -> String
stripPunctuation xs = filter (\x -> isAlpha x || isSpace x) xs

{-
  Synopsis
    Accepts a string, x, and decapitalizes any
    capital letters in x.
-}
decapitalize :: String -> String
decapitalize xs = map toLower xs 
