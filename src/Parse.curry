{-
  Synopsis
    The Parse Module defines a collection of functions that can
    be used to parse text using Curry's Parser Combinator
    library.
-}
module Parse where

import Maybe
import Parser

-- Represents parse trees.
data Token a = Terminal a Int | Nonterminal String [[Token a]]

-- Accepts a terminal token and returns its value.
terminalValue :: Token a -> a
terminalValue (Terminal x _) = x

-- Accepts a terminal token and returns its position.
terminalPos :: Token a -> Int
terminalPos (Terminal _ x) = x

-- Represents pattern tokens.
data PToken = PToken String (Maybe String) [Maybe String]

-- Represents patterns.
type Pattern = [PToken]

-- Represents template tokens.
data TToken = TToken String [[String]] | PTokenRef String

-- Represents templates.
type Template = [TToken]

-- Represents grammar rules.
data Rule = Rule Pattern Template

-- Represents grammars.
type Grammar = [Rule]

-- Represents pattern/template variable bindings.
type Binding a = (String, [Token a])

-- Represents pattern/template variable bindings.
type Bindings a = [Binding a]

{-
  Accepts a variable name and a list of variable
  bindings and returns the set of values bound to
  the named variable.
-}
getBinding :: String -> Bindings a -> [Token a]
getBinding x = fromMaybe (error "") . lookup x


{-
  Accepts a variable name and a list of bindings
  and returns the value bound for the named variable.
-}
getSingleBinding :: String -> Bindings a -> Token a
getSingleBinding x bindings = let as = getBinding x bindings
                       in if null as
                            then error $ "[getSingleBinding] Error: " ++ x ++ " is an unbound variable."
                            else head as

{-
  Auxiliary function that replaes fromMaybe for
  older versions of Curry.
-}
ifMaybe :: Bool -> a -> Maybe a
ifMaybe x y = if x then Just y else Nothing

{-
  Accepts a grammar pattern token and an input token
  and returns the bindings needed to unify them.
-}
bindPatternToken :: PToken -> Token a -> Maybe [Binding a]
bindPatternToken _ (Terminal _ _) = Nothing
bindPatternToken (PToken x y zs) a@(Nonterminal b css) =
  ifMaybe (x == b) (f ((y, [a]):(zip zs css)))
  where f [] = []
        f ((Nothing, _):xs) = f xs
        f ((Just a, bs):xs) = (a, bs):(f xs)

{-
  Accepts a grammar pattern and a sequence of tokens
  and returns the variable bindings needed to unify
  the pattern with the sequence.
-}
bindPattern :: Pattern -> [Token a] -> Maybe ([Binding a], [Token a])
bindPattern [] xs         = Just ([], xs)
bindPattern (_:_) []      = Nothing
bindPattern (x:xs) (a:as) =
  bindPattern xs as >>-
    (\(bindings, remainingTokens) -> bindPatternToken x a >>-
      (\bindings' -> Just (bindings ++ bindings', remainingTokens)))

{-
  Accepts a single template token and a set of
  variable bindings and returns the token that
  would result from appling the variable bindings
  in the template token.
-}
instantiateTemplateToken :: TToken -> [Binding a] -> Token a
instantiateTemplateToken (PTokenRef x) bindings = getSingleBinding x bindings
instantiateTemplateToken (TToken x yss) bindings = Nonterminal x $ map (concatMap (\y -> getBinding y bindings)) yss

{-
  Accepts a grammar template and a set of variable
  bindings and returns the set of token sequences
  that would result from substituting the variable
  bindings into the template.
-}
instantiate :: Template -> [Binding a] -> [Token a]
instantiate template bindings = map (\x -> instantiateTemplateToken x bindings) template

{-
  Accepts a single grammar rule and a sequence
  of tokens and attempts to parse the first
  clause or sentence in the sequence using the rule. 
-}
reduceHeadUsingRule :: Rule -> [Token a] -> Maybe [Token a]
reduceHeadUsingRule (Rule pattern template) tokens =
  bindPattern pattern tokens >>-
    (\(bindings, remainingTokens) -> Just $ (instantiate template bindings) ++ remainingTokens)

{-
  Accepts a grammer and a sequence of tokens
  and attempts to parse the first clause or
  sentence within the seqence.
-}
reduceHead :: Grammar -> [Token a] -> [[Token a]]
reduceHead rules tokens = mapMaybe ((flip reduceHeadUsingRule) tokens) rules

{-
  Accepts a grammar and a sequence of tokens
  and returns a list of the possible parsings.
-}
reduce :: Grammar -> [Token a] -> [[Token a]]
reduce _ [] = []
reduce grammar tokens@(token:remainingTokens) = (reduceHead grammar tokens) ++ (map (token:) $ reduce grammar remainingTokens)

{-
  An auxiliary function that accepts a grammar,
  a set of potential parsings, and a set of
  possible continuations; and uses the grammar
  to generate a list of valid parsings. 
-}
parse' :: Grammar -> [[Token a]] -> [[Token a]] -> [[Token a]]
parse' _ parsings [] = parsings
parse' grammar parsings (x:xs)
  | elem x parsings = parse' grammar parsings xs
  | otherwise = let ys = reduce grammar x
                  in parse' grammar (x:parsings) (xs ++ ys)

{-
  Accepts a grammer and a sequence of tokens
  and parses these tokens into a series of
  statments using the provided grammar.
-}
parse :: Grammar -> [Token a] -> [[Token a]]
parse grammar tokens = parse' grammar [] [tokens]
