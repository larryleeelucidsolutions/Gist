{-
  Synopsis
    The Tokenize module defines a collection of
    functions that can be used to tokenize strings.
-}
module Tokenize (tokenize) where

import Parse
import Preprocess
import Vocab

{-
  Synopsis
    Accepts a vocabulary, v, and a string, x, that
    represents a word, and returns a token that
    represents x using v.
-}
tokenizeWord :: Vocab -> Int -> String -> Token String
tokenizeWord vocab n x | isAdjective   vocab x = Nonterminal "adjective"   [[Nonterminal "word" [[Terminal x n]]]]
tokenizeWord vocab n x | isAdverb      vocab x = Nonterminal "adverb"      [[Nonterminal "word" [[Terminal x n]]]]
tokenizeWord vocab n x | isArticle     vocab x = Nonterminal "article"     [[Nonterminal "word" [[Terminal x n]]]]
tokenizeWord vocab n x | isNoun        vocab x = Nonterminal "noun"        [[Nonterminal "word" [[Terminal x n]]]]
tokenizeWord vocab n x | isPreposition vocab x = Nonterminal "preposition" [[Nonterminal "word" [[Terminal x n]]]]
tokenizeWord vocab n x | isPronoun     vocab x = Nonterminal "pronoun"     [[Nonterminal "word" [[Terminal x n]]]]
tokenizeWord vocab n x | isVerb        vocab x = Nonterminal "verb"        [[Nonterminal "word" [[Terminal x n]]]]
tokenizeWord vocab n x | not (isAdjective   vocab x) &&
                         not (isAdverb      vocab x) &&
                         not (isArticle     vocab x) &&
                         not (isPreposition vocab x) &&
                         not (isPronoun     vocab x) &&
                         not (isNoun        vocab x) &&
                         not (isVerb        vocab x) = Nonterminal "word" [[Terminal x n]]

{-
  Synopsis
    Accepts a vocabulary, v, and a string, x, that
    represents a passage, splits x into sentences
    and tokenizes the words using v.
-}
tokenize :: Vocab -> String -> [[Token String]]
tokenize vocab = f 0 . map words . map stripPunctuation . sentences . decapitalize
  where f _ [] = []
        f n ([]:xs) = [] : (f n xs)
        f n ((x:xs):yss) = let (as:bss) = f (n + 1) (xs:yss)
                             in (((tokenizeWord vocab n x):as):bss)
