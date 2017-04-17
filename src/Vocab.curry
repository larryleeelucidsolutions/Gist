{-
  Synopsis
    Contains definitions that can be used to
    represent and manipulate vocabularies.
-}
module Vocab where

import BinarySort
import List
import Maybe
import XML
import XML2

data Pos = Adjective | Adverb | Article | Noun | Preposition | Pronoun | Verb

posToString :: Pos -> String
posToString x | x == Adjective   = "adjective"
              | x == Adverb      = "adverb"
              | x == Article     = "article"
              | x == Noun        = "noun"
              | x == Preposition = "preposition"
              | x == Pronoun     = "pronoun"
              | x == Verb        = "verb"

posFromString :: String -> Pos
posFromString x | x == "adjective"   = Adjective
                | x == "adverb"      = Adverb
                | x == "article"     = Article
                | x == "noun"        = Noun
                | x == "preposition" = Preposition
                | x == "pronoun"     = Pronoun
                | x == "verb"        = Verb

data Word = Word String [Pos]

wordName :: Word -> String
wordName (Word name _) = name

wordPos :: Word -> [Pos]
wordPos (Word _ poss) = poss

isPos' :: Pos -> Word -> Bool
isPos' x = elem x . wordPos

{-
  Synopsis
    Represents vocabulary lists.
  Note
    The words listed in a vocabulary must be in
    alphabetical order.
-}
type Vocab = [Word]

{-
  Synopsis
    Accepts two arguments, vocab and word. If vocab
    does not contain an entry for word, adds word
    to vocab. Otherwise, adds the parts of speech
    listed in word to the corresponding entry in
    vocab.
-}
addWord :: Vocab -> Word -> Vocab
addWord vocab x@(Word name ps) =
  let (as, mw, bs) = split' ((==) name . wordName)
                            ((>)  name . wordName)
                            vocab
    in as ++ [case mw of
                Just (Word _ ps') -> Word name (nub (ps ++ ps'))
                Nothing           -> Word name ps] ++ bs

{-
  Synopsis
    Accepts two arguments, x and y, and adds the
    words listed in x to y. If any word in x is
    already listed in y, adds the parts of speech
    listed in x's entry to y's.
-}
addWords :: Vocab -> Vocab -> Vocab
addWords [] xs     = xs
addWords (x:xs) ys = addWords xs $## addWord ys x

{-
  Synopsis
    Accepts two arguments, vocab and word, and
    returns the word entry for word in vocab. If
    word does not have an entry, returns Nothing.
-}
getWord :: Vocab -> String -> Maybe Word
getWord vocab name = find ((==) name . wordName) vocab

{-
  Synopsis
    Accepts three arguments, pos, vocab, and word,
    and returns true iff word has pos in vocab.
-}
isPos :: Pos -> Vocab -> String -> Bool
isPos pos vocab name = fromMaybe False $ getWord vocab name >>- Just . isPos' pos

{-
  Synopsis
    Accepts two arguments, vocab and word, and
    returns true iff word is an adjective in vocab.
-}
isAdjective :: Vocab -> String -> Bool
isAdjective = isPos Adjective

isAdverb :: Vocab -> String -> Bool
isAdverb = isPos Adverb

isArticle :: Vocab -> String -> Bool
isArticle = isPos Article 

isPreposition :: Vocab -> String -> Bool
isPreposition = isPos Preposition

isPronoun :: Vocab -> String -> Bool
isPronoun = isPos Pronoun

removeSuffix :: String -> String -> String
removeSuffix suffix x = reverse $ f (reverse suffix) $ reverse x 
  where
    f suffix x = if isPrefixOf suffix x
                   then drop (length suffix) x
                   else x

isNoun :: Vocab -> String -> Bool
isNoun vocab x = isPos Noun vocab x ||
                 isPos Noun vocab (removeSuffix "s"  x) ||
                 isPos Noun vocab (removeSuffix "es" x)


isVerb :: Vocab -> String -> Bool
isVerb vocab x = isPos Verb vocab x ||
                 isPos Verb vocab (removeSuffix "s" x) ||
                 isPos Verb vocab (removeSuffix "ed" x)

{-
  Synopsis
    Accepts a single argument, name, and loads the
    vocabulary words stored in the file named name.
-}
loadVocab :: String -> IO Vocab
loadVocab name =
  readXmlFile name >>= return . map f . getElemsByTagName "word"
    where
      f (XElem "word" xs _) = Word (fromJust $ lookup "name" xs) $
                                map posFromString $ words $ fromJust $ lookup "pos" xs

vocabToXML :: Vocab -> XmlExp
vocabToXML = XElem "vocab" [] . map f
  where f (Word name pos) = XElem "word" [("name", name), ("pos", unwords $ map posToString pos)] []

writeVocab :: String -> Vocab -> IO ()
writeVocab filename = writeXmlFile filename . vocabToXML
