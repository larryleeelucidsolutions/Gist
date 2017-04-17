{-
  Synopsis
    The Interpret module defines a set of functions
    and data types that can be used to interpret
    and represent interpretations of parse trees.
  Note
    Interpretations are represented by collections
    of predicates. For example, the sentence: "The
    blue bird flew away", can be interpreted as
    follows: hasProperty bird blue, actor bird
    flew, actionPreposition flew away.

    The primary idea is that parse trees can be
    represented by sets of predicates. Inferences
    can then be derived from these fundamental
    predicates to build a complete interpretation
    of the given sentence.

    The fundamental predicates are hard-coded and
    describe relations between words within a
    clause. Inferences (rules that generate new
    predicates from existing predicates) can be
    defined dynamically.

    Borrowing ideas from RDF, entities are
    represented using URI's. This ensures that each
    reference is unique across the entire web.
    Since the interpretation module defines
    predicates that describe the relations between
    words within a clause, the URI's generated use
    the following format: <document uri>#<word ref>.
-}
module Interpret where

import Parse
import RDF

-- Defines the gist URI.
gistURI :: String
gistURI = "http://parallel-threads.com/gist#"

-- Represents predicates.
data Predicate = Predicate String [String]

-- Accepts a predicate and returns its name.
predicateName :: Predicate -> String
predicateName (Predicate x _) = x

-- Accepts a predicate and returns its arguments.
predicateArgs :: Predicate -> [String]
predicateArgs (Predicate _ xs) = xs

-- Accepts a terminal token and returns its URI reference.
terminalRef :: Token String -> String
terminalRef x = terminalValue x ++ "_" ++ (show $ terminalPos x)

-- Accepts a word token and returns its literal value.
word :: Token String -> String
word (Nonterminal "word" [[x]]) = terminalValue x

-- Accepts a word token and returns its word.
wordRef :: Token String -> String
wordRef (Nonterminal "word" [[x]]) = terminalRef x

-- Accepts a noun/pronoun token and returns its URI reference.
nounRef :: String -> Token String -> String
nounRef uri (Nonterminal "noun" [[x]]) = uri ++ "noun#" ++ wordRef x
nounRef uri (Nonterminal "pronoun" [[x]]) = uri ++ "pronoun#" ++ wordRef x

-- Accepts an adjective token and returns its URI reference.
adjectiveRef :: String -> Token String -> String
adjectiveRef uri (Nonterminal "adjective" [[x]]) = uri ++ "adjective#" ++ wordRef x

-- Accepts a preposition token and returns its URI reference.
prepositionRef :: String -> Token String -> String
prepositionRef uri (Nonterminal "preposition" [[x]]) = uri ++ "preposition#" ++ word x

-- Accepts a noun phrase token and returns its noun's URI reference.
nounPhraseNounRef :: String -> Token String -> String
nounPhraseNounRef uri (Nonterminal "noun phrase" [[x], _, _]) = nounRef uri x

--
adverbRef :: String -> Token String -> String
adverbRef uri (Nonterminal "adverb" [[x]]) = uri ++ "adverb#" ++ word x

--
verbRef :: String -> Token String -> String
verbRef uri (Nonterminal "verb" [[x]]) = uri ++ "verb#" ++ wordRef x

--
verbPhraseVerbRef :: String -> Token String -> String
verbPhraseVerbRef uri (Nonterminal "verb phrase" [[x], _]) = verbRef uri x

{-
  Synopsis
    Accepts two arguments: uri, the document uri;
    and x, a noun phrase token; and returns a set
    of predicates that describe x.
-}
interpretNounPhrase :: String -> Token String -> [Predicate]
interpretNounPhrase uri (Nonterminal "noun phrase" [[x], as, bs]) =
  let n = nounRef uri x
    in (map (\a -> Predicate (gistURI ++ "Adjective") [n, adjectiveRef uri a]) as) ++
         (concatMap (\(Nonterminal "prepositional phrase" [[u], [v]]) -> (Predicate (prepositionRef uri u) [n, nounPhraseNounRef uri v]):(interpretNounPhrase uri v)) bs)

{-
  Synopsis
-}
interpretVerbPhrase :: String -> Token String -> [Predicate]
interpretVerbPhrase uri (Nonterminal "verb phrase" [[x], as]) =
  let v = verbRef uri x
    in map (\a -> Predicate (gistURI ++ "Adverb") [v, adverbRef uri a]) as

{-
  Synopsis
-}
interpretClause :: String -> Token String -> [Predicate]
interpretClause uri (Nonterminal "clause" [[x], [y], zs]) =
  (concatMap (interpretNounPhrase uri) (x:zs)) ++
  (interpretVerbPhrase uri y) ++
  [Predicate (gistURI ++ "Actor") [verbPhraseVerbRef uri y, nounPhraseNounRef uri x]] ++
  (if null zs
     then []
     else [Predicate (gistURI ++ "DirectObject") [verbPhraseVerbRef uri y, nounPhraseNounRef uri (head zs)]])

{-
  Synopsis
-}
predicateToRDFTriple :: Predicate -> RDFTriple
predicateToRDFTriple (Predicate p [a, b]) = RDFTriple (RDFNode a) (RDFPredicate p Nothing) (RDFNode b)

{-
  Synopsis
-}
interpretationToRDFGraph :: [Predicate] -> RDFGraph
interpretationToRDFGraph predicates = 
  RDFGraph [rdfPrefix, RDFPrefix "gist" gistURI] $ map predicateToRDFTriple predicates
