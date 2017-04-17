{-
  Synopsis
    Gist is a natural language analyzer. It accepts
    text passages, parses them, and returns an
    interpretation. These interpretations are
    represented by RDF graphs and can be visualized
    using standard RDF tools.
-}

import AllSolutions
import GrammarXML
import Interpret
import Maybe
import Parse
import Preprocess
import Profile
import RDF
import RDFTurtle
import System
import Tokenize
import Vocab

main :: IO ()
main =
  do
    arguments <- getArgs
    if any ((==) "-h") arguments
      then putStrLn $
             "  Synopsis                                        \n" ++
             "    Gist [options] <filename> <passage>           \n" ++
             "  Gist is a natural language analyzer. It accepts \n" ++
             "  text passages, parses them, and returns an      \n" ++
             "  interpretation. These interpretations are       \n" ++
             "  represented by RDF graphs and can be visualized \n" ++
             "  using standard RDF tools.                       \n" ++
             "                                                  \n" ++
             "  Notes                                           \n" ++
             "  RDF graphs are output using the RDF Turtle      \n" ++
             "  format. The standard file extension for Turtle  \n" ++
             "  files is 'ttl'.                                 \n" ++
             "                                                  \n" ++
             "  Options:                                        \n" ++
             "  -h) Displays this help message.                 \n" ++
             "                                                  \n" ++
             "  Examples:                                       \n" ++
             "    Gist 'tmp.ttl' 'The dog ate the cat.'         \n" ++
             "  Gist will interpret the given sentence, create  \n" ++
             "  a semantic network that represents its          \n" ++
             "  interpretation, and render that network as an   \n" ++
             "  RDF Turtle file named 'tmp.ttl'.                \n" ++
             "                                                  \n" ++
             "  Authors:                                        \n" ++
             "    Larry D. Lee jr <llee@parallel-threads.com>   \n" ++
             "    Bree Katz <bkk9@georgetown.edu>               \n"
      else
        if 2 == length arguments
          then let [filename, passage] = arguments
                 in
                   do putStrLn "Parsing Vocab File"
                      vocab <- profileTime $## loadVocab "vocab.xml"
                      putStrLn "Parsing Grammar File"
                      grammar <- profileTime $## parseGrammarFile "grammar.xml"
                      putStrLn "Tokenizing"
                      tokenizations <- profileTime $## getAllValues $ tokenize vocab passage
                      putStrLn "Parsing"
                      parsings <- profileTime $ return $## parseTokenizations grammar tokenizations
                      putStrLn "Interpreting"
                      interpretation <- return $## concatMap (interpretClause ("http://" ++ filename ++ "/")) $ parsings
                      putStrLn "Writing to RDF"
                      writeFile filename $
                        RDFGraphToString 100 $
                        interpretationToRDFGraph $
                        interpretation
          else putStrLn "Error: Invalid command line arguments."

{-
  Returns true iff the parse tree represented by
  xs is complete.
-}
isComplete :: [a] -> Bool
isComplete xs = length xs == 1

{-
  Returns true iff the given token represents
  a clause.
-}
isClause :: Token a -> Bool
isClause (Nonterminal x _) = x == "clause"

{-
  Accepts a grammar and a sequence of tokens
  that represents a clause and returns the set
  of complete parsings for the clause.
-}
parseClause :: Grammar -> [Token a] -> [Token a]
parseClause grammar tokens =
  filter isClause $ map head $ filter isComplete $ parse grammar tokens

{-
  Accepts a grammar and a set of possible
  tokenizations and returns the set of possible
  parsings of the given passage.
-}
parsePassage :: Grammar -> [[Token a]] -> [Token a]
parsePassage grammar passage = concatMap (parseClause grammar) passage

{-
  Accepts a grammar and a set of possible
  tokenizations and returns the set of possible
  parsings of the given passage.
-}
parseTokenizations :: Grammar -> [[[Token a]]] -> [Token a]
parseTokenizations grammar xss = fst $ foldl (\(xs, n) -> \ys -> let m = length ys in if n >= m then (xs, n) else (ys, m)) ([], 0) $ map (parsePassage grammar) xss
