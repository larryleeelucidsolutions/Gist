{-
  Synopsis
    Defines an RDF interface. Gist uses RDF to
    represent semantic networks. It also defines a
    vocabulary whose URI is
      http://parallel-threads.com/gist/
    that defines the predicates used within these
    networks.

  Note
    RDF is a W3 standard that is used to represent
    semantic networks. RDF uses graphs to represent
    semantic information. Each node represents a
    subject. The edges between the nodes represent
    relationships. Subjects and relationships are
    identified using URI references. This allows
    different organizations to unambiguously refer
    to the same subjects and properties/
    relationships across the internet. These
    organizations can define their own subjects/
    attributes/relationships by defining their own
    vocabularies. A vocabulary is simply a set of
    URI references. Each reference denotes a given
    concept, such as a person, a property, or a
    relationship.
-}
module RDF where

import List
import XML
import XML2

-- Represents URIs.
type URI = String

-- Represents RDF Vocabularies.
type RDFVocab = [URI]

-- Represents RDF Nodes.
data RDFNode = RDFNode URI | BlankRDFNode String | LiteralRDFNode String

-- Represents RDF Predicates.
data RDFPredicate = RDFPredicate URI (Maybe String)

getRDFPredicateURI (RDFPredicate uri _) = uri
getRDFPredicateType (RDFPredicate _ x) = x

-- Represents RDF Triples.
data RDFTriple = RDFTriple RDFNode RDFPredicate RDFNode

getRDFTripleSubject   (RDFTriple subject _ _)   = subject
getRDFTriplePredicate (RDFTriple _ predicate _) = predicate
getRDFTripleObject    (RDFTriple _ _ object)    = object

groupRDFTriples :: [RDFTriple] -> [(RDFNode, [RDFTriple])]
groupRDFTriples [] = []
groupRDFTriples (x:xs) = insert x $ groupRDFTriples xs
  where insert x [] = [(getRDFTripleSubject x, [x])]
        insert x (z@(subject, ys):zs) =
          if subject == getRDFTripleSubject x
            then (subject, (x:ys)):zs
            else z:(insert x zs)

-- Represents RDF prefixes.
data RDFPrefix = RDFPrefix String URI

-- The RDF prefix.
rdfPrefix :: RDFPrefix
rdfPrefix = RDFPrefix "rdf" "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

getRDFPrefixName (RDFPrefix name _) = name
getRDFPrefixURI  (RDFPrefix _ uri)  = uri

{-
  Synopsis
    Accepts a uri and a set of RDF prefixes and
    returns the set of prefixes that could be
    applied to the uri.
-}
getRDFPrefixByURI :: URI -> [RDFPrefix] -> Maybe RDFPrefix
getRDFPrefixByURI uri = find $ (flip isPrefixOf) uri . getRDFPrefixURI

{-
  Synopsis
    Accepts an RDP prefix name, and a set of RDF
    prefixes, and returns the prefix that has the
    given name.
-}
getRDFPrefixByName :: String -> [RDFPrefix] -> Maybe RDFPrefix
getRDFPrefixByName name = find $ (==) name . getRDFPrefixName

{-
  Synopsis
    Accepts a set of RDF prefixes and a URI, finds
    the prefix that can be applied to the given
    URI, and returns the result. 
-}
prefixURI :: [RDFPrefix] -> URI -> URI
prefixURI prefixes uri =
  case getRDFPrefixByURI uri prefixes of
    Just (RDFPrefix prefix uri') -> prefix ++ ":" ++ (drop (length uri') uri)
    Nothing -> uri

{-
  Synopsis
    Accepts a set of RDF prefixes and a URI that
    uses a prefix, and replaces the prefix with its
    uri.
-}
getAbsoluteURI :: [RDFPrefix] -> URI -> URI
getAbsoluteURI prefixes uri =
  let (prefixName, (_:fragment)) = break ((==) ':') uri
    in case getRDFPrefixByName prefixName prefixes
         of Just (RDFPrefix _ uri') -> uri' ++ fragment
            Nothing -> error $ "Invalid NS. Missing NS prefix. " ++ uri

-- Represents RDF Graphs.
data RDFGraph = RDFGraph [RDFPrefix] [RDFTriple]

getRDFGraphPrefixes (RDFGraph prefixes _) = prefixes
getRDFGraphTriples  (RDFGraph _ triples)  = triples

getRDFGraphPrefixByURI :: URI -> RDFGraph -> Maybe RDFPrefix
getRDFGraphPrefixByURI uri = getRDFPrefixByURI uri . getRDFGraphPrefixes
