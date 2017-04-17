{-
  Synopsis
    Defines a set of functions that translate
    predicate sets into RDF Turtle graphs.
-}
module RDFTurtle where

import Maybe
import Pretty
import RDF

URIToDoc :: [RDFPrefix] -> URI -> Doc
URIToDoc prefixes uri =
  if isJust $ getRDFPrefixByURI uri prefixes
    then text $ prefixURI prefixes uri
    else angles $ text uri

RDFNodeToDoc :: [RDFPrefix] -> RDFNode -> Doc
RDFNodeToDoc prefixes (RDFNode uri) = URIToDoc prefixes uri
RDFNodeToDoc _ (BlankRDFNode x) = angles $ text x
RDFNodeToDoc _ (LiteralRDFNode x) = dquotes $ text x

RDFPredicateToDoc :: [RDFPrefix] -> RDFPredicate -> Doc
RDFPredicateToDoc prefixes (RDFPredicate uri _) = URIToDoc prefixes uri
RDFTripleToDoc :: [RDFPrefix] -> RDFTriple -> Doc
RDFTripleToDoc prefixes (RDFTriple subject predicate object) =
  RDFNodeToDoc prefixes subject <+> RDFPredicateToDoc prefixes predicate <+> RDFNodeToDoc prefixes object <+> dot

RDFPrefixToDoc :: RDFPrefix -> Doc
RDFPrefixToDoc (RDFPrefix name uri) =
  text "@prefix" <+> text name <> colon <+> angles (text uri) <+> dot

RDFGraphToDoc :: RDFGraph -> Doc
RDFGraphToDoc (RDFGraph prefixes triples) =
  (vcat $ map RDFPrefixToDoc prefixes) <$$> linebreak <>
  (vcat $ map (RDFTripleToDoc prefixes) triples)

RDFGraphToString :: Int -> RDFGraph -> String
RDFGraphToString width = pretty width . RDFGraphToDoc
