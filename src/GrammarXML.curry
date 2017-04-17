{-
  Synopsis
    This module defines a set of functions that can
    be used to parse XML documents that represent
    grammars.
-}
module GrammarXML (parseGrammar, parseGrammarFile) where

import AllSolutions
import Maybe
import Parse
import Parser
import XML
import XML2

{-
  Synopsis
    Accepts an XML element that should represent a
    pattern token parameter and succeeds iff it
    does. Otherwise, returns an error that
    describes the problem.
-}
checkPatternTokenParam :: XmlExp -> Success
checkPatternTokenParam x =
  let name = tagOf x
    in if name == "param"
         then success
         else error $ "Invalid pattern token parameter element. Invalid tag name (" ++ name ++ ")."

{-
  Synopsis
    Returns a parser that accepts an XML element
    that represents a grammar token.
-}
patternTokenParam :: ParserRep (Maybe String) XmlExp
patternTokenParam x (token:tokens) | checkPatternTokenParam token & x =:= getAttrib "name" token = tokens

{-
  Synopsis
    Accepts an XML element that should represent a
    pattern token and succeeds iff it does.
    Otherwise, returns an error that describes the
    problem.
-}
checkPatternToken :: XmlExp -> Success
checkPatternToken x |
  let name   = tagOf x
      prefix = "Invalid pattern token element. "
    in (name == "token"             || (error $ prefix ++ "Invalid tag name (" ++ name ++ ").")) &&
       (isJust (getAttrib "type" x) || (error $ prefix ++ "The 'type' attribute is missing."))
  = success

{-
  Synopsis
    Returns a parser that accepts an XML element
    that represents a pattern token.
-}
patternToken :: ParserRep PToken XmlExp
patternToken x (token:tokens)
  | checkPatternToken token &
    star patternTokenParam as (getElemsByTagName "param" token) =:= [] &
    x =:= PToken (fromJust $ getAttrib "type" token) (getAttrib "name" token) as
  = tokens
  where as free

{-
  Synopsis
    Accepts an XML element that should represent a
    template parameter value and succeeds iff it
    does. Otherwise, returns an error describing
    the problem.
-}
checkVar :: XmlExp -> Success
checkVar x |
  let name   = tagOf x
      prefix = "Invalid var element. "
    in (name == "var"               || (error $ prefix ++ "Invalid tag name (" ++ name ++ ").")) &&
       (isJust (getAttrib "name" x) || (error $ prefix ++ "The 'name' attribute is missing."))
  = success

{-
  Synopsis
    Returns a parser that accepts an XML element
    that represents a template token parameter
    value and returns the value name.
-}
var :: ParserRep String XmlExp
var x (token:tokens) | checkVar token & x =:= (fromJust $ getAttrib "name" token) = tokens

{-
  Synopsis
    Accepts an XML element that should represent a
    template token parameter and succeeds iff it
    does. Otherwise, returns an error that
    describes the problem.
-}
checkTemplateTokenParam :: XmlExp -> Success
checkTemplateTokenParam x =
  let name = tagOf x
    in if name == "param"
         then success
         else error $ "Invalid template token parameter element. Invalid tag name (" ++ name ++ ")."

{-
  Synopsis
    Returns a parser that accepts an XML element
    that represents a template token parameter and
    returns the names of its parameter values.
-}
templateTokenParam :: ParserRep [String] XmlExp
templateTokenParam x (token:tokens) | checkTemplateTokenParam token & star var x (getElemsByTagName "var" token) =:= [] = tokens

{-
  Synopsis
    Accepts an XML element that should represent a
    template token and succeeds iff it does.
    Otherwise, returns an error that describes the
    problem.
-}
checkTemplateToken :: XmlExp -> Success
checkTemplateToken x |
  let name = tagOf x
      prefix = "Invalid template token element. "
    in (name == "token"             || (error $ prefix ++ "Invalid tag name (" ++ name ++ ").")) &&
       (isJust (getAttrib "type" x) || isJust (getAttrib "name" x) || (error $ prefix ++ "The 'type' attribute is missing."))
  = success

{-
  Synopsis
    Returns a parser that accepts an XML element
    that represents a template token and returns an
    equivalent TemplateToken.
-}
templateToken :: ParserRep TToken XmlExp
templateToken x (token:tokens)
  | checkTemplateToken token &
    star templateTokenParam as (getElemsByTagName "param" token) =:= [] &
    x =:= case getAttrib "name" token of
            Just a  -> PTokenRef a
            Nothing -> TToken (fromJust $ getAttrib "type" token) as
  = tokens
  where as free

{-
  Synopsis
    Returns a parser that parses an XML element
    that represents a pattern.
-}
pattern :: ParserRep [PToken] XmlExp
pattern x (token:tokens)
  | star patternToken x (getElemsByTagName "token" token) =:= []
  = tokens

{-
  Synopsis
    Returns a parser that parses an XML element
    that represents a template.
-}

template :: ParserRep [TToken] XmlExp
template x (token:tokens)
  | star templateToken x (getElemsByTagName "token" token) =:= []
  = tokens 

-- template x (token:tokens) | templateToken x (getElemsByTagName "token" token) =:= [] = tokens

{-
  Synopsis
    Accepts an XML element that should represent a
    grammar rule and succeeds iff it does.
    Otherwise, returns an error that describes the
    problem.
-}
checkRule :: XmlExp -> Success
checkRule x |
  let name = tagOf x
      prefix = "Invalid rule element. "
    in (name == "rule"                         || (error $ prefix ++ "Invalid tag name (" ++ name ++ ").")) &&
       (isJust (getElemByTagName "pattern" x)  || (error $ prefix ++ "The 'pattern' element is missing.")) &&
       (isJust (getElemByTagName "template" x) || (error $ prefix ++ "The 'template' element is missing."))
  = success

{-
  Synopsis
    Returns a parser that parses an XML element
    that represents a grammar rule.
-}
rule :: ParserRep Rule XmlExp
rule x (token:tokens)
  | checkRule token &
    pattern  a [fromJust $ getElemByTagName "pattern" token] =:= [] &
    template b [fromJust $ getElemByTagName "template" token] =:= [] &
    x =:= Rule a b
  = tokens
  where a, b free

{-
  Synopsis
    Accepts an XML element that should represent a
    grammar and succeeds iff it does. Otherwise,
    returns an error that describes the problem.
-}
checkGrammar :: XmlExp -> Success
checkGrammar x =
  let name = tagOf x
    in if name == "grammar"
         then success
         else error $ "Invalid grammar element. Invalid tag name ("++ name ++ ")."

{-
  Synopsis
    Returns a parser that parses an XML element
    that represents a grammar.
-}
grammar :: ParserRep [Rule] XmlExp
grammar x (token:tokens)
  | checkGrammar token &
    star rule x (getElemsByTagName "rule" token) =:= []
  = tokens 

{-
  Synopsis
    Accepts an XML element that represents a
    grammar and parses it.
-}
parseGrammar :: XmlExp -> [Rule]
parseGrammar x = grammar a [x] =:= [] &> a where a free

{-
  Synopsis
    Accepts a filename, parses the referenced file,
    and returns the grammar described therein.
-}
parseGrammarFile :: String -> IO [Rule] 
parseGrammarFile x = (readXmlFile x >>= getOneValue . parseGrammar) >>= return . fromJust
