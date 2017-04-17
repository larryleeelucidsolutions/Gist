{-
  Synopsis
    Defines a set of functions that can be used to
    manipulate XML documents.
-}
module XML2 where

import List
import XML

-- Accepts an XML element and returns its attributes.
getAttribs :: XmlExp -> [(String, String)]
getAttribs (XElem _ attribs _) = attribs

{-
  Synopsis
    Accepts two arguments: name, an attribute name;
    and elem, an XML element; and returns the
    attribute in elem that has the given name.
-}
getAttrib :: String -> XmlExp -> Maybe String
getAttrib name = lookup name . getAttribs

{-
  Synopsis
    Accepts two XML elements, x and y, and adds y
    to x as a child.
-}
addElem :: XmlExp -> XmlExp -> XmlExp
addElem (XElem name attribs elems) x = XElem name attribs (x:elems)

{-
  Synopsis
    Accepts two arguments: name and elem; and
    returns every child element of elem whose
    tagname equals name.
-}
getElemsByTagName :: String -> XmlExp -> [XmlExp]
getElemsByTagName name = filter ((==) name . tagOf) . elemsOf

{-
  Synopsis
    Accepts two arguments: name, a tag name; and
    elem, an XML element; and returns the first
    child element in elem whose name equals name.
-}
getElemByTagName :: String -> XmlExp -> Maybe XmlExp
getElemByTagName name = find ((==) name . tagOf) . elemsOf

{-
  Synopsis
    Accepts two arguments: name and elem; and
    returns the text value of every child of elem
    whose tag name equals name.
-}
getTextByTagName :: String -> XmlExp -> [String]
getTextByTagName = (.) (map (\x -> textOf [x])) . getElemsByTagName

{-
  Synopsis
    Accepts two arguments: name and elem; and
    removes every child element in elem whose tag
    name equals name.
-}
deleteElemsByTagName :: String -> XmlExp -> XmlExp
deleteElemsByTagName name (XElem name' attribs elems) =
  XElem name' attribs $ filter (not . (==) name . tagOf) elems
