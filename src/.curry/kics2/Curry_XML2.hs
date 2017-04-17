{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module Curry_XML2 (d_C_getAttribs, d_C_getAttrib, nd_C_getAttrib, d_C_addElem, d_C_getElemsByTagName, nd_C_getElemsByTagName, d_C_getElemByTagName, nd_C_getElemByTagName, d_C_getTextByTagName, nd_C_getTextByTagName, d_C_deleteElemsByTagName) where

import Basics
import qualified Curry_List
import qualified Curry_Prelude
import qualified Curry_XML
d_C_getAttribs :: Curry_XML.C_XmlExp -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List Curry_Prelude.C_Char))
d_C_getAttribs x1 x3500 = case x1 of
     (Curry_XML.C_XElem x2 x3 x4) -> x3
     (Curry_XML.Choice_C_XmlExp x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_getAttribs x1002 x3500) (d_C_getAttribs x1003 x3500)
     (Curry_XML.Choices_C_XmlExp x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_getAttribs z x3500) x1002
     (Curry_XML.Guard_C_XmlExp x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_getAttribs x1002) $! (addCs x1001 x3500))
     (Curry_XML.Fail_C_XmlExp x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getAttrib :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_XML.C_XmlExp -> ConstStore -> Curry_Prelude.C_Maybe (Curry_Prelude.OP_List Curry_Prelude.C_Char)
d_C_getAttrib x1 x3500 = Curry_Prelude.d_OP_dot (Curry_Prelude.d_C_lookup x1) d_C_getAttribs x3500

nd_C_getAttrib :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> IDSupply -> ConstStore -> Func Curry_XML.C_XmlExp (Curry_Prelude.C_Maybe (Curry_Prelude.OP_List Curry_Prelude.C_Char))
nd_C_getAttrib x1 x3000 x3500 = let
     x2000 = x3000
      in (seq x2000 (Curry_Prelude.nd_OP_dot (wrapDX id (Curry_Prelude.d_C_lookup x1)) (wrapDX id d_C_getAttribs) x2000 x3500))

d_C_addElem :: Curry_XML.C_XmlExp -> Curry_XML.C_XmlExp -> ConstStore -> Curry_XML.C_XmlExp
d_C_addElem x1 x2 x3500 = case x1 of
     (Curry_XML.C_XElem x3 x4 x5) -> Curry_XML.C_XElem x3 x4 (Curry_Prelude.OP_Cons x2 x5)
     (Curry_XML.Choice_C_XmlExp x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_addElem x1002 x2 x3500) (d_C_addElem x1003 x2 x3500)
     (Curry_XML.Choices_C_XmlExp x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_addElem z x2 x3500) x1002
     (Curry_XML.Guard_C_XmlExp x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_addElem x1002 x2) $! (addCs x1001 x3500))
     (Curry_XML.Fail_C_XmlExp x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getElemsByTagName :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_XML.C_XmlExp -> ConstStore -> Curry_Prelude.OP_List Curry_XML.C_XmlExp
d_C_getElemsByTagName x1 x3500 = Curry_Prelude.d_OP_dot (Curry_Prelude.d_C_filter (Curry_Prelude.d_OP_dot (Curry_Prelude.d_OP_eq_eq x1) Curry_XML.d_C_tagOf x3500)) Curry_XML.d_C_elemsOf x3500

nd_C_getElemsByTagName :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> IDSupply -> ConstStore -> Func Curry_XML.C_XmlExp (Curry_Prelude.OP_List Curry_XML.C_XmlExp)
nd_C_getElemsByTagName x1 x3000 x3500 = let
     x2002 = x3000
      in (seq x2002 (let
          x2001 = leftSupply x2002
          x2000 = rightSupply x2002
           in (seq x2001 (seq x2000 (Curry_Prelude.nd_OP_dot (wrapNX id (Curry_Prelude.nd_C_filter (Curry_Prelude.nd_OP_dot (wrapDX id (Curry_Prelude.d_OP_eq_eq x1)) (wrapDX id Curry_XML.d_C_tagOf) x2000 x3500))) (wrapDX id Curry_XML.d_C_elemsOf) x2001 x3500)))))

d_C_getElemByTagName :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_XML.C_XmlExp -> ConstStore -> Curry_Prelude.C_Maybe Curry_XML.C_XmlExp
d_C_getElemByTagName x1 x3500 = Curry_Prelude.d_OP_dot (Curry_List.d_C_find (Curry_Prelude.d_OP_dot (Curry_Prelude.d_OP_eq_eq x1) Curry_XML.d_C_tagOf x3500) x3500) Curry_XML.d_C_elemsOf x3500

nd_C_getElemByTagName :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> IDSupply -> ConstStore -> Func Curry_XML.C_XmlExp (Curry_Prelude.C_Maybe Curry_XML.C_XmlExp)
nd_C_getElemByTagName x1 x3000 x3500 = let
     x2004 = x3000
      in (seq x2004 (let
          x2003 = leftSupply x2004
          x2002 = rightSupply x2004
           in (seq x2003 (seq x2002 (Curry_Prelude.nd_OP_dot (let
               x2001 = leftSupply x2002
               x2000 = rightSupply x2002
                in (seq x2001 (seq x2000 (Curry_List.nd_C_find (Curry_Prelude.nd_OP_dot (wrapDX id (Curry_Prelude.d_OP_eq_eq x1)) (wrapDX id Curry_XML.d_C_tagOf) x2000 x3500) x2001 x3500)))) (wrapDX id Curry_XML.d_C_elemsOf) x2003 x3500)))))

d_C_getTextByTagName :: ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_XML.C_XmlExp -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_List Curry_Prelude.C_Char)
d_C_getTextByTagName x3500 = Curry_Prelude.d_OP_dot (Curry_Prelude.d_OP_dot (Curry_Prelude.d_C_map d_OP_getTextByTagName_dot___hash_lambda1)) d_C_getElemsByTagName x3500

nd_C_getTextByTagName :: IDSupply -> ConstStore -> Func (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Func Curry_XML.C_XmlExp (Curry_Prelude.OP_List (Curry_Prelude.OP_List Curry_Prelude.C_Char)))
nd_C_getTextByTagName x3000 x3500 = let
     x2000 = x3000
      in (seq x2000 (Curry_Prelude.nd_OP_dot (wrapNX id (Curry_Prelude.nd_OP_dot (wrapNX id (Curry_Prelude.nd_C_map (wrapDX id d_OP_getTextByTagName_dot___hash_lambda1))))) (wrapNX id nd_C_getElemsByTagName) x2000 x3500))

d_OP_getTextByTagName_dot___hash_lambda1 :: Curry_XML.C_XmlExp -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_OP_getTextByTagName_dot___hash_lambda1 x1 x3500 = Curry_Prelude.d_C_apply (Curry_XML.d_C_textOf x3500) (Curry_Prelude.OP_Cons x1 Curry_Prelude.OP_List) x3500

d_C_deleteElemsByTagName :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> Curry_XML.C_XmlExp -> ConstStore -> Curry_XML.C_XmlExp
d_C_deleteElemsByTagName x1 x2 x3500 = case x2 of
     (Curry_XML.C_XElem x3 x4 x5) -> Curry_Prelude.d_OP_dollar (acceptCs id (Curry_XML.C_XElem x3 x4)) (Curry_Prelude.d_C_filter (Curry_Prelude.d_OP_dot Curry_Prelude.d_C_not (Curry_Prelude.d_OP_dot (Curry_Prelude.d_OP_eq_eq x1) Curry_XML.d_C_tagOf x3500) x3500) x5 x3500) x3500
     (Curry_XML.Choice_C_XmlExp x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_deleteElemsByTagName x1 x1002 x3500) (d_C_deleteElemsByTagName x1 x1003 x3500)
     (Curry_XML.Choices_C_XmlExp x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_deleteElemsByTagName x1 z x3500) x1002
     (Curry_XML.Guard_C_XmlExp x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_deleteElemsByTagName x1 x1002) $! (addCs x1001 x3500))
     (Curry_XML.Fail_C_XmlExp x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo
