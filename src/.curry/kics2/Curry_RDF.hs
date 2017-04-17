{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module Curry_RDF (C_RDFNode (..), C_RDFPredicate (..), C_RDFTriple (..), C_RDFPrefix (..), C_RDFGraph (..), C_URI, C_RDFVocab, d_C_getRDFPredicateURI, d_C_getRDFPredicateType, d_C_getRDFTripleSubject, d_C_getRDFTriplePredicate, d_C_getRDFTripleObject, d_C_groupRDFTriples, d_C_rdfPrefix, d_C_getRDFPrefixName, d_C_getRDFPrefixURI, d_C_getRDFPrefixByURI, nd_C_getRDFPrefixByURI, d_C_getRDFPrefixByName, nd_C_getRDFPrefixByName, d_C_prefixURI, d_C_getAbsoluteURI, d_C_getRDFGraphPrefixes, d_C_getRDFGraphTriples, d_C_getRDFGraphPrefixByURI, nd_C_getRDFGraphPrefixByURI) where

import Basics
import qualified Curry_List
import qualified Curry_Prelude
import qualified Curry_XML
import qualified Curry_XML2
type C_URI = Curry_Prelude.OP_List Curry_Prelude.C_Char

type C_RDFVocab = Curry_Prelude.OP_List (Curry_Prelude.OP_List Curry_Prelude.C_Char)

data C_RDFNode
     = C_RDFNode (Curry_Prelude.OP_List Curry_Prelude.C_Char)
     | C_BlankRDFNode (Curry_Prelude.OP_List Curry_Prelude.C_Char)
     | C_LiteralRDFNode (Curry_Prelude.OP_List Curry_Prelude.C_Char)
     | Choice_C_RDFNode Cover ID C_RDFNode C_RDFNode
     | Choices_C_RDFNode Cover ID ([C_RDFNode])
     | Fail_C_RDFNode Cover FailInfo
     | Guard_C_RDFNode Cover Constraints C_RDFNode

instance Show C_RDFNode where
  showsPrec d (Choice_C_RDFNode cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_RDFNode cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_RDFNode cd c e) = showsGuard d cd c e
  showsPrec _ (Fail_C_RDFNode cd info) = showChar '!'
  showsPrec _ (C_RDFNode x1) = (showString "(RDFNode") . ((showChar ' ') . ((shows x1) . (showChar ')')))
  showsPrec _ (C_BlankRDFNode x1) = (showString "(BlankRDFNode") . ((showChar ' ') . ((shows x1) . (showChar ')')))
  showsPrec _ (C_LiteralRDFNode x1) = (showString "(LiteralRDFNode") . ((showChar ' ') . ((shows x1) . (showChar ')')))


instance Read C_RDFNode where
  readsPrec d s = (readParen (d > 10) (\r -> [ (C_RDFNode x1,r1) | (_,r0) <- readQualified "RDF" "RDFNode" r, (x1,r1) <- readsPrec 11 r0]) s) ++ ((readParen (d > 10) (\r -> [ (C_BlankRDFNode x1,r1) | (_,r0) <- readQualified "RDF" "BlankRDFNode" r, (x1,r1) <- readsPrec 11 r0]) s) ++ (readParen (d > 10) (\r -> [ (C_LiteralRDFNode x1,r1) | (_,r0) <- readQualified "RDF" "LiteralRDFNode" r, (x1,r1) <- readsPrec 11 r0]) s))


instance NonDet C_RDFNode where
  choiceCons = Choice_C_RDFNode
  choicesCons = Choices_C_RDFNode
  failCons = Fail_C_RDFNode
  guardCons = Guard_C_RDFNode
  try (Choice_C_RDFNode cd i x y) = tryChoice cd i x y
  try (Choices_C_RDFNode cd i xs) = tryChoices cd i xs
  try (Fail_C_RDFNode cd info) = Fail cd info
  try (Guard_C_RDFNode cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_RDFNode cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_RDFNode cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_RDFNode cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_RDFNode cd i _) = error ("RDF.RDFNode.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_RDFNode cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_RDFNode cd c e) = f cd c e
  match _ _ _ _ _ f x = f x


instance Generable C_RDFNode where
  generate s = Choices_C_RDFNode defCover (freeID [1,1,1] s) [(C_RDFNode (generate (leftSupply s))),(C_BlankRDFNode (generate (leftSupply s))),(C_LiteralRDFNode (generate (leftSupply s)))]


instance NormalForm C_RDFNode where
  ($!!) cont (C_RDFNode x1) cs = ((\y1 cs -> cont (C_RDFNode y1) cs) $!! x1) cs
  ($!!) cont (C_BlankRDFNode x1) cs = ((\y1 cs -> cont (C_BlankRDFNode y1) cs) $!! x1) cs
  ($!!) cont (C_LiteralRDFNode x1) cs = ((\y1 cs -> cont (C_LiteralRDFNode y1) cs) $!! x1) cs
  ($!!) cont (Choice_C_RDFNode cd i x y) cs = nfChoice cont cd i x y cs
  ($!!) cont (Choices_C_RDFNode cd i xs) cs = nfChoices cont cd i xs cs
  ($!!) cont (Guard_C_RDFNode cd c e) cs = guardCons cd c ((cont $!! e) (addCs c cs))
  ($!!) _ (Fail_C_RDFNode cd info) _ = failCons cd info
  ($##) cont (C_RDFNode x1) cs = ((\y1 cs -> cont (C_RDFNode y1) cs) $## x1) cs
  ($##) cont (C_BlankRDFNode x1) cs = ((\y1 cs -> cont (C_BlankRDFNode y1) cs) $## x1) cs
  ($##) cont (C_LiteralRDFNode x1) cs = ((\y1 cs -> cont (C_LiteralRDFNode y1) cs) $## x1) cs
  ($##) cont (Choice_C_RDFNode cd i x y) cs = gnfChoice cont cd i x y cs
  ($##) cont (Choices_C_RDFNode cd i xs) cs = gnfChoices cont cd i xs cs
  ($##) cont (Guard_C_RDFNode cd c e) cs = guardCons cd c ((cont $## e) (addCs c cs))
  ($##) _ (Fail_C_RDFNode cd info) _ = failCons cd info
  ($!<) cont (C_RDFNode x1) = (\y1 -> cont (C_RDFNode y1)) $!< x1
  ($!<) cont (C_BlankRDFNode x1) = (\y1 -> cont (C_BlankRDFNode y1)) $!< x1
  ($!<) cont (C_LiteralRDFNode x1) = (\y1 -> cont (C_LiteralRDFNode y1)) $!< x1
  ($!<) cont (Choice_C_RDFNode cd i x y) = nfChoiceIO cont cd i x y
  ($!<) cont (Choices_C_RDFNode cd i xs) = nfChoicesIO cont cd i xs
  ($!<) cont x = cont x
  searchNF search cont (C_RDFNode x1) = search (\y1 -> cont (C_RDFNode y1)) x1
  searchNF search cont (C_BlankRDFNode x1) = search (\y1 -> cont (C_BlankRDFNode y1)) x1
  searchNF search cont (C_LiteralRDFNode x1) = search (\y1 -> cont (C_LiteralRDFNode y1)) x1
  searchNF _ _ x = error ("RDF.RDFNode.searchNF: no constructor: " ++ (show x))


instance Unifiable C_RDFNode where
  (=.=) (C_RDFNode x1) (C_RDFNode y1) cs = (x1 =:= y1) cs
  (=.=) (C_BlankRDFNode x1) (C_BlankRDFNode y1) cs = (x1 =:= y1) cs
  (=.=) (C_LiteralRDFNode x1) (C_LiteralRDFNode y1) cs = (x1 =:= y1) cs
  (=.=) _ _ _ = Fail_C_Success defCover defFailInfo
  (=.<=) (C_RDFNode x1) (C_RDFNode y1) cs = (x1 =:<= y1) cs
  (=.<=) (C_BlankRDFNode x1) (C_BlankRDFNode y1) cs = (x1 =:<= y1) cs
  (=.<=) (C_LiteralRDFNode x1) (C_LiteralRDFNode y1) cs = (x1 =:<= y1) cs
  (=.<=) _ _ _ = Fail_C_Success defCover defFailInfo
  bind i (C_RDFNode x2) = ((i :=: (ChooseN 0 1)):(concat [(bind (leftID i) x2)]))
  bind i (C_BlankRDFNode x2) = ((i :=: (ChooseN 1 1)):(concat [(bind (leftID i) x2)]))
  bind i (C_LiteralRDFNode x2) = ((i :=: (ChooseN 2 1)):(concat [(bind (leftID i) x2)]))
  bind i (Choice_C_RDFNode cd j x y) = [(ConstraintChoice cd j (bind i x) (bind i y))]
  bind i (Choices_C_RDFNode cd j@(FreeID _ _) xs) = bindOrNarrow i cd j xs
  bind i (Choices_C_RDFNode cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (bind i) xs))]
  bind _ (Choices_C_RDFNode cd i _) = error ("RDF.RDFNode.bind: Choices with ChoiceID: " ++ (show i))
  bind _ (Fail_C_RDFNode cd info) = [(Unsolvable info)]
  bind i (Guard_C_RDFNode cd c e) = (getConstrList c) ++ (bind i e)
  lazyBind i (C_RDFNode x2) = [(i :=: (ChooseN 0 1)),((leftID i) :=: (LazyBind (lazyBind (leftID i) x2)))]
  lazyBind i (C_BlankRDFNode x2) = [(i :=: (ChooseN 1 1)),((leftID i) :=: (LazyBind (lazyBind (leftID i) x2)))]
  lazyBind i (C_LiteralRDFNode x2) = [(i :=: (ChooseN 2 1)),((leftID i) :=: (LazyBind (lazyBind (leftID i) x2)))]
  lazyBind i (Choice_C_RDFNode cd j x y) = [(ConstraintChoice cd j (lazyBind i x) (lazyBind i y))]
  lazyBind i (Choices_C_RDFNode cd j@(FreeID _ _) xs) = lazyBindOrNarrow i cd j xs
  lazyBind i (Choices_C_RDFNode cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (lazyBind i) xs))]
  lazyBind _ (Choices_C_RDFNode cd i _) = error ("RDF.RDFNode.lazyBind: Choices with ChoiceID: " ++ (show i))
  lazyBind _ (Fail_C_RDFNode cd info) = [(Unsolvable info)]
  lazyBind i (Guard_C_RDFNode cd c e) = (getConstrList c) ++ [(i :=: (LazyBind (lazyBind i e)))]


instance Curry_Prelude.Curry C_RDFNode where
  (=?=) (Choice_C_RDFNode cd i x y) z cs = narrow cd i ((x Curry_Prelude.=?= z) cs) ((y Curry_Prelude.=?= z) cs)
  (=?=) (Choices_C_RDFNode cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.=?= y) cs) xs
  (=?=) (Guard_C_RDFNode cd c e) y cs = guardCons cd c ((e Curry_Prelude.=?= y) (addCs c cs))
  (=?=) (Fail_C_RDFNode cd info) _ _ = failCons cd info
  (=?=) z (Choice_C_RDFNode cd i x y) cs = narrow cd i ((z Curry_Prelude.=?= x) cs) ((z Curry_Prelude.=?= y) cs)
  (=?=) y (Choices_C_RDFNode cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.=?= x) cs) xs
  (=?=) y (Guard_C_RDFNode cd c e) cs = guardCons cd c ((y Curry_Prelude.=?= e) (addCs c cs))
  (=?=) _ (Fail_C_RDFNode cd info) _ = failCons cd info
  (=?=) (C_RDFNode x1) (C_RDFNode y1) cs = (x1 Curry_Prelude.=?= y1) cs
  (=?=) (C_BlankRDFNode x1) (C_BlankRDFNode y1) cs = (x1 Curry_Prelude.=?= y1) cs
  (=?=) (C_LiteralRDFNode x1) (C_LiteralRDFNode y1) cs = (x1 Curry_Prelude.=?= y1) cs
  (=?=) _ _ _ = Curry_Prelude.C_False
  (<?=) (Choice_C_RDFNode cd i x y) z cs = narrow cd i ((x Curry_Prelude.<?= z) cs) ((y Curry_Prelude.<?= z) cs)
  (<?=) (Choices_C_RDFNode cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.<?= y) cs) xs
  (<?=) (Guard_C_RDFNode cd c e) y cs = guardCons cd c ((e Curry_Prelude.<?= y) (addCs c cs))
  (<?=) (Fail_C_RDFNode cd info) _ _ = failCons cd info
  (<?=) z (Choice_C_RDFNode cd i x y) cs = narrow cd i ((z Curry_Prelude.<?= x) cs) ((z Curry_Prelude.<?= y) cs)
  (<?=) y (Choices_C_RDFNode cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.<?= x) cs) xs
  (<?=) y (Guard_C_RDFNode cd c e) cs = guardCons cd c ((y Curry_Prelude.<?= e) (addCs c cs))
  (<?=) _ (Fail_C_RDFNode cd info) _ = failCons cd info
  (<?=) (C_RDFNode x1) (C_RDFNode y1) cs = (x1 Curry_Prelude.<?= y1) cs
  (<?=) (C_RDFNode _) (C_BlankRDFNode _) _ = Curry_Prelude.C_True
  (<?=) (C_RDFNode _) (C_LiteralRDFNode _) _ = Curry_Prelude.C_True
  (<?=) (C_BlankRDFNode x1) (C_BlankRDFNode y1) cs = (x1 Curry_Prelude.<?= y1) cs
  (<?=) (C_BlankRDFNode _) (C_LiteralRDFNode _) _ = Curry_Prelude.C_True
  (<?=) (C_LiteralRDFNode x1) (C_LiteralRDFNode y1) cs = (x1 Curry_Prelude.<?= y1) cs
  (<?=) _ _ _ = Curry_Prelude.C_False


instance Coverable C_RDFNode where
  cover (C_RDFNode x1) = C_RDFNode (cover x1)
  cover (C_BlankRDFNode x1) = C_BlankRDFNode (cover x1)
  cover (C_LiteralRDFNode x1) = C_LiteralRDFNode (cover x1)
  cover (Choice_C_RDFNode cd i x y) = Choice_C_RDFNode (incCover cd) i (cover x) (cover y)
  cover (Choices_C_RDFNode cd i xs) = Choices_C_RDFNode (incCover cd) i (map cover xs)
  cover (Fail_C_RDFNode cd info) = Fail_C_RDFNode (incCover cd) info
  cover (Guard_C_RDFNode cd c e) = Guard_C_RDFNode (incCover cd) c (cover e)


data C_RDFPredicate
     = C_RDFPredicate (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.C_Maybe (Curry_Prelude.OP_List Curry_Prelude.C_Char))
     | Choice_C_RDFPredicate Cover ID C_RDFPredicate C_RDFPredicate
     | Choices_C_RDFPredicate Cover ID ([C_RDFPredicate])
     | Fail_C_RDFPredicate Cover FailInfo
     | Guard_C_RDFPredicate Cover Constraints C_RDFPredicate

instance Show C_RDFPredicate where
  showsPrec d (Choice_C_RDFPredicate cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_RDFPredicate cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_RDFPredicate cd c e) = showsGuard d cd c e
  showsPrec _ (Fail_C_RDFPredicate cd info) = showChar '!'
  showsPrec _ (C_RDFPredicate x1 x2) = (showString "(RDFPredicate") . ((showChar ' ') . ((shows x1) . ((showChar ' ') . ((shows x2) . (showChar ')')))))


instance Read C_RDFPredicate where
  readsPrec d s = readParen (d > 10) (\r -> [ (C_RDFPredicate x1 x2,r2) | (_,r0) <- readQualified "RDF" "RDFPredicate" r, (x1,r1) <- readsPrec 11 r0, (x2,r2) <- readsPrec 11 r1]) s


instance NonDet C_RDFPredicate where
  choiceCons = Choice_C_RDFPredicate
  choicesCons = Choices_C_RDFPredicate
  failCons = Fail_C_RDFPredicate
  guardCons = Guard_C_RDFPredicate
  try (Choice_C_RDFPredicate cd i x y) = tryChoice cd i x y
  try (Choices_C_RDFPredicate cd i xs) = tryChoices cd i xs
  try (Fail_C_RDFPredicate cd info) = Fail cd info
  try (Guard_C_RDFPredicate cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_RDFPredicate cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_RDFPredicate cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_RDFPredicate cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_RDFPredicate cd i _) = error ("RDF.RDFPredicate.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_RDFPredicate cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_RDFPredicate cd c e) = f cd c e
  match _ _ _ _ _ f x = f x


instance Generable C_RDFPredicate where
  generate s = Choices_C_RDFPredicate defCover (freeID [2] s) [(C_RDFPredicate (generate (leftSupply s)) (generate (rightSupply s)))]


instance NormalForm C_RDFPredicate where
  ($!!) cont (C_RDFPredicate x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_RDFPredicate y1 y2) cs) $!! x2) cs) $!! x1) cs
  ($!!) cont (Choice_C_RDFPredicate cd i x y) cs = nfChoice cont cd i x y cs
  ($!!) cont (Choices_C_RDFPredicate cd i xs) cs = nfChoices cont cd i xs cs
  ($!!) cont (Guard_C_RDFPredicate cd c e) cs = guardCons cd c ((cont $!! e) (addCs c cs))
  ($!!) _ (Fail_C_RDFPredicate cd info) _ = failCons cd info
  ($##) cont (C_RDFPredicate x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_RDFPredicate y1 y2) cs) $## x2) cs) $## x1) cs
  ($##) cont (Choice_C_RDFPredicate cd i x y) cs = gnfChoice cont cd i x y cs
  ($##) cont (Choices_C_RDFPredicate cd i xs) cs = gnfChoices cont cd i xs cs
  ($##) cont (Guard_C_RDFPredicate cd c e) cs = guardCons cd c ((cont $## e) (addCs c cs))
  ($##) _ (Fail_C_RDFPredicate cd info) _ = failCons cd info
  ($!<) cont (C_RDFPredicate x1 x2) = (\y1 -> (\y2 -> cont (C_RDFPredicate y1 y2)) $!< x2) $!< x1
  ($!<) cont (Choice_C_RDFPredicate cd i x y) = nfChoiceIO cont cd i x y
  ($!<) cont (Choices_C_RDFPredicate cd i xs) = nfChoicesIO cont cd i xs
  ($!<) cont x = cont x
  searchNF search cont (C_RDFPredicate x1 x2) = search (\y1 -> search (\y2 -> cont (C_RDFPredicate y1 y2)) x2) x1
  searchNF _ _ x = error ("RDF.RDFPredicate.searchNF: no constructor: " ++ (show x))


instance Unifiable C_RDFPredicate where
  (=.=) (C_RDFPredicate x1 x2) (C_RDFPredicate y1 y2) cs = (((x1 =:= y1) cs) & ((x2 =:= y2) cs)) cs
  (=.=) _ _ _ = Fail_C_Success defCover defFailInfo
  (=.<=) (C_RDFPredicate x1 x2) (C_RDFPredicate y1 y2) cs = (((x1 =:<= y1) cs) & ((x2 =:<= y2) cs)) cs
  (=.<=) _ _ _ = Fail_C_Success defCover defFailInfo
  bind i (C_RDFPredicate x2 x3) = ((i :=: (ChooseN 0 2)):(concat [(bind (leftID i) x2),(bind (rightID i) x3)]))
  bind i (Choice_C_RDFPredicate cd j x y) = [(ConstraintChoice cd j (bind i x) (bind i y))]
  bind i (Choices_C_RDFPredicate cd j@(FreeID _ _) xs) = bindOrNarrow i cd j xs
  bind i (Choices_C_RDFPredicate cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (bind i) xs))]
  bind _ (Choices_C_RDFPredicate cd i _) = error ("RDF.RDFPredicate.bind: Choices with ChoiceID: " ++ (show i))
  bind _ (Fail_C_RDFPredicate cd info) = [(Unsolvable info)]
  bind i (Guard_C_RDFPredicate cd c e) = (getConstrList c) ++ (bind i e)
  lazyBind i (C_RDFPredicate x2 x3) = [(i :=: (ChooseN 0 2)),((leftID i) :=: (LazyBind (lazyBind (leftID i) x2))),((rightID i) :=: (LazyBind (lazyBind (rightID i) x3)))]
  lazyBind i (Choice_C_RDFPredicate cd j x y) = [(ConstraintChoice cd j (lazyBind i x) (lazyBind i y))]
  lazyBind i (Choices_C_RDFPredicate cd j@(FreeID _ _) xs) = lazyBindOrNarrow i cd j xs
  lazyBind i (Choices_C_RDFPredicate cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (lazyBind i) xs))]
  lazyBind _ (Choices_C_RDFPredicate cd i _) = error ("RDF.RDFPredicate.lazyBind: Choices with ChoiceID: " ++ (show i))
  lazyBind _ (Fail_C_RDFPredicate cd info) = [(Unsolvable info)]
  lazyBind i (Guard_C_RDFPredicate cd c e) = (getConstrList c) ++ [(i :=: (LazyBind (lazyBind i e)))]


instance Curry_Prelude.Curry C_RDFPredicate where
  (=?=) (Choice_C_RDFPredicate cd i x y) z cs = narrow cd i ((x Curry_Prelude.=?= z) cs) ((y Curry_Prelude.=?= z) cs)
  (=?=) (Choices_C_RDFPredicate cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.=?= y) cs) xs
  (=?=) (Guard_C_RDFPredicate cd c e) y cs = guardCons cd c ((e Curry_Prelude.=?= y) (addCs c cs))
  (=?=) (Fail_C_RDFPredicate cd info) _ _ = failCons cd info
  (=?=) z (Choice_C_RDFPredicate cd i x y) cs = narrow cd i ((z Curry_Prelude.=?= x) cs) ((z Curry_Prelude.=?= y) cs)
  (=?=) y (Choices_C_RDFPredicate cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.=?= x) cs) xs
  (=?=) y (Guard_C_RDFPredicate cd c e) cs = guardCons cd c ((y Curry_Prelude.=?= e) (addCs c cs))
  (=?=) _ (Fail_C_RDFPredicate cd info) _ = failCons cd info
  (=?=) (C_RDFPredicate x1 x2) (C_RDFPredicate y1 y2) cs = Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.=?= y2) cs) cs
  (<?=) (Choice_C_RDFPredicate cd i x y) z cs = narrow cd i ((x Curry_Prelude.<?= z) cs) ((y Curry_Prelude.<?= z) cs)
  (<?=) (Choices_C_RDFPredicate cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.<?= y) cs) xs
  (<?=) (Guard_C_RDFPredicate cd c e) y cs = guardCons cd c ((e Curry_Prelude.<?= y) (addCs c cs))
  (<?=) (Fail_C_RDFPredicate cd info) _ _ = failCons cd info
  (<?=) z (Choice_C_RDFPredicate cd i x y) cs = narrow cd i ((z Curry_Prelude.<?= x) cs) ((z Curry_Prelude.<?= y) cs)
  (<?=) y (Choices_C_RDFPredicate cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.<?= x) cs) xs
  (<?=) y (Guard_C_RDFPredicate cd c e) cs = guardCons cd c ((y Curry_Prelude.<?= e) (addCs c cs))
  (<?=) _ (Fail_C_RDFPredicate cd info) _ = failCons cd info
  (<?=) (C_RDFPredicate x1 x2) (C_RDFPredicate y1 y2) cs = Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_lt x1 y1 cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.<?= y2) cs) cs) cs


instance Coverable C_RDFPredicate where
  cover (C_RDFPredicate x1 x2) = C_RDFPredicate (cover x1) (cover x2)
  cover (Choice_C_RDFPredicate cd i x y) = Choice_C_RDFPredicate (incCover cd) i (cover x) (cover y)
  cover (Choices_C_RDFPredicate cd i xs) = Choices_C_RDFPredicate (incCover cd) i (map cover xs)
  cover (Fail_C_RDFPredicate cd info) = Fail_C_RDFPredicate (incCover cd) info
  cover (Guard_C_RDFPredicate cd c e) = Guard_C_RDFPredicate (incCover cd) c (cover e)


data C_RDFTriple
     = C_RDFTriple C_RDFNode C_RDFPredicate C_RDFNode
     | Choice_C_RDFTriple Cover ID C_RDFTriple C_RDFTriple
     | Choices_C_RDFTriple Cover ID ([C_RDFTriple])
     | Fail_C_RDFTriple Cover FailInfo
     | Guard_C_RDFTriple Cover Constraints C_RDFTriple

instance Show C_RDFTriple where
  showsPrec d (Choice_C_RDFTriple cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_RDFTriple cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_RDFTriple cd c e) = showsGuard d cd c e
  showsPrec _ (Fail_C_RDFTriple cd info) = showChar '!'
  showsPrec _ (C_RDFTriple x1 x2 x3) = (showString "(RDFTriple") . ((showChar ' ') . ((shows x1) . ((showChar ' ') . ((shows x2) . ((showChar ' ') . ((shows x3) . (showChar ')')))))))


instance Read C_RDFTriple where
  readsPrec d s = readParen (d > 10) (\r -> [ (C_RDFTriple x1 x2 x3,r3) | (_,r0) <- readQualified "RDF" "RDFTriple" r, (x1,r1) <- readsPrec 11 r0, (x2,r2) <- readsPrec 11 r1, (x3,r3) <- readsPrec 11 r2]) s


instance NonDet C_RDFTriple where
  choiceCons = Choice_C_RDFTriple
  choicesCons = Choices_C_RDFTriple
  failCons = Fail_C_RDFTriple
  guardCons = Guard_C_RDFTriple
  try (Choice_C_RDFTriple cd i x y) = tryChoice cd i x y
  try (Choices_C_RDFTriple cd i xs) = tryChoices cd i xs
  try (Fail_C_RDFTriple cd info) = Fail cd info
  try (Guard_C_RDFTriple cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_RDFTriple cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_RDFTriple cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_RDFTriple cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_RDFTriple cd i _) = error ("RDF.RDFTriple.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_RDFTriple cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_RDFTriple cd c e) = f cd c e
  match _ _ _ _ _ f x = f x


instance Generable C_RDFTriple where
  generate s = Choices_C_RDFTriple defCover (freeID [3] s) [(C_RDFTriple (generate (leftSupply (leftSupply s))) (generate (rightSupply (leftSupply s))) (generate (rightSupply s)))]


instance NormalForm C_RDFTriple where
  ($!!) cont (C_RDFTriple x1 x2 x3) cs = ((\y1 cs -> ((\y2 cs -> ((\y3 cs -> cont (C_RDFTriple y1 y2 y3) cs) $!! x3) cs) $!! x2) cs) $!! x1) cs
  ($!!) cont (Choice_C_RDFTriple cd i x y) cs = nfChoice cont cd i x y cs
  ($!!) cont (Choices_C_RDFTriple cd i xs) cs = nfChoices cont cd i xs cs
  ($!!) cont (Guard_C_RDFTriple cd c e) cs = guardCons cd c ((cont $!! e) (addCs c cs))
  ($!!) _ (Fail_C_RDFTriple cd info) _ = failCons cd info
  ($##) cont (C_RDFTriple x1 x2 x3) cs = ((\y1 cs -> ((\y2 cs -> ((\y3 cs -> cont (C_RDFTriple y1 y2 y3) cs) $## x3) cs) $## x2) cs) $## x1) cs
  ($##) cont (Choice_C_RDFTriple cd i x y) cs = gnfChoice cont cd i x y cs
  ($##) cont (Choices_C_RDFTriple cd i xs) cs = gnfChoices cont cd i xs cs
  ($##) cont (Guard_C_RDFTriple cd c e) cs = guardCons cd c ((cont $## e) (addCs c cs))
  ($##) _ (Fail_C_RDFTriple cd info) _ = failCons cd info
  ($!<) cont (C_RDFTriple x1 x2 x3) = (\y1 -> (\y2 -> (\y3 -> cont (C_RDFTriple y1 y2 y3)) $!< x3) $!< x2) $!< x1
  ($!<) cont (Choice_C_RDFTriple cd i x y) = nfChoiceIO cont cd i x y
  ($!<) cont (Choices_C_RDFTriple cd i xs) = nfChoicesIO cont cd i xs
  ($!<) cont x = cont x
  searchNF search cont (C_RDFTriple x1 x2 x3) = search (\y1 -> search (\y2 -> search (\y3 -> cont (C_RDFTriple y1 y2 y3)) x3) x2) x1
  searchNF _ _ x = error ("RDF.RDFTriple.searchNF: no constructor: " ++ (show x))


instance Unifiable C_RDFTriple where
  (=.=) (C_RDFTriple x1 x2 x3) (C_RDFTriple y1 y2 y3) cs = (((x1 =:= y1) cs) & ((((x2 =:= y2) cs) & ((x3 =:= y3) cs)) cs)) cs
  (=.=) _ _ _ = Fail_C_Success defCover defFailInfo
  (=.<=) (C_RDFTriple x1 x2 x3) (C_RDFTriple y1 y2 y3) cs = (((x1 =:<= y1) cs) & ((((x2 =:<= y2) cs) & ((x3 =:<= y3) cs)) cs)) cs
  (=.<=) _ _ _ = Fail_C_Success defCover defFailInfo
  bind i (C_RDFTriple x2 x3 x4) = ((i :=: (ChooseN 0 3)):(concat [(bind (leftID (leftID i)) x2),(bind (rightID (leftID i)) x3),(bind (rightID i) x4)]))
  bind i (Choice_C_RDFTriple cd j x y) = [(ConstraintChoice cd j (bind i x) (bind i y))]
  bind i (Choices_C_RDFTriple cd j@(FreeID _ _) xs) = bindOrNarrow i cd j xs
  bind i (Choices_C_RDFTriple cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (bind i) xs))]
  bind _ (Choices_C_RDFTriple cd i _) = error ("RDF.RDFTriple.bind: Choices with ChoiceID: " ++ (show i))
  bind _ (Fail_C_RDFTriple cd info) = [(Unsolvable info)]
  bind i (Guard_C_RDFTriple cd c e) = (getConstrList c) ++ (bind i e)
  lazyBind i (C_RDFTriple x2 x3 x4) = [(i :=: (ChooseN 0 3)),((leftID (leftID i)) :=: (LazyBind (lazyBind (leftID (leftID i)) x2))),((rightID (leftID i)) :=: (LazyBind (lazyBind (rightID (leftID i)) x3))),((rightID i) :=: (LazyBind (lazyBind (rightID i) x4)))]
  lazyBind i (Choice_C_RDFTriple cd j x y) = [(ConstraintChoice cd j (lazyBind i x) (lazyBind i y))]
  lazyBind i (Choices_C_RDFTriple cd j@(FreeID _ _) xs) = lazyBindOrNarrow i cd j xs
  lazyBind i (Choices_C_RDFTriple cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (lazyBind i) xs))]
  lazyBind _ (Choices_C_RDFTriple cd i _) = error ("RDF.RDFTriple.lazyBind: Choices with ChoiceID: " ++ (show i))
  lazyBind _ (Fail_C_RDFTriple cd info) = [(Unsolvable info)]
  lazyBind i (Guard_C_RDFTriple cd c e) = (getConstrList c) ++ [(i :=: (LazyBind (lazyBind i e)))]


instance Curry_Prelude.Curry C_RDFTriple where
  (=?=) (Choice_C_RDFTriple cd i x y) z cs = narrow cd i ((x Curry_Prelude.=?= z) cs) ((y Curry_Prelude.=?= z) cs)
  (=?=) (Choices_C_RDFTriple cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.=?= y) cs) xs
  (=?=) (Guard_C_RDFTriple cd c e) y cs = guardCons cd c ((e Curry_Prelude.=?= y) (addCs c cs))
  (=?=) (Fail_C_RDFTriple cd info) _ _ = failCons cd info
  (=?=) z (Choice_C_RDFTriple cd i x y) cs = narrow cd i ((z Curry_Prelude.=?= x) cs) ((z Curry_Prelude.=?= y) cs)
  (=?=) y (Choices_C_RDFTriple cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.=?= x) cs) xs
  (=?=) y (Guard_C_RDFTriple cd c e) cs = guardCons cd c ((y Curry_Prelude.=?= e) (addCs c cs))
  (=?=) _ (Fail_C_RDFTriple cd info) _ = failCons cd info
  (=?=) (C_RDFTriple x1 x2 x3) (C_RDFTriple y1 y2 y3) cs = Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x2 Curry_Prelude.=?= y2) cs) ((x3 Curry_Prelude.=?= y3) cs) cs) cs
  (<?=) (Choice_C_RDFTriple cd i x y) z cs = narrow cd i ((x Curry_Prelude.<?= z) cs) ((y Curry_Prelude.<?= z) cs)
  (<?=) (Choices_C_RDFTriple cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.<?= y) cs) xs
  (<?=) (Guard_C_RDFTriple cd c e) y cs = guardCons cd c ((e Curry_Prelude.<?= y) (addCs c cs))
  (<?=) (Fail_C_RDFTriple cd info) _ _ = failCons cd info
  (<?=) z (Choice_C_RDFTriple cd i x y) cs = narrow cd i ((z Curry_Prelude.<?= x) cs) ((z Curry_Prelude.<?= y) cs)
  (<?=) y (Choices_C_RDFTriple cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.<?= x) cs) xs
  (<?=) y (Guard_C_RDFTriple cd c e) cs = guardCons cd c ((y Curry_Prelude.<?= e) (addCs c cs))
  (<?=) _ (Fail_C_RDFTriple cd info) _ = failCons cd info
  (<?=) (C_RDFTriple x1 x2 x3) (C_RDFTriple y1 y2 y3) cs = Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_lt x1 y1 cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) (Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_lt x2 y2 cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x2 Curry_Prelude.=?= y2) cs) ((x3 Curry_Prelude.<?= y3) cs) cs) cs) cs) cs


instance Coverable C_RDFTriple where
  cover (C_RDFTriple x1 x2 x3) = C_RDFTriple (cover x1) (cover x2) (cover x3)
  cover (Choice_C_RDFTriple cd i x y) = Choice_C_RDFTriple (incCover cd) i (cover x) (cover y)
  cover (Choices_C_RDFTriple cd i xs) = Choices_C_RDFTriple (incCover cd) i (map cover xs)
  cover (Fail_C_RDFTriple cd info) = Fail_C_RDFTriple (incCover cd) info
  cover (Guard_C_RDFTriple cd c e) = Guard_C_RDFTriple (incCover cd) c (cover e)


data C_RDFPrefix
     = C_RDFPrefix (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List Curry_Prelude.C_Char)
     | Choice_C_RDFPrefix Cover ID C_RDFPrefix C_RDFPrefix
     | Choices_C_RDFPrefix Cover ID ([C_RDFPrefix])
     | Fail_C_RDFPrefix Cover FailInfo
     | Guard_C_RDFPrefix Cover Constraints C_RDFPrefix

instance Show C_RDFPrefix where
  showsPrec d (Choice_C_RDFPrefix cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_RDFPrefix cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_RDFPrefix cd c e) = showsGuard d cd c e
  showsPrec _ (Fail_C_RDFPrefix cd info) = showChar '!'
  showsPrec _ (C_RDFPrefix x1 x2) = (showString "(RDFPrefix") . ((showChar ' ') . ((shows x1) . ((showChar ' ') . ((shows x2) . (showChar ')')))))


instance Read C_RDFPrefix where
  readsPrec d s = readParen (d > 10) (\r -> [ (C_RDFPrefix x1 x2,r2) | (_,r0) <- readQualified "RDF" "RDFPrefix" r, (x1,r1) <- readsPrec 11 r0, (x2,r2) <- readsPrec 11 r1]) s


instance NonDet C_RDFPrefix where
  choiceCons = Choice_C_RDFPrefix
  choicesCons = Choices_C_RDFPrefix
  failCons = Fail_C_RDFPrefix
  guardCons = Guard_C_RDFPrefix
  try (Choice_C_RDFPrefix cd i x y) = tryChoice cd i x y
  try (Choices_C_RDFPrefix cd i xs) = tryChoices cd i xs
  try (Fail_C_RDFPrefix cd info) = Fail cd info
  try (Guard_C_RDFPrefix cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_RDFPrefix cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_RDFPrefix cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_RDFPrefix cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_RDFPrefix cd i _) = error ("RDF.RDFPrefix.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_RDFPrefix cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_RDFPrefix cd c e) = f cd c e
  match _ _ _ _ _ f x = f x


instance Generable C_RDFPrefix where
  generate s = Choices_C_RDFPrefix defCover (freeID [2] s) [(C_RDFPrefix (generate (leftSupply s)) (generate (rightSupply s)))]


instance NormalForm C_RDFPrefix where
  ($!!) cont (C_RDFPrefix x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_RDFPrefix y1 y2) cs) $!! x2) cs) $!! x1) cs
  ($!!) cont (Choice_C_RDFPrefix cd i x y) cs = nfChoice cont cd i x y cs
  ($!!) cont (Choices_C_RDFPrefix cd i xs) cs = nfChoices cont cd i xs cs
  ($!!) cont (Guard_C_RDFPrefix cd c e) cs = guardCons cd c ((cont $!! e) (addCs c cs))
  ($!!) _ (Fail_C_RDFPrefix cd info) _ = failCons cd info
  ($##) cont (C_RDFPrefix x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_RDFPrefix y1 y2) cs) $## x2) cs) $## x1) cs
  ($##) cont (Choice_C_RDFPrefix cd i x y) cs = gnfChoice cont cd i x y cs
  ($##) cont (Choices_C_RDFPrefix cd i xs) cs = gnfChoices cont cd i xs cs
  ($##) cont (Guard_C_RDFPrefix cd c e) cs = guardCons cd c ((cont $## e) (addCs c cs))
  ($##) _ (Fail_C_RDFPrefix cd info) _ = failCons cd info
  ($!<) cont (C_RDFPrefix x1 x2) = (\y1 -> (\y2 -> cont (C_RDFPrefix y1 y2)) $!< x2) $!< x1
  ($!<) cont (Choice_C_RDFPrefix cd i x y) = nfChoiceIO cont cd i x y
  ($!<) cont (Choices_C_RDFPrefix cd i xs) = nfChoicesIO cont cd i xs
  ($!<) cont x = cont x
  searchNF search cont (C_RDFPrefix x1 x2) = search (\y1 -> search (\y2 -> cont (C_RDFPrefix y1 y2)) x2) x1
  searchNF _ _ x = error ("RDF.RDFPrefix.searchNF: no constructor: " ++ (show x))


instance Unifiable C_RDFPrefix where
  (=.=) (C_RDFPrefix x1 x2) (C_RDFPrefix y1 y2) cs = (((x1 =:= y1) cs) & ((x2 =:= y2) cs)) cs
  (=.=) _ _ _ = Fail_C_Success defCover defFailInfo
  (=.<=) (C_RDFPrefix x1 x2) (C_RDFPrefix y1 y2) cs = (((x1 =:<= y1) cs) & ((x2 =:<= y2) cs)) cs
  (=.<=) _ _ _ = Fail_C_Success defCover defFailInfo
  bind i (C_RDFPrefix x2 x3) = ((i :=: (ChooseN 0 2)):(concat [(bind (leftID i) x2),(bind (rightID i) x3)]))
  bind i (Choice_C_RDFPrefix cd j x y) = [(ConstraintChoice cd j (bind i x) (bind i y))]
  bind i (Choices_C_RDFPrefix cd j@(FreeID _ _) xs) = bindOrNarrow i cd j xs
  bind i (Choices_C_RDFPrefix cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (bind i) xs))]
  bind _ (Choices_C_RDFPrefix cd i _) = error ("RDF.RDFPrefix.bind: Choices with ChoiceID: " ++ (show i))
  bind _ (Fail_C_RDFPrefix cd info) = [(Unsolvable info)]
  bind i (Guard_C_RDFPrefix cd c e) = (getConstrList c) ++ (bind i e)
  lazyBind i (C_RDFPrefix x2 x3) = [(i :=: (ChooseN 0 2)),((leftID i) :=: (LazyBind (lazyBind (leftID i) x2))),((rightID i) :=: (LazyBind (lazyBind (rightID i) x3)))]
  lazyBind i (Choice_C_RDFPrefix cd j x y) = [(ConstraintChoice cd j (lazyBind i x) (lazyBind i y))]
  lazyBind i (Choices_C_RDFPrefix cd j@(FreeID _ _) xs) = lazyBindOrNarrow i cd j xs
  lazyBind i (Choices_C_RDFPrefix cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (lazyBind i) xs))]
  lazyBind _ (Choices_C_RDFPrefix cd i _) = error ("RDF.RDFPrefix.lazyBind: Choices with ChoiceID: " ++ (show i))
  lazyBind _ (Fail_C_RDFPrefix cd info) = [(Unsolvable info)]
  lazyBind i (Guard_C_RDFPrefix cd c e) = (getConstrList c) ++ [(i :=: (LazyBind (lazyBind i e)))]


instance Curry_Prelude.Curry C_RDFPrefix where
  (=?=) (Choice_C_RDFPrefix cd i x y) z cs = narrow cd i ((x Curry_Prelude.=?= z) cs) ((y Curry_Prelude.=?= z) cs)
  (=?=) (Choices_C_RDFPrefix cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.=?= y) cs) xs
  (=?=) (Guard_C_RDFPrefix cd c e) y cs = guardCons cd c ((e Curry_Prelude.=?= y) (addCs c cs))
  (=?=) (Fail_C_RDFPrefix cd info) _ _ = failCons cd info
  (=?=) z (Choice_C_RDFPrefix cd i x y) cs = narrow cd i ((z Curry_Prelude.=?= x) cs) ((z Curry_Prelude.=?= y) cs)
  (=?=) y (Choices_C_RDFPrefix cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.=?= x) cs) xs
  (=?=) y (Guard_C_RDFPrefix cd c e) cs = guardCons cd c ((y Curry_Prelude.=?= e) (addCs c cs))
  (=?=) _ (Fail_C_RDFPrefix cd info) _ = failCons cd info
  (=?=) (C_RDFPrefix x1 x2) (C_RDFPrefix y1 y2) cs = Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.=?= y2) cs) cs
  (<?=) (Choice_C_RDFPrefix cd i x y) z cs = narrow cd i ((x Curry_Prelude.<?= z) cs) ((y Curry_Prelude.<?= z) cs)
  (<?=) (Choices_C_RDFPrefix cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.<?= y) cs) xs
  (<?=) (Guard_C_RDFPrefix cd c e) y cs = guardCons cd c ((e Curry_Prelude.<?= y) (addCs c cs))
  (<?=) (Fail_C_RDFPrefix cd info) _ _ = failCons cd info
  (<?=) z (Choice_C_RDFPrefix cd i x y) cs = narrow cd i ((z Curry_Prelude.<?= x) cs) ((z Curry_Prelude.<?= y) cs)
  (<?=) y (Choices_C_RDFPrefix cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.<?= x) cs) xs
  (<?=) y (Guard_C_RDFPrefix cd c e) cs = guardCons cd c ((y Curry_Prelude.<?= e) (addCs c cs))
  (<?=) _ (Fail_C_RDFPrefix cd info) _ = failCons cd info
  (<?=) (C_RDFPrefix x1 x2) (C_RDFPrefix y1 y2) cs = Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_lt x1 y1 cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.<?= y2) cs) cs) cs


instance Coverable C_RDFPrefix where
  cover (C_RDFPrefix x1 x2) = C_RDFPrefix (cover x1) (cover x2)
  cover (Choice_C_RDFPrefix cd i x y) = Choice_C_RDFPrefix (incCover cd) i (cover x) (cover y)
  cover (Choices_C_RDFPrefix cd i xs) = Choices_C_RDFPrefix (incCover cd) i (map cover xs)
  cover (Fail_C_RDFPrefix cd info) = Fail_C_RDFPrefix (incCover cd) info
  cover (Guard_C_RDFPrefix cd c e) = Guard_C_RDFPrefix (incCover cd) c (cover e)


data C_RDFGraph
     = C_RDFGraph (Curry_Prelude.OP_List C_RDFPrefix) (Curry_Prelude.OP_List C_RDFTriple)
     | Choice_C_RDFGraph Cover ID C_RDFGraph C_RDFGraph
     | Choices_C_RDFGraph Cover ID ([C_RDFGraph])
     | Fail_C_RDFGraph Cover FailInfo
     | Guard_C_RDFGraph Cover Constraints C_RDFGraph

instance Show C_RDFGraph where
  showsPrec d (Choice_C_RDFGraph cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_RDFGraph cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_RDFGraph cd c e) = showsGuard d cd c e
  showsPrec _ (Fail_C_RDFGraph cd info) = showChar '!'
  showsPrec _ (C_RDFGraph x1 x2) = (showString "(RDFGraph") . ((showChar ' ') . ((shows x1) . ((showChar ' ') . ((shows x2) . (showChar ')')))))


instance Read C_RDFGraph where
  readsPrec d s = readParen (d > 10) (\r -> [ (C_RDFGraph x1 x2,r2) | (_,r0) <- readQualified "RDF" "RDFGraph" r, (x1,r1) <- readsPrec 11 r0, (x2,r2) <- readsPrec 11 r1]) s


instance NonDet C_RDFGraph where
  choiceCons = Choice_C_RDFGraph
  choicesCons = Choices_C_RDFGraph
  failCons = Fail_C_RDFGraph
  guardCons = Guard_C_RDFGraph
  try (Choice_C_RDFGraph cd i x y) = tryChoice cd i x y
  try (Choices_C_RDFGraph cd i xs) = tryChoices cd i xs
  try (Fail_C_RDFGraph cd info) = Fail cd info
  try (Guard_C_RDFGraph cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_RDFGraph cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_RDFGraph cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_RDFGraph cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_RDFGraph cd i _) = error ("RDF.RDFGraph.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_RDFGraph cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_RDFGraph cd c e) = f cd c e
  match _ _ _ _ _ f x = f x


instance Generable C_RDFGraph where
  generate s = Choices_C_RDFGraph defCover (freeID [2] s) [(C_RDFGraph (generate (leftSupply s)) (generate (rightSupply s)))]


instance NormalForm C_RDFGraph where
  ($!!) cont (C_RDFGraph x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_RDFGraph y1 y2) cs) $!! x2) cs) $!! x1) cs
  ($!!) cont (Choice_C_RDFGraph cd i x y) cs = nfChoice cont cd i x y cs
  ($!!) cont (Choices_C_RDFGraph cd i xs) cs = nfChoices cont cd i xs cs
  ($!!) cont (Guard_C_RDFGraph cd c e) cs = guardCons cd c ((cont $!! e) (addCs c cs))
  ($!!) _ (Fail_C_RDFGraph cd info) _ = failCons cd info
  ($##) cont (C_RDFGraph x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_RDFGraph y1 y2) cs) $## x2) cs) $## x1) cs
  ($##) cont (Choice_C_RDFGraph cd i x y) cs = gnfChoice cont cd i x y cs
  ($##) cont (Choices_C_RDFGraph cd i xs) cs = gnfChoices cont cd i xs cs
  ($##) cont (Guard_C_RDFGraph cd c e) cs = guardCons cd c ((cont $## e) (addCs c cs))
  ($##) _ (Fail_C_RDFGraph cd info) _ = failCons cd info
  ($!<) cont (C_RDFGraph x1 x2) = (\y1 -> (\y2 -> cont (C_RDFGraph y1 y2)) $!< x2) $!< x1
  ($!<) cont (Choice_C_RDFGraph cd i x y) = nfChoiceIO cont cd i x y
  ($!<) cont (Choices_C_RDFGraph cd i xs) = nfChoicesIO cont cd i xs
  ($!<) cont x = cont x
  searchNF search cont (C_RDFGraph x1 x2) = search (\y1 -> search (\y2 -> cont (C_RDFGraph y1 y2)) x2) x1
  searchNF _ _ x = error ("RDF.RDFGraph.searchNF: no constructor: " ++ (show x))


instance Unifiable C_RDFGraph where
  (=.=) (C_RDFGraph x1 x2) (C_RDFGraph y1 y2) cs = (((x1 =:= y1) cs) & ((x2 =:= y2) cs)) cs
  (=.=) _ _ _ = Fail_C_Success defCover defFailInfo
  (=.<=) (C_RDFGraph x1 x2) (C_RDFGraph y1 y2) cs = (((x1 =:<= y1) cs) & ((x2 =:<= y2) cs)) cs
  (=.<=) _ _ _ = Fail_C_Success defCover defFailInfo
  bind i (C_RDFGraph x2 x3) = ((i :=: (ChooseN 0 2)):(concat [(bind (leftID i) x2),(bind (rightID i) x3)]))
  bind i (Choice_C_RDFGraph cd j x y) = [(ConstraintChoice cd j (bind i x) (bind i y))]
  bind i (Choices_C_RDFGraph cd j@(FreeID _ _) xs) = bindOrNarrow i cd j xs
  bind i (Choices_C_RDFGraph cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (bind i) xs))]
  bind _ (Choices_C_RDFGraph cd i _) = error ("RDF.RDFGraph.bind: Choices with ChoiceID: " ++ (show i))
  bind _ (Fail_C_RDFGraph cd info) = [(Unsolvable info)]
  bind i (Guard_C_RDFGraph cd c e) = (getConstrList c) ++ (bind i e)
  lazyBind i (C_RDFGraph x2 x3) = [(i :=: (ChooseN 0 2)),((leftID i) :=: (LazyBind (lazyBind (leftID i) x2))),((rightID i) :=: (LazyBind (lazyBind (rightID i) x3)))]
  lazyBind i (Choice_C_RDFGraph cd j x y) = [(ConstraintChoice cd j (lazyBind i x) (lazyBind i y))]
  lazyBind i (Choices_C_RDFGraph cd j@(FreeID _ _) xs) = lazyBindOrNarrow i cd j xs
  lazyBind i (Choices_C_RDFGraph cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (lazyBind i) xs))]
  lazyBind _ (Choices_C_RDFGraph cd i _) = error ("RDF.RDFGraph.lazyBind: Choices with ChoiceID: " ++ (show i))
  lazyBind _ (Fail_C_RDFGraph cd info) = [(Unsolvable info)]
  lazyBind i (Guard_C_RDFGraph cd c e) = (getConstrList c) ++ [(i :=: (LazyBind (lazyBind i e)))]


instance Curry_Prelude.Curry C_RDFGraph where
  (=?=) (Choice_C_RDFGraph cd i x y) z cs = narrow cd i ((x Curry_Prelude.=?= z) cs) ((y Curry_Prelude.=?= z) cs)
  (=?=) (Choices_C_RDFGraph cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.=?= y) cs) xs
  (=?=) (Guard_C_RDFGraph cd c e) y cs = guardCons cd c ((e Curry_Prelude.=?= y) (addCs c cs))
  (=?=) (Fail_C_RDFGraph cd info) _ _ = failCons cd info
  (=?=) z (Choice_C_RDFGraph cd i x y) cs = narrow cd i ((z Curry_Prelude.=?= x) cs) ((z Curry_Prelude.=?= y) cs)
  (=?=) y (Choices_C_RDFGraph cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.=?= x) cs) xs
  (=?=) y (Guard_C_RDFGraph cd c e) cs = guardCons cd c ((y Curry_Prelude.=?= e) (addCs c cs))
  (=?=) _ (Fail_C_RDFGraph cd info) _ = failCons cd info
  (=?=) (C_RDFGraph x1 x2) (C_RDFGraph y1 y2) cs = Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.=?= y2) cs) cs
  (<?=) (Choice_C_RDFGraph cd i x y) z cs = narrow cd i ((x Curry_Prelude.<?= z) cs) ((y Curry_Prelude.<?= z) cs)
  (<?=) (Choices_C_RDFGraph cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.<?= y) cs) xs
  (<?=) (Guard_C_RDFGraph cd c e) y cs = guardCons cd c ((e Curry_Prelude.<?= y) (addCs c cs))
  (<?=) (Fail_C_RDFGraph cd info) _ _ = failCons cd info
  (<?=) z (Choice_C_RDFGraph cd i x y) cs = narrow cd i ((z Curry_Prelude.<?= x) cs) ((z Curry_Prelude.<?= y) cs)
  (<?=) y (Choices_C_RDFGraph cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.<?= x) cs) xs
  (<?=) y (Guard_C_RDFGraph cd c e) cs = guardCons cd c ((y Curry_Prelude.<?= e) (addCs c cs))
  (<?=) _ (Fail_C_RDFGraph cd info) _ = failCons cd info
  (<?=) (C_RDFGraph x1 x2) (C_RDFGraph y1 y2) cs = Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_lt x1 y1 cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.<?= y2) cs) cs) cs


instance Coverable C_RDFGraph where
  cover (C_RDFGraph x1 x2) = C_RDFGraph (cover x1) (cover x2)
  cover (Choice_C_RDFGraph cd i x y) = Choice_C_RDFGraph (incCover cd) i (cover x) (cover y)
  cover (Choices_C_RDFGraph cd i xs) = Choices_C_RDFGraph (incCover cd) i (map cover xs)
  cover (Fail_C_RDFGraph cd info) = Fail_C_RDFGraph (incCover cd) info
  cover (Guard_C_RDFGraph cd c e) = Guard_C_RDFGraph (incCover cd) c (cover e)


d_C_getRDFPredicateURI :: C_RDFPredicate -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_C_getRDFPredicateURI x1 x3500 = case x1 of
     (C_RDFPredicate x2 x3) -> x2
     (Choice_C_RDFPredicate x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_getRDFPredicateURI x1002 x3500) (d_C_getRDFPredicateURI x1003 x3500)
     (Choices_C_RDFPredicate x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_getRDFPredicateURI z x3500) x1002
     (Guard_C_RDFPredicate x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_getRDFPredicateURI x1002) $! (addCs x1001 x3500))
     (Fail_C_RDFPredicate x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getRDFPredicateType :: C_RDFPredicate -> ConstStore -> Curry_Prelude.C_Maybe (Curry_Prelude.OP_List Curry_Prelude.C_Char)
d_C_getRDFPredicateType x1 x3500 = case x1 of
     (C_RDFPredicate x2 x3) -> x3
     (Choice_C_RDFPredicate x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_getRDFPredicateType x1002 x3500) (d_C_getRDFPredicateType x1003 x3500)
     (Choices_C_RDFPredicate x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_getRDFPredicateType z x3500) x1002
     (Guard_C_RDFPredicate x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_getRDFPredicateType x1002) $! (addCs x1001 x3500))
     (Fail_C_RDFPredicate x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getRDFTripleSubject :: C_RDFTriple -> ConstStore -> C_RDFNode
d_C_getRDFTripleSubject x1 x3500 = case x1 of
     (C_RDFTriple x2 x3 x4) -> x2
     (Choice_C_RDFTriple x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_getRDFTripleSubject x1002 x3500) (d_C_getRDFTripleSubject x1003 x3500)
     (Choices_C_RDFTriple x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_getRDFTripleSubject z x3500) x1002
     (Guard_C_RDFTriple x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_getRDFTripleSubject x1002) $! (addCs x1001 x3500))
     (Fail_C_RDFTriple x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getRDFTriplePredicate :: C_RDFTriple -> ConstStore -> C_RDFPredicate
d_C_getRDFTriplePredicate x1 x3500 = case x1 of
     (C_RDFTriple x2 x3 x4) -> x3
     (Choice_C_RDFTriple x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_getRDFTriplePredicate x1002 x3500) (d_C_getRDFTriplePredicate x1003 x3500)
     (Choices_C_RDFTriple x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_getRDFTriplePredicate z x3500) x1002
     (Guard_C_RDFTriple x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_getRDFTriplePredicate x1002) $! (addCs x1001 x3500))
     (Fail_C_RDFTriple x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getRDFTripleObject :: C_RDFTriple -> ConstStore -> C_RDFNode
d_C_getRDFTripleObject x1 x3500 = case x1 of
     (C_RDFTriple x2 x3 x4) -> x4
     (Choice_C_RDFTriple x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_getRDFTripleObject x1002 x3500) (d_C_getRDFTripleObject x1003 x3500)
     (Choices_C_RDFTriple x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_getRDFTripleObject z x3500) x1002
     (Guard_C_RDFTriple x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_getRDFTripleObject x1002) $! (addCs x1001 x3500))
     (Fail_C_RDFTriple x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_groupRDFTriples :: Curry_Prelude.OP_List C_RDFTriple -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 C_RDFNode (Curry_Prelude.OP_List C_RDFTriple))
d_C_groupRDFTriples x1 x3500 = case x1 of
     Curry_Prelude.OP_List -> Curry_Prelude.OP_List
     (Curry_Prelude.OP_Cons x2 x3) -> Curry_Prelude.d_OP_dollar (d_OP_groupRDFTriples_dot_insert_dot_22 x2) (d_C_groupRDFTriples x3 x3500) x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_groupRDFTriples x1002 x3500) (d_C_groupRDFTriples x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_groupRDFTriples z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_groupRDFTriples x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_groupRDFTriples_dot_insert_dot_22 :: C_RDFTriple -> Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 C_RDFNode (Curry_Prelude.OP_List C_RDFTriple)) -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 C_RDFNode (Curry_Prelude.OP_List C_RDFTriple))
d_OP_groupRDFTriples_dot_insert_dot_22 x1 x2 x3500 = case x2 of
     Curry_Prelude.OP_List -> Curry_Prelude.OP_Cons (Curry_Prelude.OP_Tuple2 (d_C_getRDFTripleSubject x1 x3500) (Curry_Prelude.OP_Cons x1 Curry_Prelude.OP_List)) Curry_Prelude.OP_List
     (Curry_Prelude.OP_Cons x3 x4) -> d_OP__case_7 x1 x4 x3 x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_groupRDFTriples_dot_insert_dot_22 x1 x1002 x3500) (d_OP_groupRDFTriples_dot_insert_dot_22 x1 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_groupRDFTriples_dot_insert_dot_22 x1 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_groupRDFTriples_dot_insert_dot_22 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_rdfPrefix :: ConstStore -> C_RDFPrefix
d_C_rdfPrefix x3500 = C_RDFPrefix (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'f'#) Curry_Prelude.OP_List))) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'h'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ':'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '/'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '/'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '.'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '3'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '.'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'g'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '/'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '1'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '9'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '9'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '9'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '/'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '0'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '2'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '/'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '2'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '2'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '-'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'f'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '-'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'y'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'x'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '-'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '#'#) Curry_Prelude.OP_List)))))))))))))))))))))))))))))))))))))))))))

d_C_getRDFPrefixName :: C_RDFPrefix -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_C_getRDFPrefixName x1 x3500 = case x1 of
     (C_RDFPrefix x2 x3) -> x2
     (Choice_C_RDFPrefix x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_getRDFPrefixName x1002 x3500) (d_C_getRDFPrefixName x1003 x3500)
     (Choices_C_RDFPrefix x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_getRDFPrefixName z x3500) x1002
     (Guard_C_RDFPrefix x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_getRDFPrefixName x1002) $! (addCs x1001 x3500))
     (Fail_C_RDFPrefix x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getRDFPrefixURI :: C_RDFPrefix -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_C_getRDFPrefixURI x1 x3500 = case x1 of
     (C_RDFPrefix x2 x3) -> x3
     (Choice_C_RDFPrefix x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_getRDFPrefixURI x1002 x3500) (d_C_getRDFPrefixURI x1003 x3500)
     (Choices_C_RDFPrefix x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_getRDFPrefixURI z x3500) x1002
     (Guard_C_RDFPrefix x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_getRDFPrefixURI x1002) $! (addCs x1001 x3500))
     (Fail_C_RDFPrefix x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getRDFPrefixByURI :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.OP_List C_RDFPrefix -> ConstStore -> Curry_Prelude.C_Maybe C_RDFPrefix
d_C_getRDFPrefixByURI x1 x3500 = Curry_Prelude.d_OP_dollar Curry_List.d_C_find (Curry_Prelude.d_OP_dot (Curry_Prelude.d_C_flip (acceptCs id Curry_List.d_C_isPrefixOf) x1) d_C_getRDFPrefixURI x3500) x3500

nd_C_getRDFPrefixByURI :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> IDSupply -> ConstStore -> Func (Curry_Prelude.OP_List C_RDFPrefix) (Curry_Prelude.C_Maybe C_RDFPrefix)
nd_C_getRDFPrefixByURI x1 x3000 x3500 = let
     x2002 = x3000
      in (seq x2002 (let
          x2001 = leftSupply x2002
          x2000 = rightSupply x2002
           in (seq x2001 (seq x2000 (Curry_Prelude.nd_OP_dollar (wrapNX id Curry_List.nd_C_find) (Curry_Prelude.nd_OP_dot (wrapNX id (Curry_Prelude.nd_C_flip (wrapDX (wrapDX id) (acceptCs id Curry_List.d_C_isPrefixOf)) x1)) (wrapDX id d_C_getRDFPrefixURI) x2000 x3500) x2001 x3500)))))

d_C_getRDFPrefixByName :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.OP_List C_RDFPrefix -> ConstStore -> Curry_Prelude.C_Maybe C_RDFPrefix
d_C_getRDFPrefixByName x1 x3500 = Curry_Prelude.d_OP_dollar Curry_List.d_C_find (Curry_Prelude.d_OP_dot (Curry_Prelude.d_OP_eq_eq x1) d_C_getRDFPrefixName x3500) x3500

nd_C_getRDFPrefixByName :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> IDSupply -> ConstStore -> Func (Curry_Prelude.OP_List C_RDFPrefix) (Curry_Prelude.C_Maybe C_RDFPrefix)
nd_C_getRDFPrefixByName x1 x3000 x3500 = let
     x2002 = x3000
      in (seq x2002 (let
          x2001 = leftSupply x2002
          x2000 = rightSupply x2002
           in (seq x2001 (seq x2000 (Curry_Prelude.nd_OP_dollar (wrapNX id Curry_List.nd_C_find) (Curry_Prelude.nd_OP_dot (wrapDX id (Curry_Prelude.d_OP_eq_eq x1)) (wrapDX id d_C_getRDFPrefixName) x2000 x3500) x2001 x3500)))))

d_C_prefixURI :: Curry_Prelude.OP_List C_RDFPrefix -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_C_prefixURI x1 x2 x3500 = d_OP__case_5 x1 x2 (Curry_Prelude.d_C_apply (d_C_getRDFPrefixByURI x2 x3500) x1 x3500) x3500

d_C_getAbsoluteURI :: Curry_Prelude.OP_List C_RDFPrefix -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_C_getAbsoluteURI x1 x2 x3500 = let
     x3 = Curry_Prelude.d_C_apply (Curry_Prelude.d_C_break (Curry_Prelude.d_OP_eq_eq (Curry_Prelude.C_Char ':'#)) x3500) x2 x3500
     x4 = d_OP_getAbsoluteURI_dot___hash_selFP2_hash_prefixName x3 x3500
     x5 = d_OP_getAbsoluteURI_dot___hash_selFP3_hash_fragment x3 x3500
      in (d_OP__case_3 x1 x2 x4 x5 (Curry_Prelude.d_C_apply (d_C_getRDFPrefixByName x4 x3500) x1 x3500) x3500)

d_OP_getAbsoluteURI_dot___hash_selFP2_hash_prefixName :: Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List Curry_Prelude.C_Char) -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_OP_getAbsoluteURI_dot___hash_selFP2_hash_prefixName x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple2 x2 x3) -> d_OP__case_1 x2 x3 x3500
     (Curry_Prelude.Choice_OP_Tuple2 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_getAbsoluteURI_dot___hash_selFP2_hash_prefixName x1002 x3500) (d_OP_getAbsoluteURI_dot___hash_selFP2_hash_prefixName x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple2 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_getAbsoluteURI_dot___hash_selFP2_hash_prefixName z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple2 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_getAbsoluteURI_dot___hash_selFP2_hash_prefixName x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple2 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_getAbsoluteURI_dot___hash_selFP3_hash_fragment :: Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List Curry_Prelude.C_Char) -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_OP_getAbsoluteURI_dot___hash_selFP3_hash_fragment x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple2 x2 x3) -> d_OP__case_0 x3 x3500
     (Curry_Prelude.Choice_OP_Tuple2 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_getAbsoluteURI_dot___hash_selFP3_hash_fragment x1002 x3500) (d_OP_getAbsoluteURI_dot___hash_selFP3_hash_fragment x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple2 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_getAbsoluteURI_dot___hash_selFP3_hash_fragment z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple2 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_getAbsoluteURI_dot___hash_selFP3_hash_fragment x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple2 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getRDFGraphPrefixes :: C_RDFGraph -> ConstStore -> Curry_Prelude.OP_List C_RDFPrefix
d_C_getRDFGraphPrefixes x1 x3500 = case x1 of
     (C_RDFGraph x2 x3) -> x2
     (Choice_C_RDFGraph x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_getRDFGraphPrefixes x1002 x3500) (d_C_getRDFGraphPrefixes x1003 x3500)
     (Choices_C_RDFGraph x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_getRDFGraphPrefixes z x3500) x1002
     (Guard_C_RDFGraph x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_getRDFGraphPrefixes x1002) $! (addCs x1001 x3500))
     (Fail_C_RDFGraph x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getRDFGraphTriples :: C_RDFGraph -> ConstStore -> Curry_Prelude.OP_List C_RDFTriple
d_C_getRDFGraphTriples x1 x3500 = case x1 of
     (C_RDFGraph x2 x3) -> x3
     (Choice_C_RDFGraph x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_getRDFGraphTriples x1002 x3500) (d_C_getRDFGraphTriples x1003 x3500)
     (Choices_C_RDFGraph x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_getRDFGraphTriples z x3500) x1002
     (Guard_C_RDFGraph x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_getRDFGraphTriples x1002) $! (addCs x1001 x3500))
     (Fail_C_RDFGraph x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getRDFGraphPrefixByURI :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> C_RDFGraph -> ConstStore -> Curry_Prelude.C_Maybe C_RDFPrefix
d_C_getRDFGraphPrefixByURI x1 x3500 = Curry_Prelude.d_OP_dot (d_C_getRDFPrefixByURI x1 x3500) d_C_getRDFGraphPrefixes x3500

nd_C_getRDFGraphPrefixByURI :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> IDSupply -> ConstStore -> Func C_RDFGraph (Curry_Prelude.C_Maybe C_RDFPrefix)
nd_C_getRDFGraphPrefixByURI x1 x3000 x3500 = let
     x2002 = x3000
      in (seq x2002 (let
          x2001 = leftSupply x2002
          x2000 = rightSupply x2002
           in (seq x2001 (seq x2000 (Curry_Prelude.nd_OP_dot (nd_C_getRDFPrefixByURI x1 x2000 x3500) (wrapDX id d_C_getRDFGraphPrefixes) x2001 x3500)))))

d_OP__case_0 x3 x3500 = case x3 of
     (Curry_Prelude.OP_Cons x4 x5) -> x5
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_0 x1002 x3500) (d_OP__case_0 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_0 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_0 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_0 x3 x3000 x3500 = case x3 of
     (Curry_Prelude.OP_Cons x4 x5) -> x5
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_0 x1002 x3000 x3500) (nd_OP__case_0 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_0 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_0 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_1 x2 x3 x3500 = case x3 of
     (Curry_Prelude.OP_Cons x4 x5) -> x2
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_1 x2 x1002 x3500) (d_OP__case_1 x2 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_1 x2 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_1 x2 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_1 x2 x3 x3000 x3500 = case x3 of
     (Curry_Prelude.OP_Cons x4 x5) -> x2
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_1 x2 x1002 x3000 x3500) (nd_OP__case_1 x2 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_1 x2 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_1 x2 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_3 x1 x2 x4 x5 x7 x3500 = case x7 of
     (Curry_Prelude.C_Just x6) -> d_OP__case_2 x5 x6 x3500
     Curry_Prelude.C_Nothing -> Curry_Prelude.d_OP_dollar Curry_Prelude.d_C_error (Curry_Prelude.d_OP_plus_plus (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'I'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'l'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ' '#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'N'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'S'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '.'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ' '#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'M'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'g'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ' '#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'N'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'S'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ' '#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'f'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'x'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '.'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ' '#) Curry_Prelude.OP_List))))))))))))))))))))))))))))))) x2 x3500) x3500
     (Curry_Prelude.Choice_C_Maybe x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_3 x1 x2 x4 x5 x1002 x3500) (d_OP__case_3 x1 x2 x4 x5 x1003 x3500)
     (Curry_Prelude.Choices_C_Maybe x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_3 x1 x2 x4 x5 z x3500) x1002
     (Curry_Prelude.Guard_C_Maybe x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_3 x1 x2 x4 x5 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Maybe x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_3 x1 x2 x4 x5 x7 x3000 x3500 = case x7 of
     (Curry_Prelude.C_Just x6) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_2 x5 x6 x2000 x3500))
     Curry_Prelude.C_Nothing -> let
          x2000 = x3000
           in (seq x2000 (Curry_Prelude.nd_OP_dollar (wrapDX id Curry_Prelude.d_C_error) (Curry_Prelude.d_OP_plus_plus (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'I'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'l'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ' '#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'N'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'S'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '.'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ' '#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'M'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'g'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ' '#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'N'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'S'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ' '#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'f'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'x'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '.'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ' '#) Curry_Prelude.OP_List))))))))))))))))))))))))))))))) x2 x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Maybe x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_3 x1 x2 x4 x5 x1002 x3000 x3500) (nd_OP__case_3 x1 x2 x4 x5 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Maybe x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_3 x1 x2 x4 x5 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Maybe x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_3 x1 x2 x4 x5 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Maybe x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_2 x5 x6 x3500 = case x6 of
     (C_RDFPrefix x7 x8) -> Curry_Prelude.d_OP_plus_plus x8 x5 x3500
     (Choice_C_RDFPrefix x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_2 x5 x1002 x3500) (d_OP__case_2 x5 x1003 x3500)
     (Choices_C_RDFPrefix x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_2 x5 z x3500) x1002
     (Guard_C_RDFPrefix x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_2 x5 x1002) $! (addCs x1001 x3500))
     (Fail_C_RDFPrefix x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_2 x5 x6 x3000 x3500 = case x6 of
     (C_RDFPrefix x7 x8) -> Curry_Prelude.d_OP_plus_plus x8 x5 x3500
     (Choice_C_RDFPrefix x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_2 x5 x1002 x3000 x3500) (nd_OP__case_2 x5 x1003 x3000 x3500)
     (Choices_C_RDFPrefix x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_2 x5 z x3000 x3500) x1002
     (Guard_C_RDFPrefix x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_2 x5 x1002 x3000) $! (addCs x1001 x3500))
     (Fail_C_RDFPrefix x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_5 x1 x2 x4 x3500 = case x4 of
     (Curry_Prelude.C_Just x3) -> d_OP__case_4 x2 x3 x3500
     Curry_Prelude.C_Nothing -> x2
     (Curry_Prelude.Choice_C_Maybe x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_5 x1 x2 x1002 x3500) (d_OP__case_5 x1 x2 x1003 x3500)
     (Curry_Prelude.Choices_C_Maybe x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_5 x1 x2 z x3500) x1002
     (Curry_Prelude.Guard_C_Maybe x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_5 x1 x2 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Maybe x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_5 x1 x2 x4 x3000 x3500 = case x4 of
     (Curry_Prelude.C_Just x3) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_4 x2 x3 x2000 x3500))
     Curry_Prelude.C_Nothing -> x2
     (Curry_Prelude.Choice_C_Maybe x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_5 x1 x2 x1002 x3000 x3500) (nd_OP__case_5 x1 x2 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Maybe x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_5 x1 x2 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Maybe x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_5 x1 x2 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Maybe x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_4 x2 x3 x3500 = case x3 of
     (C_RDFPrefix x4 x5) -> Curry_Prelude.d_OP_plus_plus x4 (Curry_Prelude.d_OP_plus_plus (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ':'#) Curry_Prelude.OP_List) (Curry_Prelude.d_C_drop (Curry_Prelude.d_C_length x5 x3500) x2 x3500) x3500) x3500
     (Choice_C_RDFPrefix x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_4 x2 x1002 x3500) (d_OP__case_4 x2 x1003 x3500)
     (Choices_C_RDFPrefix x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_4 x2 z x3500) x1002
     (Guard_C_RDFPrefix x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_4 x2 x1002) $! (addCs x1001 x3500))
     (Fail_C_RDFPrefix x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_4 x2 x3 x3000 x3500 = case x3 of
     (C_RDFPrefix x4 x5) -> Curry_Prelude.d_OP_plus_plus x4 (Curry_Prelude.d_OP_plus_plus (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char ':'#) Curry_Prelude.OP_List) (Curry_Prelude.d_C_drop (Curry_Prelude.d_C_length x5 x3500) x2 x3500) x3500) x3500
     (Choice_C_RDFPrefix x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_4 x2 x1002 x3000 x3500) (nd_OP__case_4 x2 x1003 x3000 x3500)
     (Choices_C_RDFPrefix x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_4 x2 z x3000 x3500) x1002
     (Guard_C_RDFPrefix x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_4 x2 x1002 x3000) $! (addCs x1001 x3500))
     (Fail_C_RDFPrefix x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_7 x1 x4 x3 x3500 = case x3 of
     (Curry_Prelude.OP_Tuple2 x5 x6) -> d_OP__case_6 x1 x3 x4 x5 x6 (Curry_Prelude.d_OP_eq_eq x5 (d_C_getRDFTripleSubject x1 x3500) x3500) x3500
     (Curry_Prelude.Choice_OP_Tuple2 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_7 x1 x4 x1002 x3500) (d_OP__case_7 x1 x4 x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple2 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_7 x1 x4 z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple2 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_7 x1 x4 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple2 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_7 x1 x4 x3 x3000 x3500 = case x3 of
     (Curry_Prelude.OP_Tuple2 x5 x6) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_6 x1 x3 x4 x5 x6 (Curry_Prelude.d_OP_eq_eq x5 (d_C_getRDFTripleSubject x1 x3500) x3500) x2000 x3500))
     (Curry_Prelude.Choice_OP_Tuple2 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_7 x1 x4 x1002 x3000 x3500) (nd_OP__case_7 x1 x4 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_Tuple2 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_7 x1 x4 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple2 x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_7 x1 x4 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple2 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_6 x1 x3 x4 x5 x6 x7 x3500 = case x7 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.OP_Tuple2 x5 (Curry_Prelude.OP_Cons x1 x6)) x4
     Curry_Prelude.C_False -> Curry_Prelude.OP_Cons x3 (d_OP_groupRDFTriples_dot_insert_dot_22 x1 x4 x3500)
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_6 x1 x3 x4 x5 x6 x1002 x3500) (d_OP__case_6 x1 x3 x4 x5 x6 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_6 x1 x3 x4 x5 x6 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_6 x1 x3 x4 x5 x6 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_6 x1 x3 x4 x5 x6 x7 x3000 x3500 = case x7 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.OP_Tuple2 x5 (Curry_Prelude.OP_Cons x1 x6)) x4
     Curry_Prelude.C_False -> Curry_Prelude.OP_Cons x3 (d_OP_groupRDFTriples_dot_insert_dot_22 x1 x4 x3500)
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_6 x1 x3 x4 x5 x6 x1002 x3000 x3500) (nd_OP__case_6 x1 x3 x4 x5 x6 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_6 x1 x3 x4 x5 x6 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_6 x1 x3 x4 x5 x6 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo
