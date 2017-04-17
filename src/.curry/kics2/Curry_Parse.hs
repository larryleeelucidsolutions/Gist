{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module Curry_Parse (C_Token (..), C_PToken (..), C_TToken (..), C_Rule (..), C_Pattern, C_Template, C_Grammar, C_Binding, C_Bindings, d_C_terminalValue, d_C_terminalPos, d_C_getBinding, nd_C_getBinding, d_C_getSingleBinding, d_C_ifMaybe, d_C_bindPatternToken, d_C_bindPattern, d_C_instantiateTemplateToken, d_C_instantiate, d_C_reduceHeadUsingRule, d_C_reduceHead, d_C_reduce, d_C_parse', d_C_parse) where

import Basics
import qualified Curry_Maybe
import qualified Curry_Prelude
import qualified Curry_Parser
type C_Pattern = Curry_Prelude.OP_List C_PToken

type C_Template = Curry_Prelude.OP_List C_TToken

type C_Grammar = Curry_Prelude.OP_List C_Rule

type C_Binding t0 = Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t0))

type C_Bindings t0 = Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t0)))

data C_Token t0
     = C_Terminal t0 Curry_Prelude.C_Int
     | C_Nonterminal (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (Curry_Prelude.OP_List (C_Token t0)))
     | Choice_C_Token Cover ID (C_Token t0) (C_Token t0)
     | Choices_C_Token Cover ID ([C_Token t0])
     | Fail_C_Token Cover FailInfo
     | Guard_C_Token Cover Constraints (C_Token t0)

instance Show t0 => Show (C_Token t0) where
  showsPrec d (Choice_C_Token cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_Token cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_Token cd c e) = showsGuard d cd c e
  showsPrec _ (Fail_C_Token cd info) = showChar '!'
  showsPrec _ (C_Terminal x1 x2) = (showString "(Terminal") . ((showChar ' ') . ((shows x1) . ((showChar ' ') . ((shows x2) . (showChar ')')))))
  showsPrec _ (C_Nonterminal x1 x2) = (showString "(Nonterminal") . ((showChar ' ') . ((shows x1) . ((showChar ' ') . ((shows x2) . (showChar ')')))))


instance Read t0 => Read (C_Token t0) where
  readsPrec d s = (readParen (d > 10) (\r -> [ (C_Terminal x1 x2,r2) | (_,r0) <- readQualified "Parse" "Terminal" r, (x1,r1) <- readsPrec 11 r0, (x2,r2) <- readsPrec 11 r1]) s) ++ (readParen (d > 10) (\r -> [ (C_Nonterminal x1 x2,r2) | (_,r0) <- readQualified "Parse" "Nonterminal" r, (x1,r1) <- readsPrec 11 r0, (x2,r2) <- readsPrec 11 r1]) s)


instance NonDet (C_Token t0) where
  choiceCons = Choice_C_Token
  choicesCons = Choices_C_Token
  failCons = Fail_C_Token
  guardCons = Guard_C_Token
  try (Choice_C_Token cd i x y) = tryChoice cd i x y
  try (Choices_C_Token cd i xs) = tryChoices cd i xs
  try (Fail_C_Token cd info) = Fail cd info
  try (Guard_C_Token cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_Token cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_Token cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_Token cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_Token cd i _) = error ("Parse.Token.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_Token cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_Token cd c e) = f cd c e
  match _ _ _ _ _ f x = f x


instance Generable t0 => Generable (C_Token t0) where
  generate s = Choices_C_Token defCover (freeID [2,2] s) [(C_Terminal (generate (leftSupply s)) (generate (rightSupply s))),(C_Nonterminal (generate (leftSupply s)) (generate (rightSupply s)))]


instance NormalForm t0 => NormalForm (C_Token t0) where
  ($!!) cont (C_Terminal x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_Terminal y1 y2) cs) $!! x2) cs) $!! x1) cs
  ($!!) cont (C_Nonterminal x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_Nonterminal y1 y2) cs) $!! x2) cs) $!! x1) cs
  ($!!) cont (Choice_C_Token cd i x y) cs = nfChoice cont cd i x y cs
  ($!!) cont (Choices_C_Token cd i xs) cs = nfChoices cont cd i xs cs
  ($!!) cont (Guard_C_Token cd c e) cs = guardCons cd c ((cont $!! e) (addCs c cs))
  ($!!) _ (Fail_C_Token cd info) _ = failCons cd info
  ($##) cont (C_Terminal x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_Terminal y1 y2) cs) $## x2) cs) $## x1) cs
  ($##) cont (C_Nonterminal x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_Nonterminal y1 y2) cs) $## x2) cs) $## x1) cs
  ($##) cont (Choice_C_Token cd i x y) cs = gnfChoice cont cd i x y cs
  ($##) cont (Choices_C_Token cd i xs) cs = gnfChoices cont cd i xs cs
  ($##) cont (Guard_C_Token cd c e) cs = guardCons cd c ((cont $## e) (addCs c cs))
  ($##) _ (Fail_C_Token cd info) _ = failCons cd info
  ($!<) cont (C_Terminal x1 x2) = (\y1 -> (\y2 -> cont (C_Terminal y1 y2)) $!< x2) $!< x1
  ($!<) cont (C_Nonterminal x1 x2) = (\y1 -> (\y2 -> cont (C_Nonterminal y1 y2)) $!< x2) $!< x1
  ($!<) cont (Choice_C_Token cd i x y) = nfChoiceIO cont cd i x y
  ($!<) cont (Choices_C_Token cd i xs) = nfChoicesIO cont cd i xs
  ($!<) cont x = cont x
  searchNF search cont (C_Terminal x1 x2) = search (\y1 -> search (\y2 -> cont (C_Terminal y1 y2)) x2) x1
  searchNF search cont (C_Nonterminal x1 x2) = search (\y1 -> search (\y2 -> cont (C_Nonterminal y1 y2)) x2) x1
  searchNF _ _ x = error ("Parse.Token.searchNF: no constructor: " ++ (show x))


instance Unifiable t0 => Unifiable (C_Token t0) where
  (=.=) (C_Terminal x1 x2) (C_Terminal y1 y2) cs = (((x1 =:= y1) cs) & ((x2 =:= y2) cs)) cs
  (=.=) (C_Nonterminal x1 x2) (C_Nonterminal y1 y2) cs = (((x1 =:= y1) cs) & ((x2 =:= y2) cs)) cs
  (=.=) _ _ _ = Fail_C_Success defCover defFailInfo
  (=.<=) (C_Terminal x1 x2) (C_Terminal y1 y2) cs = (((x1 =:<= y1) cs) & ((x2 =:<= y2) cs)) cs
  (=.<=) (C_Nonterminal x1 x2) (C_Nonterminal y1 y2) cs = (((x1 =:<= y1) cs) & ((x2 =:<= y2) cs)) cs
  (=.<=) _ _ _ = Fail_C_Success defCover defFailInfo
  bind i (C_Terminal x2 x3) = ((i :=: (ChooseN 0 2)):(concat [(bind (leftID i) x2),(bind (rightID i) x3)]))
  bind i (C_Nonterminal x2 x3) = ((i :=: (ChooseN 1 2)):(concat [(bind (leftID i) x2),(bind (rightID i) x3)]))
  bind i (Choice_C_Token cd j x y) = [(ConstraintChoice cd j (bind i x) (bind i y))]
  bind i (Choices_C_Token cd j@(FreeID _ _) xs) = bindOrNarrow i cd j xs
  bind i (Choices_C_Token cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (bind i) xs))]
  bind _ (Choices_C_Token cd i _) = error ("Parse.Token.bind: Choices with ChoiceID: " ++ (show i))
  bind _ (Fail_C_Token cd info) = [(Unsolvable info)]
  bind i (Guard_C_Token cd c e) = (getConstrList c) ++ (bind i e)
  lazyBind i (C_Terminal x2 x3) = [(i :=: (ChooseN 0 2)),((leftID i) :=: (LazyBind (lazyBind (leftID i) x2))),((rightID i) :=: (LazyBind (lazyBind (rightID i) x3)))]
  lazyBind i (C_Nonterminal x2 x3) = [(i :=: (ChooseN 1 2)),((leftID i) :=: (LazyBind (lazyBind (leftID i) x2))),((rightID i) :=: (LazyBind (lazyBind (rightID i) x3)))]
  lazyBind i (Choice_C_Token cd j x y) = [(ConstraintChoice cd j (lazyBind i x) (lazyBind i y))]
  lazyBind i (Choices_C_Token cd j@(FreeID _ _) xs) = lazyBindOrNarrow i cd j xs
  lazyBind i (Choices_C_Token cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (lazyBind i) xs))]
  lazyBind _ (Choices_C_Token cd i _) = error ("Parse.Token.lazyBind: Choices with ChoiceID: " ++ (show i))
  lazyBind _ (Fail_C_Token cd info) = [(Unsolvable info)]
  lazyBind i (Guard_C_Token cd c e) = (getConstrList c) ++ [(i :=: (LazyBind (lazyBind i e)))]


instance Curry_Prelude.Curry t0 => Curry_Prelude.Curry (C_Token t0) where
  (=?=) (Choice_C_Token cd i x y) z cs = narrow cd i ((x Curry_Prelude.=?= z) cs) ((y Curry_Prelude.=?= z) cs)
  (=?=) (Choices_C_Token cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.=?= y) cs) xs
  (=?=) (Guard_C_Token cd c e) y cs = guardCons cd c ((e Curry_Prelude.=?= y) (addCs c cs))
  (=?=) (Fail_C_Token cd info) _ _ = failCons cd info
  (=?=) z (Choice_C_Token cd i x y) cs = narrow cd i ((z Curry_Prelude.=?= x) cs) ((z Curry_Prelude.=?= y) cs)
  (=?=) y (Choices_C_Token cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.=?= x) cs) xs
  (=?=) y (Guard_C_Token cd c e) cs = guardCons cd c ((y Curry_Prelude.=?= e) (addCs c cs))
  (=?=) _ (Fail_C_Token cd info) _ = failCons cd info
  (=?=) (C_Terminal x1 x2) (C_Terminal y1 y2) cs = Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.=?= y2) cs) cs
  (=?=) (C_Nonterminal x1 x2) (C_Nonterminal y1 y2) cs = Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.=?= y2) cs) cs
  (=?=) _ _ _ = Curry_Prelude.C_False
  (<?=) (Choice_C_Token cd i x y) z cs = narrow cd i ((x Curry_Prelude.<?= z) cs) ((y Curry_Prelude.<?= z) cs)
  (<?=) (Choices_C_Token cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.<?= y) cs) xs
  (<?=) (Guard_C_Token cd c e) y cs = guardCons cd c ((e Curry_Prelude.<?= y) (addCs c cs))
  (<?=) (Fail_C_Token cd info) _ _ = failCons cd info
  (<?=) z (Choice_C_Token cd i x y) cs = narrow cd i ((z Curry_Prelude.<?= x) cs) ((z Curry_Prelude.<?= y) cs)
  (<?=) y (Choices_C_Token cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.<?= x) cs) xs
  (<?=) y (Guard_C_Token cd c e) cs = guardCons cd c ((y Curry_Prelude.<?= e) (addCs c cs))
  (<?=) _ (Fail_C_Token cd info) _ = failCons cd info
  (<?=) (C_Terminal x1 x2) (C_Terminal y1 y2) cs = Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_lt x1 y1 cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.<?= y2) cs) cs) cs
  (<?=) (C_Terminal _ _) (C_Nonterminal _ _) _ = Curry_Prelude.C_True
  (<?=) (C_Nonterminal x1 x2) (C_Nonterminal y1 y2) cs = Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_lt x1 y1 cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.<?= y2) cs) cs) cs
  (<?=) _ _ _ = Curry_Prelude.C_False


instance Coverable t0 => Coverable (C_Token t0) where
  cover (C_Terminal x1 x2) = C_Terminal (cover x1) (cover x2)
  cover (C_Nonterminal x1 x2) = C_Nonterminal (cover x1) (cover x2)
  cover (Choice_C_Token cd i x y) = Choice_C_Token (incCover cd) i (cover x) (cover y)
  cover (Choices_C_Token cd i xs) = Choices_C_Token (incCover cd) i (map cover xs)
  cover (Fail_C_Token cd info) = Fail_C_Token (incCover cd) info
  cover (Guard_C_Token cd c e) = Guard_C_Token (incCover cd) c (cover e)


data C_PToken
     = C_PToken (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.C_Maybe (Curry_Prelude.OP_List Curry_Prelude.C_Char)) (Curry_Prelude.OP_List (Curry_Prelude.C_Maybe (Curry_Prelude.OP_List Curry_Prelude.C_Char)))
     | Choice_C_PToken Cover ID C_PToken C_PToken
     | Choices_C_PToken Cover ID ([C_PToken])
     | Fail_C_PToken Cover FailInfo
     | Guard_C_PToken Cover Constraints C_PToken

instance Show C_PToken where
  showsPrec d (Choice_C_PToken cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_PToken cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_PToken cd c e) = showsGuard d cd c e
  showsPrec _ (Fail_C_PToken cd info) = showChar '!'
  showsPrec _ (C_PToken x1 x2 x3) = (showString "(PToken") . ((showChar ' ') . ((shows x1) . ((showChar ' ') . ((shows x2) . ((showChar ' ') . ((shows x3) . (showChar ')')))))))


instance Read C_PToken where
  readsPrec d s = readParen (d > 10) (\r -> [ (C_PToken x1 x2 x3,r3) | (_,r0) <- readQualified "Parse" "PToken" r, (x1,r1) <- readsPrec 11 r0, (x2,r2) <- readsPrec 11 r1, (x3,r3) <- readsPrec 11 r2]) s


instance NonDet C_PToken where
  choiceCons = Choice_C_PToken
  choicesCons = Choices_C_PToken
  failCons = Fail_C_PToken
  guardCons = Guard_C_PToken
  try (Choice_C_PToken cd i x y) = tryChoice cd i x y
  try (Choices_C_PToken cd i xs) = tryChoices cd i xs
  try (Fail_C_PToken cd info) = Fail cd info
  try (Guard_C_PToken cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_PToken cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_PToken cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_PToken cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_PToken cd i _) = error ("Parse.PToken.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_PToken cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_PToken cd c e) = f cd c e
  match _ _ _ _ _ f x = f x


instance Generable C_PToken where
  generate s = Choices_C_PToken defCover (freeID [3] s) [(C_PToken (generate (leftSupply (leftSupply s))) (generate (rightSupply (leftSupply s))) (generate (rightSupply s)))]


instance NormalForm C_PToken where
  ($!!) cont (C_PToken x1 x2 x3) cs = ((\y1 cs -> ((\y2 cs -> ((\y3 cs -> cont (C_PToken y1 y2 y3) cs) $!! x3) cs) $!! x2) cs) $!! x1) cs
  ($!!) cont (Choice_C_PToken cd i x y) cs = nfChoice cont cd i x y cs
  ($!!) cont (Choices_C_PToken cd i xs) cs = nfChoices cont cd i xs cs
  ($!!) cont (Guard_C_PToken cd c e) cs = guardCons cd c ((cont $!! e) (addCs c cs))
  ($!!) _ (Fail_C_PToken cd info) _ = failCons cd info
  ($##) cont (C_PToken x1 x2 x3) cs = ((\y1 cs -> ((\y2 cs -> ((\y3 cs -> cont (C_PToken y1 y2 y3) cs) $## x3) cs) $## x2) cs) $## x1) cs
  ($##) cont (Choice_C_PToken cd i x y) cs = gnfChoice cont cd i x y cs
  ($##) cont (Choices_C_PToken cd i xs) cs = gnfChoices cont cd i xs cs
  ($##) cont (Guard_C_PToken cd c e) cs = guardCons cd c ((cont $## e) (addCs c cs))
  ($##) _ (Fail_C_PToken cd info) _ = failCons cd info
  ($!<) cont (C_PToken x1 x2 x3) = (\y1 -> (\y2 -> (\y3 -> cont (C_PToken y1 y2 y3)) $!< x3) $!< x2) $!< x1
  ($!<) cont (Choice_C_PToken cd i x y) = nfChoiceIO cont cd i x y
  ($!<) cont (Choices_C_PToken cd i xs) = nfChoicesIO cont cd i xs
  ($!<) cont x = cont x
  searchNF search cont (C_PToken x1 x2 x3) = search (\y1 -> search (\y2 -> search (\y3 -> cont (C_PToken y1 y2 y3)) x3) x2) x1
  searchNF _ _ x = error ("Parse.PToken.searchNF: no constructor: " ++ (show x))


instance Unifiable C_PToken where
  (=.=) (C_PToken x1 x2 x3) (C_PToken y1 y2 y3) cs = (((x1 =:= y1) cs) & ((((x2 =:= y2) cs) & ((x3 =:= y3) cs)) cs)) cs
  (=.=) _ _ _ = Fail_C_Success defCover defFailInfo
  (=.<=) (C_PToken x1 x2 x3) (C_PToken y1 y2 y3) cs = (((x1 =:<= y1) cs) & ((((x2 =:<= y2) cs) & ((x3 =:<= y3) cs)) cs)) cs
  (=.<=) _ _ _ = Fail_C_Success defCover defFailInfo
  bind i (C_PToken x2 x3 x4) = ((i :=: (ChooseN 0 3)):(concat [(bind (leftID (leftID i)) x2),(bind (rightID (leftID i)) x3),(bind (rightID i) x4)]))
  bind i (Choice_C_PToken cd j x y) = [(ConstraintChoice cd j (bind i x) (bind i y))]
  bind i (Choices_C_PToken cd j@(FreeID _ _) xs) = bindOrNarrow i cd j xs
  bind i (Choices_C_PToken cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (bind i) xs))]
  bind _ (Choices_C_PToken cd i _) = error ("Parse.PToken.bind: Choices with ChoiceID: " ++ (show i))
  bind _ (Fail_C_PToken cd info) = [(Unsolvable info)]
  bind i (Guard_C_PToken cd c e) = (getConstrList c) ++ (bind i e)
  lazyBind i (C_PToken x2 x3 x4) = [(i :=: (ChooseN 0 3)),((leftID (leftID i)) :=: (LazyBind (lazyBind (leftID (leftID i)) x2))),((rightID (leftID i)) :=: (LazyBind (lazyBind (rightID (leftID i)) x3))),((rightID i) :=: (LazyBind (lazyBind (rightID i) x4)))]
  lazyBind i (Choice_C_PToken cd j x y) = [(ConstraintChoice cd j (lazyBind i x) (lazyBind i y))]
  lazyBind i (Choices_C_PToken cd j@(FreeID _ _) xs) = lazyBindOrNarrow i cd j xs
  lazyBind i (Choices_C_PToken cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (lazyBind i) xs))]
  lazyBind _ (Choices_C_PToken cd i _) = error ("Parse.PToken.lazyBind: Choices with ChoiceID: " ++ (show i))
  lazyBind _ (Fail_C_PToken cd info) = [(Unsolvable info)]
  lazyBind i (Guard_C_PToken cd c e) = (getConstrList c) ++ [(i :=: (LazyBind (lazyBind i e)))]


instance Curry_Prelude.Curry C_PToken where
  (=?=) (Choice_C_PToken cd i x y) z cs = narrow cd i ((x Curry_Prelude.=?= z) cs) ((y Curry_Prelude.=?= z) cs)
  (=?=) (Choices_C_PToken cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.=?= y) cs) xs
  (=?=) (Guard_C_PToken cd c e) y cs = guardCons cd c ((e Curry_Prelude.=?= y) (addCs c cs))
  (=?=) (Fail_C_PToken cd info) _ _ = failCons cd info
  (=?=) z (Choice_C_PToken cd i x y) cs = narrow cd i ((z Curry_Prelude.=?= x) cs) ((z Curry_Prelude.=?= y) cs)
  (=?=) y (Choices_C_PToken cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.=?= x) cs) xs
  (=?=) y (Guard_C_PToken cd c e) cs = guardCons cd c ((y Curry_Prelude.=?= e) (addCs c cs))
  (=?=) _ (Fail_C_PToken cd info) _ = failCons cd info
  (=?=) (C_PToken x1 x2 x3) (C_PToken y1 y2 y3) cs = Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x2 Curry_Prelude.=?= y2) cs) ((x3 Curry_Prelude.=?= y3) cs) cs) cs
  (<?=) (Choice_C_PToken cd i x y) z cs = narrow cd i ((x Curry_Prelude.<?= z) cs) ((y Curry_Prelude.<?= z) cs)
  (<?=) (Choices_C_PToken cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.<?= y) cs) xs
  (<?=) (Guard_C_PToken cd c e) y cs = guardCons cd c ((e Curry_Prelude.<?= y) (addCs c cs))
  (<?=) (Fail_C_PToken cd info) _ _ = failCons cd info
  (<?=) z (Choice_C_PToken cd i x y) cs = narrow cd i ((z Curry_Prelude.<?= x) cs) ((z Curry_Prelude.<?= y) cs)
  (<?=) y (Choices_C_PToken cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.<?= x) cs) xs
  (<?=) y (Guard_C_PToken cd c e) cs = guardCons cd c ((y Curry_Prelude.<?= e) (addCs c cs))
  (<?=) _ (Fail_C_PToken cd info) _ = failCons cd info
  (<?=) (C_PToken x1 x2 x3) (C_PToken y1 y2 y3) cs = Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_lt x1 y1 cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) (Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_lt x2 y2 cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x2 Curry_Prelude.=?= y2) cs) ((x3 Curry_Prelude.<?= y3) cs) cs) cs) cs) cs


instance Coverable C_PToken where
  cover (C_PToken x1 x2 x3) = C_PToken (cover x1) (cover x2) (cover x3)
  cover (Choice_C_PToken cd i x y) = Choice_C_PToken (incCover cd) i (cover x) (cover y)
  cover (Choices_C_PToken cd i xs) = Choices_C_PToken (incCover cd) i (map cover xs)
  cover (Fail_C_PToken cd info) = Fail_C_PToken (incCover cd) info
  cover (Guard_C_PToken cd c e) = Guard_C_PToken (incCover cd) c (cover e)


data C_TToken
     = C_TToken (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (Curry_Prelude.OP_List (Curry_Prelude.OP_List Curry_Prelude.C_Char)))
     | C_PTokenRef (Curry_Prelude.OP_List Curry_Prelude.C_Char)
     | Choice_C_TToken Cover ID C_TToken C_TToken
     | Choices_C_TToken Cover ID ([C_TToken])
     | Fail_C_TToken Cover FailInfo
     | Guard_C_TToken Cover Constraints C_TToken

instance Show C_TToken where
  showsPrec d (Choice_C_TToken cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_TToken cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_TToken cd c e) = showsGuard d cd c e
  showsPrec _ (Fail_C_TToken cd info) = showChar '!'
  showsPrec _ (C_TToken x1 x2) = (showString "(TToken") . ((showChar ' ') . ((shows x1) . ((showChar ' ') . ((shows x2) . (showChar ')')))))
  showsPrec _ (C_PTokenRef x1) = (showString "(PTokenRef") . ((showChar ' ') . ((shows x1) . (showChar ')')))


instance Read C_TToken where
  readsPrec d s = (readParen (d > 10) (\r -> [ (C_TToken x1 x2,r2) | (_,r0) <- readQualified "Parse" "TToken" r, (x1,r1) <- readsPrec 11 r0, (x2,r2) <- readsPrec 11 r1]) s) ++ (readParen (d > 10) (\r -> [ (C_PTokenRef x1,r1) | (_,r0) <- readQualified "Parse" "PTokenRef" r, (x1,r1) <- readsPrec 11 r0]) s)


instance NonDet C_TToken where
  choiceCons = Choice_C_TToken
  choicesCons = Choices_C_TToken
  failCons = Fail_C_TToken
  guardCons = Guard_C_TToken
  try (Choice_C_TToken cd i x y) = tryChoice cd i x y
  try (Choices_C_TToken cd i xs) = tryChoices cd i xs
  try (Fail_C_TToken cd info) = Fail cd info
  try (Guard_C_TToken cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_TToken cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_TToken cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_TToken cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_TToken cd i _) = error ("Parse.TToken.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_TToken cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_TToken cd c e) = f cd c e
  match _ _ _ _ _ f x = f x


instance Generable C_TToken where
  generate s = Choices_C_TToken defCover (freeID [2,1] s) [(C_TToken (generate (leftSupply s)) (generate (rightSupply s))),(C_PTokenRef (generate (leftSupply s)))]


instance NormalForm C_TToken where
  ($!!) cont (C_TToken x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_TToken y1 y2) cs) $!! x2) cs) $!! x1) cs
  ($!!) cont (C_PTokenRef x1) cs = ((\y1 cs -> cont (C_PTokenRef y1) cs) $!! x1) cs
  ($!!) cont (Choice_C_TToken cd i x y) cs = nfChoice cont cd i x y cs
  ($!!) cont (Choices_C_TToken cd i xs) cs = nfChoices cont cd i xs cs
  ($!!) cont (Guard_C_TToken cd c e) cs = guardCons cd c ((cont $!! e) (addCs c cs))
  ($!!) _ (Fail_C_TToken cd info) _ = failCons cd info
  ($##) cont (C_TToken x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_TToken y1 y2) cs) $## x2) cs) $## x1) cs
  ($##) cont (C_PTokenRef x1) cs = ((\y1 cs -> cont (C_PTokenRef y1) cs) $## x1) cs
  ($##) cont (Choice_C_TToken cd i x y) cs = gnfChoice cont cd i x y cs
  ($##) cont (Choices_C_TToken cd i xs) cs = gnfChoices cont cd i xs cs
  ($##) cont (Guard_C_TToken cd c e) cs = guardCons cd c ((cont $## e) (addCs c cs))
  ($##) _ (Fail_C_TToken cd info) _ = failCons cd info
  ($!<) cont (C_TToken x1 x2) = (\y1 -> (\y2 -> cont (C_TToken y1 y2)) $!< x2) $!< x1
  ($!<) cont (C_PTokenRef x1) = (\y1 -> cont (C_PTokenRef y1)) $!< x1
  ($!<) cont (Choice_C_TToken cd i x y) = nfChoiceIO cont cd i x y
  ($!<) cont (Choices_C_TToken cd i xs) = nfChoicesIO cont cd i xs
  ($!<) cont x = cont x
  searchNF search cont (C_TToken x1 x2) = search (\y1 -> search (\y2 -> cont (C_TToken y1 y2)) x2) x1
  searchNF search cont (C_PTokenRef x1) = search (\y1 -> cont (C_PTokenRef y1)) x1
  searchNF _ _ x = error ("Parse.TToken.searchNF: no constructor: " ++ (show x))


instance Unifiable C_TToken where
  (=.=) (C_TToken x1 x2) (C_TToken y1 y2) cs = (((x1 =:= y1) cs) & ((x2 =:= y2) cs)) cs
  (=.=) (C_PTokenRef x1) (C_PTokenRef y1) cs = (x1 =:= y1) cs
  (=.=) _ _ _ = Fail_C_Success defCover defFailInfo
  (=.<=) (C_TToken x1 x2) (C_TToken y1 y2) cs = (((x1 =:<= y1) cs) & ((x2 =:<= y2) cs)) cs
  (=.<=) (C_PTokenRef x1) (C_PTokenRef y1) cs = (x1 =:<= y1) cs
  (=.<=) _ _ _ = Fail_C_Success defCover defFailInfo
  bind i (C_TToken x2 x3) = ((i :=: (ChooseN 0 2)):(concat [(bind (leftID i) x2),(bind (rightID i) x3)]))
  bind i (C_PTokenRef x2) = ((i :=: (ChooseN 1 1)):(concat [(bind (leftID i) x2)]))
  bind i (Choice_C_TToken cd j x y) = [(ConstraintChoice cd j (bind i x) (bind i y))]
  bind i (Choices_C_TToken cd j@(FreeID _ _) xs) = bindOrNarrow i cd j xs
  bind i (Choices_C_TToken cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (bind i) xs))]
  bind _ (Choices_C_TToken cd i _) = error ("Parse.TToken.bind: Choices with ChoiceID: " ++ (show i))
  bind _ (Fail_C_TToken cd info) = [(Unsolvable info)]
  bind i (Guard_C_TToken cd c e) = (getConstrList c) ++ (bind i e)
  lazyBind i (C_TToken x2 x3) = [(i :=: (ChooseN 0 2)),((leftID i) :=: (LazyBind (lazyBind (leftID i) x2))),((rightID i) :=: (LazyBind (lazyBind (rightID i) x3)))]
  lazyBind i (C_PTokenRef x2) = [(i :=: (ChooseN 1 1)),((leftID i) :=: (LazyBind (lazyBind (leftID i) x2)))]
  lazyBind i (Choice_C_TToken cd j x y) = [(ConstraintChoice cd j (lazyBind i x) (lazyBind i y))]
  lazyBind i (Choices_C_TToken cd j@(FreeID _ _) xs) = lazyBindOrNarrow i cd j xs
  lazyBind i (Choices_C_TToken cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (lazyBind i) xs))]
  lazyBind _ (Choices_C_TToken cd i _) = error ("Parse.TToken.lazyBind: Choices with ChoiceID: " ++ (show i))
  lazyBind _ (Fail_C_TToken cd info) = [(Unsolvable info)]
  lazyBind i (Guard_C_TToken cd c e) = (getConstrList c) ++ [(i :=: (LazyBind (lazyBind i e)))]


instance Curry_Prelude.Curry C_TToken where
  (=?=) (Choice_C_TToken cd i x y) z cs = narrow cd i ((x Curry_Prelude.=?= z) cs) ((y Curry_Prelude.=?= z) cs)
  (=?=) (Choices_C_TToken cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.=?= y) cs) xs
  (=?=) (Guard_C_TToken cd c e) y cs = guardCons cd c ((e Curry_Prelude.=?= y) (addCs c cs))
  (=?=) (Fail_C_TToken cd info) _ _ = failCons cd info
  (=?=) z (Choice_C_TToken cd i x y) cs = narrow cd i ((z Curry_Prelude.=?= x) cs) ((z Curry_Prelude.=?= y) cs)
  (=?=) y (Choices_C_TToken cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.=?= x) cs) xs
  (=?=) y (Guard_C_TToken cd c e) cs = guardCons cd c ((y Curry_Prelude.=?= e) (addCs c cs))
  (=?=) _ (Fail_C_TToken cd info) _ = failCons cd info
  (=?=) (C_TToken x1 x2) (C_TToken y1 y2) cs = Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.=?= y2) cs) cs
  (=?=) (C_PTokenRef x1) (C_PTokenRef y1) cs = (x1 Curry_Prelude.=?= y1) cs
  (=?=) _ _ _ = Curry_Prelude.C_False
  (<?=) (Choice_C_TToken cd i x y) z cs = narrow cd i ((x Curry_Prelude.<?= z) cs) ((y Curry_Prelude.<?= z) cs)
  (<?=) (Choices_C_TToken cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.<?= y) cs) xs
  (<?=) (Guard_C_TToken cd c e) y cs = guardCons cd c ((e Curry_Prelude.<?= y) (addCs c cs))
  (<?=) (Fail_C_TToken cd info) _ _ = failCons cd info
  (<?=) z (Choice_C_TToken cd i x y) cs = narrow cd i ((z Curry_Prelude.<?= x) cs) ((z Curry_Prelude.<?= y) cs)
  (<?=) y (Choices_C_TToken cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.<?= x) cs) xs
  (<?=) y (Guard_C_TToken cd c e) cs = guardCons cd c ((y Curry_Prelude.<?= e) (addCs c cs))
  (<?=) _ (Fail_C_TToken cd info) _ = failCons cd info
  (<?=) (C_TToken x1 x2) (C_TToken y1 y2) cs = Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_lt x1 y1 cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.<?= y2) cs) cs) cs
  (<?=) (C_TToken _ _) (C_PTokenRef _) _ = Curry_Prelude.C_True
  (<?=) (C_PTokenRef x1) (C_PTokenRef y1) cs = (x1 Curry_Prelude.<?= y1) cs
  (<?=) _ _ _ = Curry_Prelude.C_False


instance Coverable C_TToken where
  cover (C_TToken x1 x2) = C_TToken (cover x1) (cover x2)
  cover (C_PTokenRef x1) = C_PTokenRef (cover x1)
  cover (Choice_C_TToken cd i x y) = Choice_C_TToken (incCover cd) i (cover x) (cover y)
  cover (Choices_C_TToken cd i xs) = Choices_C_TToken (incCover cd) i (map cover xs)
  cover (Fail_C_TToken cd info) = Fail_C_TToken (incCover cd) info
  cover (Guard_C_TToken cd c e) = Guard_C_TToken (incCover cd) c (cover e)


data C_Rule
     = C_Rule (Curry_Prelude.OP_List C_PToken) (Curry_Prelude.OP_List C_TToken)
     | Choice_C_Rule Cover ID C_Rule C_Rule
     | Choices_C_Rule Cover ID ([C_Rule])
     | Fail_C_Rule Cover FailInfo
     | Guard_C_Rule Cover Constraints C_Rule

instance Show C_Rule where
  showsPrec d (Choice_C_Rule cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_Rule cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_Rule cd c e) = showsGuard d cd c e
  showsPrec _ (Fail_C_Rule cd info) = showChar '!'
  showsPrec _ (C_Rule x1 x2) = (showString "(Rule") . ((showChar ' ') . ((shows x1) . ((showChar ' ') . ((shows x2) . (showChar ')')))))


instance Read C_Rule where
  readsPrec d s = readParen (d > 10) (\r -> [ (C_Rule x1 x2,r2) | (_,r0) <- readQualified "Parse" "Rule" r, (x1,r1) <- readsPrec 11 r0, (x2,r2) <- readsPrec 11 r1]) s


instance NonDet C_Rule where
  choiceCons = Choice_C_Rule
  choicesCons = Choices_C_Rule
  failCons = Fail_C_Rule
  guardCons = Guard_C_Rule
  try (Choice_C_Rule cd i x y) = tryChoice cd i x y
  try (Choices_C_Rule cd i xs) = tryChoices cd i xs
  try (Fail_C_Rule cd info) = Fail cd info
  try (Guard_C_Rule cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_Rule cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_Rule cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_Rule cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_Rule cd i _) = error ("Parse.Rule.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_Rule cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_Rule cd c e) = f cd c e
  match _ _ _ _ _ f x = f x


instance Generable C_Rule where
  generate s = Choices_C_Rule defCover (freeID [2] s) [(C_Rule (generate (leftSupply s)) (generate (rightSupply s)))]


instance NormalForm C_Rule where
  ($!!) cont (C_Rule x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_Rule y1 y2) cs) $!! x2) cs) $!! x1) cs
  ($!!) cont (Choice_C_Rule cd i x y) cs = nfChoice cont cd i x y cs
  ($!!) cont (Choices_C_Rule cd i xs) cs = nfChoices cont cd i xs cs
  ($!!) cont (Guard_C_Rule cd c e) cs = guardCons cd c ((cont $!! e) (addCs c cs))
  ($!!) _ (Fail_C_Rule cd info) _ = failCons cd info
  ($##) cont (C_Rule x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_Rule y1 y2) cs) $## x2) cs) $## x1) cs
  ($##) cont (Choice_C_Rule cd i x y) cs = gnfChoice cont cd i x y cs
  ($##) cont (Choices_C_Rule cd i xs) cs = gnfChoices cont cd i xs cs
  ($##) cont (Guard_C_Rule cd c e) cs = guardCons cd c ((cont $## e) (addCs c cs))
  ($##) _ (Fail_C_Rule cd info) _ = failCons cd info
  ($!<) cont (C_Rule x1 x2) = (\y1 -> (\y2 -> cont (C_Rule y1 y2)) $!< x2) $!< x1
  ($!<) cont (Choice_C_Rule cd i x y) = nfChoiceIO cont cd i x y
  ($!<) cont (Choices_C_Rule cd i xs) = nfChoicesIO cont cd i xs
  ($!<) cont x = cont x
  searchNF search cont (C_Rule x1 x2) = search (\y1 -> search (\y2 -> cont (C_Rule y1 y2)) x2) x1
  searchNF _ _ x = error ("Parse.Rule.searchNF: no constructor: " ++ (show x))


instance Unifiable C_Rule where
  (=.=) (C_Rule x1 x2) (C_Rule y1 y2) cs = (((x1 =:= y1) cs) & ((x2 =:= y2) cs)) cs
  (=.=) _ _ _ = Fail_C_Success defCover defFailInfo
  (=.<=) (C_Rule x1 x2) (C_Rule y1 y2) cs = (((x1 =:<= y1) cs) & ((x2 =:<= y2) cs)) cs
  (=.<=) _ _ _ = Fail_C_Success defCover defFailInfo
  bind i (C_Rule x2 x3) = ((i :=: (ChooseN 0 2)):(concat [(bind (leftID i) x2),(bind (rightID i) x3)]))
  bind i (Choice_C_Rule cd j x y) = [(ConstraintChoice cd j (bind i x) (bind i y))]
  bind i (Choices_C_Rule cd j@(FreeID _ _) xs) = bindOrNarrow i cd j xs
  bind i (Choices_C_Rule cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (bind i) xs))]
  bind _ (Choices_C_Rule cd i _) = error ("Parse.Rule.bind: Choices with ChoiceID: " ++ (show i))
  bind _ (Fail_C_Rule cd info) = [(Unsolvable info)]
  bind i (Guard_C_Rule cd c e) = (getConstrList c) ++ (bind i e)
  lazyBind i (C_Rule x2 x3) = [(i :=: (ChooseN 0 2)),((leftID i) :=: (LazyBind (lazyBind (leftID i) x2))),((rightID i) :=: (LazyBind (lazyBind (rightID i) x3)))]
  lazyBind i (Choice_C_Rule cd j x y) = [(ConstraintChoice cd j (lazyBind i x) (lazyBind i y))]
  lazyBind i (Choices_C_Rule cd j@(FreeID _ _) xs) = lazyBindOrNarrow i cd j xs
  lazyBind i (Choices_C_Rule cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (lazyBind i) xs))]
  lazyBind _ (Choices_C_Rule cd i _) = error ("Parse.Rule.lazyBind: Choices with ChoiceID: " ++ (show i))
  lazyBind _ (Fail_C_Rule cd info) = [(Unsolvable info)]
  lazyBind i (Guard_C_Rule cd c e) = (getConstrList c) ++ [(i :=: (LazyBind (lazyBind i e)))]


instance Curry_Prelude.Curry C_Rule where
  (=?=) (Choice_C_Rule cd i x y) z cs = narrow cd i ((x Curry_Prelude.=?= z) cs) ((y Curry_Prelude.=?= z) cs)
  (=?=) (Choices_C_Rule cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.=?= y) cs) xs
  (=?=) (Guard_C_Rule cd c e) y cs = guardCons cd c ((e Curry_Prelude.=?= y) (addCs c cs))
  (=?=) (Fail_C_Rule cd info) _ _ = failCons cd info
  (=?=) z (Choice_C_Rule cd i x y) cs = narrow cd i ((z Curry_Prelude.=?= x) cs) ((z Curry_Prelude.=?= y) cs)
  (=?=) y (Choices_C_Rule cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.=?= x) cs) xs
  (=?=) y (Guard_C_Rule cd c e) cs = guardCons cd c ((y Curry_Prelude.=?= e) (addCs c cs))
  (=?=) _ (Fail_C_Rule cd info) _ = failCons cd info
  (=?=) (C_Rule x1 x2) (C_Rule y1 y2) cs = Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.=?= y2) cs) cs
  (<?=) (Choice_C_Rule cd i x y) z cs = narrow cd i ((x Curry_Prelude.<?= z) cs) ((y Curry_Prelude.<?= z) cs)
  (<?=) (Choices_C_Rule cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.<?= y) cs) xs
  (<?=) (Guard_C_Rule cd c e) y cs = guardCons cd c ((e Curry_Prelude.<?= y) (addCs c cs))
  (<?=) (Fail_C_Rule cd info) _ _ = failCons cd info
  (<?=) z (Choice_C_Rule cd i x y) cs = narrow cd i ((z Curry_Prelude.<?= x) cs) ((z Curry_Prelude.<?= y) cs)
  (<?=) y (Choices_C_Rule cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.<?= x) cs) xs
  (<?=) y (Guard_C_Rule cd c e) cs = guardCons cd c ((y Curry_Prelude.<?= e) (addCs c cs))
  (<?=) _ (Fail_C_Rule cd info) _ = failCons cd info
  (<?=) (C_Rule x1 x2) (C_Rule y1 y2) cs = Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_lt x1 y1 cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.<?= y2) cs) cs) cs


instance Coverable C_Rule where
  cover (C_Rule x1 x2) = C_Rule (cover x1) (cover x2)
  cover (Choice_C_Rule cd i x y) = Choice_C_Rule (incCover cd) i (cover x) (cover y)
  cover (Choices_C_Rule cd i xs) = Choices_C_Rule (incCover cd) i (map cover xs)
  cover (Fail_C_Rule cd info) = Fail_C_Rule (incCover cd) info
  cover (Guard_C_Rule cd c e) = Guard_C_Rule (incCover cd) c (cover e)


d_C_terminalValue :: Curry_Prelude.Curry t0 => C_Token t0 -> ConstStore -> t0
d_C_terminalValue x1 x3500 = case x1 of
     (C_Terminal x2 x3) -> x2
     (Choice_C_Token x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_terminalValue x1002 x3500) (d_C_terminalValue x1003 x3500)
     (Choices_C_Token x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_terminalValue z x3500) x1002
     (Guard_C_Token x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_terminalValue x1002) $! (addCs x1001 x3500))
     (Fail_C_Token x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_terminalPos :: Curry_Prelude.Curry t0 => C_Token t0 -> ConstStore -> Curry_Prelude.C_Int
d_C_terminalPos x1 x3500 = case x1 of
     (C_Terminal x2 x3) -> x3
     (Choice_C_Token x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_terminalPos x1002 x3500) (d_C_terminalPos x1003 x3500)
     (Choices_C_Token x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_terminalPos z x3500) x1002
     (Guard_C_Token x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_terminalPos x1002) $! (addCs x1001 x3500))
     (Fail_C_Token x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getBinding :: Curry_Prelude.Curry t0 => Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t0))) -> ConstStore -> Curry_Prelude.OP_List (C_Token t0)
d_C_getBinding x1 x3500 = Curry_Prelude.d_OP_dot (Curry_Maybe.d_C_fromMaybe (Curry_Prelude.d_C_error Curry_Prelude.OP_List x3500)) (Curry_Prelude.d_C_lookup x1) x3500

nd_C_getBinding :: Curry_Prelude.Curry t0 => Curry_Prelude.OP_List Curry_Prelude.C_Char -> IDSupply -> ConstStore -> Func (Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t0)))) (Curry_Prelude.OP_List (C_Token t0))
nd_C_getBinding x1 x3000 x3500 = let
     x2000 = x3000
      in (seq x2000 (Curry_Prelude.nd_OP_dot (wrapDX id (Curry_Maybe.d_C_fromMaybe (Curry_Prelude.d_C_error Curry_Prelude.OP_List x3500))) (wrapDX id (Curry_Prelude.d_C_lookup x1)) x2000 x3500))

d_C_getSingleBinding :: Curry_Prelude.Curry t0 => Curry_Prelude.OP_List Curry_Prelude.C_Char -> Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t0))) -> ConstStore -> C_Token t0
d_C_getSingleBinding x1 x2 x3500 = let
     x3 = Curry_Prelude.d_C_apply (d_C_getBinding x1 x3500) x2 x3500
      in (d_OP__case_6 x3 (Curry_Prelude.d_C_null x3 x3500) x3500)

d_C_ifMaybe :: Curry_Prelude.Curry t0 => Curry_Prelude.C_Bool -> t0 -> ConstStore -> Curry_Prelude.C_Maybe t0
d_C_ifMaybe x1 x2 x3500 = case x1 of
     Curry_Prelude.C_True -> Curry_Prelude.C_Just x2
     Curry_Prelude.C_False -> Curry_Prelude.C_Nothing
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_ifMaybe x1002 x2 x3500) (d_C_ifMaybe x1003 x2 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_ifMaybe z x2 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_ifMaybe x1002 x2) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_bindPatternToken :: Curry_Prelude.Curry t0 => C_PToken -> C_Token t0 -> ConstStore -> Curry_Prelude.C_Maybe (Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t0))))
d_C_bindPatternToken x1 x2 x3500 = case x2 of
     (C_Terminal x3 x4) -> Curry_Prelude.C_Nothing
     (C_Nonterminal x5 x6) -> d_OP__case_5 x2 x5 x6 x1 x3500
     (Choice_C_Token x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_bindPatternToken x1 x1002 x3500) (d_C_bindPatternToken x1 x1003 x3500)
     (Choices_C_Token x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_bindPatternToken x1 z x3500) x1002
     (Guard_C_Token x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_bindPatternToken x1 x1002) $! (addCs x1001 x3500))
     (Fail_C_Token x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_bindPatternToken_dot_f_dot_21 :: (Curry_Prelude.Curry t0,Curry_Prelude.Curry t1) => Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.C_Maybe t0) t1) -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 t0 t1)
d_OP_bindPatternToken_dot_f_dot_21 x1 x3500 = case x1 of
     Curry_Prelude.OP_List -> Curry_Prelude.OP_List
     (Curry_Prelude.OP_Cons x2 x3) -> d_OP__case_4 x3 x2 x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_bindPatternToken_dot_f_dot_21 x1002 x3500) (d_OP_bindPatternToken_dot_f_dot_21 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_bindPatternToken_dot_f_dot_21 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_bindPatternToken_dot_f_dot_21 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_bindPattern :: Curry_Prelude.Curry t0 => Curry_Prelude.OP_List C_PToken -> Curry_Prelude.OP_List (C_Token t0) -> ConstStore -> Curry_Prelude.C_Maybe (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t0)))) (Curry_Prelude.OP_List (C_Token t0)))
d_C_bindPattern x1 x2 x3500 = case x1 of
     Curry_Prelude.OP_List -> Curry_Prelude.C_Just (Curry_Prelude.OP_Tuple2 Curry_Prelude.OP_List x2)
     (Curry_Prelude.OP_Cons x3 x4) -> d_OP__case_2 x3 x4 x2 x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_bindPattern x1002 x2 x3500) (d_C_bindPattern x1003 x2 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_bindPattern z x2 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_bindPattern x1002 x2) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_bindPattern_dot___hash_lambda1 :: Curry_Prelude.Curry t85 => C_Token t85 -> C_PToken -> Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t85)))) (Curry_Prelude.OP_List (C_Token t85)) -> ConstStore -> Curry_Prelude.C_Maybe (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t85)))) (Curry_Prelude.OP_List (C_Token t85)))
d_OP_bindPattern_dot___hash_lambda1 x1 x2 x3 x3500 = case x3 of
     (Curry_Prelude.OP_Tuple2 x4 x5) -> Curry_Maybe.d_OP_gt_gt_minus (d_C_bindPatternToken x2 x1 x3500) (d_OP_bindPattern_dot___hash_lambda1_dot___hash_lambda2 x4 x5) x3500
     (Curry_Prelude.Choice_OP_Tuple2 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_bindPattern_dot___hash_lambda1 x1 x2 x1002 x3500) (d_OP_bindPattern_dot___hash_lambda1 x1 x2 x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple2 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_bindPattern_dot___hash_lambda1 x1 x2 z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple2 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_bindPattern_dot___hash_lambda1 x1 x2 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple2 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_bindPattern_dot___hash_lambda1_dot___hash_lambda2 :: Curry_Prelude.Curry t85 => Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t85))) -> Curry_Prelude.OP_List (C_Token t85) -> Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t85))) -> ConstStore -> Curry_Prelude.C_Maybe (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t85)))) (Curry_Prelude.OP_List (C_Token t85)))
d_OP_bindPattern_dot___hash_lambda1_dot___hash_lambda2 x1 x2 x3 x3500 = Curry_Prelude.C_Just (Curry_Prelude.OP_Tuple2 (Curry_Prelude.d_OP_plus_plus x1 x3 x3500) x2)

d_C_instantiateTemplateToken :: Curry_Prelude.Curry t0 => C_TToken -> Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t0))) -> ConstStore -> C_Token t0
d_C_instantiateTemplateToken x1 x2 x3500 = case x1 of
     (C_PTokenRef x3) -> d_C_getSingleBinding x3 x2 x3500
     (C_TToken x4 x5) -> Curry_Prelude.d_OP_dollar (acceptCs id (C_Nonterminal x4)) (Curry_Prelude.d_C_map (Curry_Prelude.d_C_concatMap (d_OP_instantiateTemplateToken_dot___hash_lambda3 x2) x3500) x5 x3500) x3500
     (Choice_C_TToken x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_instantiateTemplateToken x1002 x2 x3500) (d_C_instantiateTemplateToken x1003 x2 x3500)
     (Choices_C_TToken x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_instantiateTemplateToken z x2 x3500) x1002
     (Guard_C_TToken x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_instantiateTemplateToken x1002 x2) $! (addCs x1001 x3500))
     (Fail_C_TToken x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_instantiateTemplateToken_dot___hash_lambda3 :: Curry_Prelude.Curry t109 => Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t109))) -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.OP_List (C_Token t109)
d_OP_instantiateTemplateToken_dot___hash_lambda3 x1 x2 x3500 = Curry_Prelude.d_C_apply (d_C_getBinding x2 x3500) x1 x3500

d_C_instantiate :: Curry_Prelude.Curry t0 => Curry_Prelude.OP_List C_TToken -> Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t0))) -> ConstStore -> Curry_Prelude.OP_List (C_Token t0)
d_C_instantiate x1 x2 x3500 = Curry_Prelude.d_C_map (d_OP_instantiate_dot___hash_lambda4 x2) x1 x3500

d_OP_instantiate_dot___hash_lambda4 :: Curry_Prelude.Curry t116 => Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t116))) -> C_TToken -> ConstStore -> C_Token t116
d_OP_instantiate_dot___hash_lambda4 x1 x2 x3500 = d_C_instantiateTemplateToken x2 x1 x3500

d_C_reduceHeadUsingRule :: Curry_Prelude.Curry t0 => C_Rule -> Curry_Prelude.OP_List (C_Token t0) -> ConstStore -> Curry_Prelude.C_Maybe (Curry_Prelude.OP_List (C_Token t0))
d_C_reduceHeadUsingRule x1 x2 x3500 = case x1 of
     (C_Rule x3 x4) -> Curry_Maybe.d_OP_gt_gt_minus (d_C_bindPattern x3 x2 x3500) (d_OP_reduceHeadUsingRule_dot___hash_lambda5 x4) x3500
     (Choice_C_Rule x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_reduceHeadUsingRule x1002 x2 x3500) (d_C_reduceHeadUsingRule x1003 x2 x3500)
     (Choices_C_Rule x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_reduceHeadUsingRule z x2 x3500) x1002
     (Guard_C_Rule x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_reduceHeadUsingRule x1002 x2) $! (addCs x1001 x3500))
     (Fail_C_Rule x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_reduceHeadUsingRule_dot___hash_lambda5 :: Curry_Prelude.Curry t130 => Curry_Prelude.OP_List C_TToken -> Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (C_Token t130)))) (Curry_Prelude.OP_List (C_Token t130)) -> ConstStore -> Curry_Prelude.C_Maybe (Curry_Prelude.OP_List (C_Token t130))
d_OP_reduceHeadUsingRule_dot___hash_lambda5 x1 x2 x3500 = case x2 of
     (Curry_Prelude.OP_Tuple2 x3 x4) -> Curry_Prelude.d_OP_dollar (acceptCs id Curry_Prelude.C_Just) (Curry_Prelude.d_OP_plus_plus (d_C_instantiate x1 x3 x3500) x4 x3500) x3500
     (Curry_Prelude.Choice_OP_Tuple2 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_reduceHeadUsingRule_dot___hash_lambda5 x1 x1002 x3500) (d_OP_reduceHeadUsingRule_dot___hash_lambda5 x1 x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple2 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_reduceHeadUsingRule_dot___hash_lambda5 x1 z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple2 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_reduceHeadUsingRule_dot___hash_lambda5 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple2 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_reduceHead :: Curry_Prelude.Curry t0 => Curry_Prelude.OP_List C_Rule -> Curry_Prelude.OP_List (C_Token t0) -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_List (C_Token t0))
d_C_reduceHead x1 x2 x3500 = Curry_Prelude.d_C_apply (Curry_Maybe.d_C_mapMaybe (Curry_Prelude.d_C_flip (acceptCs id d_C_reduceHeadUsingRule) x2) x3500) x1 x3500

d_C_reduce :: Curry_Prelude.Curry t0 => Curry_Prelude.OP_List C_Rule -> Curry_Prelude.OP_List (C_Token t0) -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_List (C_Token t0))
d_C_reduce x1 x2 x3500 = case x2 of
     Curry_Prelude.OP_List -> Curry_Prelude.OP_List
     (Curry_Prelude.OP_Cons x3 x4) -> Curry_Prelude.d_OP_plus_plus (d_C_reduceHead x1 x2 x3500) (Curry_Prelude.d_OP_dollar (Curry_Prelude.d_C_map (acceptCs id (Curry_Prelude.OP_Cons x3))) (d_C_reduce x1 x4 x3500) x3500) x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_reduce x1 x1002 x3500) (d_C_reduce x1 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_reduce x1 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_reduce x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_parse' :: Curry_Prelude.Curry t0 => Curry_Prelude.OP_List C_Rule -> Curry_Prelude.OP_List (Curry_Prelude.OP_List (C_Token t0)) -> Curry_Prelude.OP_List (Curry_Prelude.OP_List (C_Token t0)) -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_List (C_Token t0))
d_C_parse' x1 x2 x3 x3500 = case x3 of
     Curry_Prelude.OP_List -> x2
     (Curry_Prelude.OP_Cons x4 x5) -> d_OP__case_1 x1 x2 x4 x5 (Curry_Prelude.d_C_apply (Curry_Prelude.d_C_elem x4 x3500) x2 x3500) x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_parse' x1 x2 x1002 x3500) (d_C_parse' x1 x2 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_parse' x1 x2 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_parse' x1 x2 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_parse :: Curry_Prelude.Curry t0 => Curry_Prelude.OP_List C_Rule -> Curry_Prelude.OP_List (C_Token t0) -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_List (C_Token t0))
d_C_parse x1 x2 x3500 = d_C_parse' x1 Curry_Prelude.OP_List (Curry_Prelude.OP_Cons x2 Curry_Prelude.OP_List) x3500

d_OP__case_1 x1 x2 x4 x5 x6 x3500 = case x6 of
     Curry_Prelude.C_True -> d_C_parse' x1 x2 x5 x3500
     Curry_Prelude.C_False -> d_OP__case_0 x1 x2 x4 x5 (Curry_Prelude.d_C_otherwise x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_1 x1 x2 x4 x5 x1002 x3500) (d_OP__case_1 x1 x2 x4 x5 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_1 x1 x2 x4 x5 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_1 x1 x2 x4 x5 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_1 x1 x2 x4 x5 x6 x3000 x3500 = case x6 of
     Curry_Prelude.C_True -> d_C_parse' x1 x2 x5 x3500
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_0 x1 x2 x4 x5 (Curry_Prelude.d_C_otherwise x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_1 x1 x2 x4 x5 x1002 x3000 x3500) (nd_OP__case_1 x1 x2 x4 x5 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_1 x1 x2 x4 x5 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_1 x1 x2 x4 x5 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_0 x1 x2 x4 x5 x7 x3500 = case x7 of
     Curry_Prelude.C_True -> let
          x6 = d_C_reduce x1 x4 x3500
           in (d_C_parse' x1 (Curry_Prelude.OP_Cons x4 x2) (Curry_Prelude.d_OP_plus_plus x5 x6 x3500) x3500)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_0 x1 x2 x4 x5 x1002 x3500) (d_OP__case_0 x1 x2 x4 x5 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_0 x1 x2 x4 x5 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_0 x1 x2 x4 x5 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_0 x1 x2 x4 x5 x7 x3000 x3500 = case x7 of
     Curry_Prelude.C_True -> let
          x6 = d_C_reduce x1 x4 x3500
           in (d_C_parse' x1 (Curry_Prelude.OP_Cons x4 x2) (Curry_Prelude.d_OP_plus_plus x5 x6 x3500) x3500)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_0 x1 x2 x4 x5 x1002 x3000 x3500) (nd_OP__case_0 x1 x2 x4 x5 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_0 x1 x2 x4 x5 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_0 x1 x2 x4 x5 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_2 x3 x4 x2 x3500 = case x2 of
     Curry_Prelude.OP_List -> Curry_Prelude.C_Nothing
     (Curry_Prelude.OP_Cons x5 x6) -> Curry_Maybe.d_OP_gt_gt_minus (d_C_bindPattern x4 x6 x3500) (d_OP_bindPattern_dot___hash_lambda1 x5 x3) x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_2 x3 x4 x1002 x3500) (d_OP__case_2 x3 x4 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_2 x3 x4 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_2 x3 x4 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_2 x3 x4 x2 x3000 x3500 = case x2 of
     Curry_Prelude.OP_List -> Curry_Prelude.C_Nothing
     (Curry_Prelude.OP_Cons x5 x6) -> let
          x2000 = x3000
           in (seq x2000 (Curry_Maybe.nd_OP_gt_gt_minus (d_C_bindPattern x4 x6 x3500) (wrapDX id (d_OP_bindPattern_dot___hash_lambda1 x5 x3)) x2000 x3500))
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_2 x3 x4 x1002 x3000 x3500) (nd_OP__case_2 x3 x4 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_2 x3 x4 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_2 x3 x4 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_4 x3 x2 x3500 = case x2 of
     (Curry_Prelude.OP_Tuple2 x4 x5) -> d_OP__case_3 x3 x5 x4 x3500
     (Curry_Prelude.Choice_OP_Tuple2 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_4 x3 x1002 x3500) (d_OP__case_4 x3 x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple2 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_4 x3 z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple2 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_4 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple2 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_4 x3 x2 x3000 x3500 = case x2 of
     (Curry_Prelude.OP_Tuple2 x4 x5) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_3 x3 x5 x4 x2000 x3500))
     (Curry_Prelude.Choice_OP_Tuple2 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_4 x3 x1002 x3000 x3500) (nd_OP__case_4 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_Tuple2 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_4 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple2 x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_4 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple2 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_3 x3 x5 x4 x3500 = case x4 of
     Curry_Prelude.C_Nothing -> d_OP_bindPatternToken_dot_f_dot_21 x3 x3500
     (Curry_Prelude.C_Just x6) -> Curry_Prelude.OP_Cons (Curry_Prelude.OP_Tuple2 x6 x5) (d_OP_bindPatternToken_dot_f_dot_21 x3 x3500)
     (Curry_Prelude.Choice_C_Maybe x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_3 x3 x5 x1002 x3500) (d_OP__case_3 x3 x5 x1003 x3500)
     (Curry_Prelude.Choices_C_Maybe x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_3 x3 x5 z x3500) x1002
     (Curry_Prelude.Guard_C_Maybe x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_3 x3 x5 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Maybe x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_3 x3 x5 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_Nothing -> d_OP_bindPatternToken_dot_f_dot_21 x3 x3500
     (Curry_Prelude.C_Just x6) -> Curry_Prelude.OP_Cons (Curry_Prelude.OP_Tuple2 x6 x5) (d_OP_bindPatternToken_dot_f_dot_21 x3 x3500)
     (Curry_Prelude.Choice_C_Maybe x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_3 x3 x5 x1002 x3000 x3500) (nd_OP__case_3 x3 x5 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Maybe x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_3 x3 x5 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Maybe x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_3 x3 x5 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Maybe x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_5 x2 x5 x6 x1 x3500 = case x1 of
     (C_PToken x7 x8 x9) -> d_C_ifMaybe (Curry_Prelude.d_OP_eq_eq x7 x5 x3500) (d_OP_bindPatternToken_dot_f_dot_21 (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Tuple2 x8 (Curry_Prelude.OP_Cons x2 Curry_Prelude.OP_List)) (Curry_Prelude.d_C_zip x9 x6 x3500)) x3500) x3500
     (Choice_C_PToken x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_5 x2 x5 x6 x1002 x3500) (d_OP__case_5 x2 x5 x6 x1003 x3500)
     (Choices_C_PToken x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_5 x2 x5 x6 z x3500) x1002
     (Guard_C_PToken x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_5 x2 x5 x6 x1002) $! (addCs x1001 x3500))
     (Fail_C_PToken x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_5 x2 x5 x6 x1 x3000 x3500 = case x1 of
     (C_PToken x7 x8 x9) -> d_C_ifMaybe (Curry_Prelude.d_OP_eq_eq x7 x5 x3500) (d_OP_bindPatternToken_dot_f_dot_21 (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Tuple2 x8 (Curry_Prelude.OP_Cons x2 Curry_Prelude.OP_List)) (Curry_Prelude.d_C_zip x9 x6 x3500)) x3500) x3500
     (Choice_C_PToken x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_5 x2 x5 x6 x1002 x3000 x3500) (nd_OP__case_5 x2 x5 x6 x1003 x3000 x3500)
     (Choices_C_PToken x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_5 x2 x5 x6 z x3000 x3500) x1002
     (Guard_C_PToken x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_5 x2 x5 x6 x1002 x3000) $! (addCs x1001 x3500))
     (Fail_C_PToken x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_6 x3 x4 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Prelude.d_C_error Curry_Prelude.OP_List x3500
     Curry_Prelude.C_False -> Curry_Prelude.d_C_head x3 x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_6 x3 x1002 x3500) (d_OP__case_6 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_6 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_6 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_6 x3 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Prelude.d_C_error Curry_Prelude.OP_List x3500
     Curry_Prelude.C_False -> Curry_Prelude.d_C_head x3 x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_6 x3 x1002 x3000 x3500) (nd_OP__case_6 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_6 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_6 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo
