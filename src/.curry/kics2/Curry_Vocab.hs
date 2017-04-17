{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module Curry_Vocab (C_Pos (..), C_Word (..), C_Vocab, d_C_posToString, d_C_posFromString, d_C_wordName, d_C_wordPos, d_C_isPos', nd_C_isPos', d_C_addWord, d_C_addWords, d_C_getWord, d_C_isPos, d_C_isAdjective, nd_C_isAdjective, d_C_isAdverb, nd_C_isAdverb, d_C_isArticle, nd_C_isArticle, d_C_isPreposition, nd_C_isPreposition, d_C_isPronoun, nd_C_isPronoun, d_C_removeSuffix, d_C_isNoun, d_C_isVerb, d_C_loadVocab, d_C_vocabToXML, nd_C_vocabToXML, d_C_writeVocab, nd_C_writeVocab) where

import Basics
import qualified Curry_BinarySort
import qualified Curry_List
import qualified Curry_Maybe
import qualified Curry_Prelude
import qualified Curry_XML
import qualified Curry_XML2
type C_Vocab = Curry_Prelude.OP_List C_Word

data C_Pos
     = C_Adjective
     | C_Adverb
     | C_Article
     | C_Noun
     | C_Preposition
     | C_Pronoun
     | C_Verb
     | Choice_C_Pos Cover ID C_Pos C_Pos
     | Choices_C_Pos Cover ID ([C_Pos])
     | Fail_C_Pos Cover FailInfo
     | Guard_C_Pos Cover Constraints C_Pos

instance Show C_Pos where
  showsPrec d (Choice_C_Pos cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_Pos cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_Pos cd c e) = showsGuard d cd c e
  showsPrec _ (Fail_C_Pos cd info) = showChar '!'
  showsPrec _ C_Adjective = showString "Adjective"
  showsPrec _ C_Adverb = showString "Adverb"
  showsPrec _ C_Article = showString "Article"
  showsPrec _ C_Noun = showString "Noun"
  showsPrec _ C_Preposition = showString "Preposition"
  showsPrec _ C_Pronoun = showString "Pronoun"
  showsPrec _ C_Verb = showString "Verb"


instance Read C_Pos where
  readsPrec _ s = (readParen False (\r -> [ (C_Adjective,r0) | (_,r0) <- readQualified "Vocab" "Adjective" r]) s) ++ ((readParen False (\r -> [ (C_Adverb,r0) | (_,r0) <- readQualified "Vocab" "Adverb" r]) s) ++ ((readParen False (\r -> [ (C_Article,r0) | (_,r0) <- readQualified "Vocab" "Article" r]) s) ++ ((readParen False (\r -> [ (C_Noun,r0) | (_,r0) <- readQualified "Vocab" "Noun" r]) s) ++ ((readParen False (\r -> [ (C_Preposition,r0) | (_,r0) <- readQualified "Vocab" "Preposition" r]) s) ++ ((readParen False (\r -> [ (C_Pronoun,r0) | (_,r0) <- readQualified "Vocab" "Pronoun" r]) s) ++ (readParen False (\r -> [ (C_Verb,r0) | (_,r0) <- readQualified "Vocab" "Verb" r]) s))))))


instance NonDet C_Pos where
  choiceCons = Choice_C_Pos
  choicesCons = Choices_C_Pos
  failCons = Fail_C_Pos
  guardCons = Guard_C_Pos
  try (Choice_C_Pos cd i x y) = tryChoice cd i x y
  try (Choices_C_Pos cd i xs) = tryChoices cd i xs
  try (Fail_C_Pos cd info) = Fail cd info
  try (Guard_C_Pos cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_Pos cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_Pos cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_Pos cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_Pos cd i _) = error ("Vocab.Pos.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_Pos cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_Pos cd c e) = f cd c e
  match _ _ _ _ _ f x = f x


instance Generable C_Pos where
  generate s = Choices_C_Pos defCover (freeID [0,0,0,0,0,0,0] s) [C_Adjective,C_Adverb,C_Article,C_Noun,C_Preposition,C_Pronoun,C_Verb]


instance NormalForm C_Pos where
  ($!!) cont C_Adjective cs = cont C_Adjective cs
  ($!!) cont C_Adverb cs = cont C_Adverb cs
  ($!!) cont C_Article cs = cont C_Article cs
  ($!!) cont C_Noun cs = cont C_Noun cs
  ($!!) cont C_Preposition cs = cont C_Preposition cs
  ($!!) cont C_Pronoun cs = cont C_Pronoun cs
  ($!!) cont C_Verb cs = cont C_Verb cs
  ($!!) cont (Choice_C_Pos cd i x y) cs = nfChoice cont cd i x y cs
  ($!!) cont (Choices_C_Pos cd i xs) cs = nfChoices cont cd i xs cs
  ($!!) cont (Guard_C_Pos cd c e) cs = guardCons cd c ((cont $!! e) (addCs c cs))
  ($!!) _ (Fail_C_Pos cd info) _ = failCons cd info
  ($##) cont C_Adjective cs = cont C_Adjective cs
  ($##) cont C_Adverb cs = cont C_Adverb cs
  ($##) cont C_Article cs = cont C_Article cs
  ($##) cont C_Noun cs = cont C_Noun cs
  ($##) cont C_Preposition cs = cont C_Preposition cs
  ($##) cont C_Pronoun cs = cont C_Pronoun cs
  ($##) cont C_Verb cs = cont C_Verb cs
  ($##) cont (Choice_C_Pos cd i x y) cs = gnfChoice cont cd i x y cs
  ($##) cont (Choices_C_Pos cd i xs) cs = gnfChoices cont cd i xs cs
  ($##) cont (Guard_C_Pos cd c e) cs = guardCons cd c ((cont $## e) (addCs c cs))
  ($##) _ (Fail_C_Pos cd info) _ = failCons cd info
  ($!<) cont C_Adjective = cont C_Adjective
  ($!<) cont C_Adverb = cont C_Adverb
  ($!<) cont C_Article = cont C_Article
  ($!<) cont C_Noun = cont C_Noun
  ($!<) cont C_Preposition = cont C_Preposition
  ($!<) cont C_Pronoun = cont C_Pronoun
  ($!<) cont C_Verb = cont C_Verb
  ($!<) cont (Choice_C_Pos cd i x y) = nfChoiceIO cont cd i x y
  ($!<) cont (Choices_C_Pos cd i xs) = nfChoicesIO cont cd i xs
  ($!<) cont x = cont x
  searchNF _ cont C_Adjective = cont C_Adjective
  searchNF _ cont C_Adverb = cont C_Adverb
  searchNF _ cont C_Article = cont C_Article
  searchNF _ cont C_Noun = cont C_Noun
  searchNF _ cont C_Preposition = cont C_Preposition
  searchNF _ cont C_Pronoun = cont C_Pronoun
  searchNF _ cont C_Verb = cont C_Verb
  searchNF _ _ x = error ("Vocab.Pos.searchNF: no constructor: " ++ (show x))


instance Unifiable C_Pos where
  (=.=) C_Adjective C_Adjective cs = C_Success
  (=.=) C_Adverb C_Adverb cs = C_Success
  (=.=) C_Article C_Article cs = C_Success
  (=.=) C_Noun C_Noun cs = C_Success
  (=.=) C_Preposition C_Preposition cs = C_Success
  (=.=) C_Pronoun C_Pronoun cs = C_Success
  (=.=) C_Verb C_Verb cs = C_Success
  (=.=) _ _ _ = Fail_C_Success defCover defFailInfo
  (=.<=) C_Adjective C_Adjective cs = C_Success
  (=.<=) C_Adverb C_Adverb cs = C_Success
  (=.<=) C_Article C_Article cs = C_Success
  (=.<=) C_Noun C_Noun cs = C_Success
  (=.<=) C_Preposition C_Preposition cs = C_Success
  (=.<=) C_Pronoun C_Pronoun cs = C_Success
  (=.<=) C_Verb C_Verb cs = C_Success
  (=.<=) _ _ _ = Fail_C_Success defCover defFailInfo
  bind i C_Adjective = ((i :=: (ChooseN 0 0)):(concat []))
  bind i C_Adverb = ((i :=: (ChooseN 1 0)):(concat []))
  bind i C_Article = ((i :=: (ChooseN 2 0)):(concat []))
  bind i C_Noun = ((i :=: (ChooseN 3 0)):(concat []))
  bind i C_Preposition = ((i :=: (ChooseN 4 0)):(concat []))
  bind i C_Pronoun = ((i :=: (ChooseN 5 0)):(concat []))
  bind i C_Verb = ((i :=: (ChooseN 6 0)):(concat []))
  bind i (Choice_C_Pos cd j x y) = [(ConstraintChoice cd j (bind i x) (bind i y))]
  bind i (Choices_C_Pos cd j@(FreeID _ _) xs) = bindOrNarrow i cd j xs
  bind i (Choices_C_Pos cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (bind i) xs))]
  bind _ (Choices_C_Pos cd i _) = error ("Vocab.Pos.bind: Choices with ChoiceID: " ++ (show i))
  bind _ (Fail_C_Pos cd info) = [(Unsolvable info)]
  bind i (Guard_C_Pos cd c e) = (getConstrList c) ++ (bind i e)
  lazyBind i C_Adjective = [(i :=: (ChooseN 0 0))]
  lazyBind i C_Adverb = [(i :=: (ChooseN 1 0))]
  lazyBind i C_Article = [(i :=: (ChooseN 2 0))]
  lazyBind i C_Noun = [(i :=: (ChooseN 3 0))]
  lazyBind i C_Preposition = [(i :=: (ChooseN 4 0))]
  lazyBind i C_Pronoun = [(i :=: (ChooseN 5 0))]
  lazyBind i C_Verb = [(i :=: (ChooseN 6 0))]
  lazyBind i (Choice_C_Pos cd j x y) = [(ConstraintChoice cd j (lazyBind i x) (lazyBind i y))]
  lazyBind i (Choices_C_Pos cd j@(FreeID _ _) xs) = lazyBindOrNarrow i cd j xs
  lazyBind i (Choices_C_Pos cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (lazyBind i) xs))]
  lazyBind _ (Choices_C_Pos cd i _) = error ("Vocab.Pos.lazyBind: Choices with ChoiceID: " ++ (show i))
  lazyBind _ (Fail_C_Pos cd info) = [(Unsolvable info)]
  lazyBind i (Guard_C_Pos cd c e) = (getConstrList c) ++ [(i :=: (LazyBind (lazyBind i e)))]


instance Curry_Prelude.Curry C_Pos where
  (=?=) (Choice_C_Pos cd i x y) z cs = narrow cd i ((x Curry_Prelude.=?= z) cs) ((y Curry_Prelude.=?= z) cs)
  (=?=) (Choices_C_Pos cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.=?= y) cs) xs
  (=?=) (Guard_C_Pos cd c e) y cs = guardCons cd c ((e Curry_Prelude.=?= y) (addCs c cs))
  (=?=) (Fail_C_Pos cd info) _ _ = failCons cd info
  (=?=) z (Choice_C_Pos cd i x y) cs = narrow cd i ((z Curry_Prelude.=?= x) cs) ((z Curry_Prelude.=?= y) cs)
  (=?=) y (Choices_C_Pos cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.=?= x) cs) xs
  (=?=) y (Guard_C_Pos cd c e) cs = guardCons cd c ((y Curry_Prelude.=?= e) (addCs c cs))
  (=?=) _ (Fail_C_Pos cd info) _ = failCons cd info
  (=?=) C_Adjective C_Adjective cs = Curry_Prelude.C_True
  (=?=) C_Adverb C_Adverb cs = Curry_Prelude.C_True
  (=?=) C_Article C_Article cs = Curry_Prelude.C_True
  (=?=) C_Noun C_Noun cs = Curry_Prelude.C_True
  (=?=) C_Preposition C_Preposition cs = Curry_Prelude.C_True
  (=?=) C_Pronoun C_Pronoun cs = Curry_Prelude.C_True
  (=?=) C_Verb C_Verb cs = Curry_Prelude.C_True
  (=?=) _ _ _ = Curry_Prelude.C_False
  (<?=) (Choice_C_Pos cd i x y) z cs = narrow cd i ((x Curry_Prelude.<?= z) cs) ((y Curry_Prelude.<?= z) cs)
  (<?=) (Choices_C_Pos cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.<?= y) cs) xs
  (<?=) (Guard_C_Pos cd c e) y cs = guardCons cd c ((e Curry_Prelude.<?= y) (addCs c cs))
  (<?=) (Fail_C_Pos cd info) _ _ = failCons cd info
  (<?=) z (Choice_C_Pos cd i x y) cs = narrow cd i ((z Curry_Prelude.<?= x) cs) ((z Curry_Prelude.<?= y) cs)
  (<?=) y (Choices_C_Pos cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.<?= x) cs) xs
  (<?=) y (Guard_C_Pos cd c e) cs = guardCons cd c ((y Curry_Prelude.<?= e) (addCs c cs))
  (<?=) _ (Fail_C_Pos cd info) _ = failCons cd info
  (<?=) C_Adjective C_Adjective cs = Curry_Prelude.C_True
  (<?=) C_Adjective C_Adverb _ = Curry_Prelude.C_True
  (<?=) C_Adjective C_Article _ = Curry_Prelude.C_True
  (<?=) C_Adjective C_Noun _ = Curry_Prelude.C_True
  (<?=) C_Adjective C_Preposition _ = Curry_Prelude.C_True
  (<?=) C_Adjective C_Pronoun _ = Curry_Prelude.C_True
  (<?=) C_Adjective C_Verb _ = Curry_Prelude.C_True
  (<?=) C_Adverb C_Adverb cs = Curry_Prelude.C_True
  (<?=) C_Adverb C_Article _ = Curry_Prelude.C_True
  (<?=) C_Adverb C_Noun _ = Curry_Prelude.C_True
  (<?=) C_Adverb C_Preposition _ = Curry_Prelude.C_True
  (<?=) C_Adverb C_Pronoun _ = Curry_Prelude.C_True
  (<?=) C_Adverb C_Verb _ = Curry_Prelude.C_True
  (<?=) C_Article C_Article cs = Curry_Prelude.C_True
  (<?=) C_Article C_Noun _ = Curry_Prelude.C_True
  (<?=) C_Article C_Preposition _ = Curry_Prelude.C_True
  (<?=) C_Article C_Pronoun _ = Curry_Prelude.C_True
  (<?=) C_Article C_Verb _ = Curry_Prelude.C_True
  (<?=) C_Noun C_Noun cs = Curry_Prelude.C_True
  (<?=) C_Noun C_Preposition _ = Curry_Prelude.C_True
  (<?=) C_Noun C_Pronoun _ = Curry_Prelude.C_True
  (<?=) C_Noun C_Verb _ = Curry_Prelude.C_True
  (<?=) C_Preposition C_Preposition cs = Curry_Prelude.C_True
  (<?=) C_Preposition C_Pronoun _ = Curry_Prelude.C_True
  (<?=) C_Preposition C_Verb _ = Curry_Prelude.C_True
  (<?=) C_Pronoun C_Pronoun cs = Curry_Prelude.C_True
  (<?=) C_Pronoun C_Verb _ = Curry_Prelude.C_True
  (<?=) C_Verb C_Verb cs = Curry_Prelude.C_True
  (<?=) _ _ _ = Curry_Prelude.C_False


instance Coverable C_Pos where
  cover C_Adjective = C_Adjective
  cover C_Adverb = C_Adverb
  cover C_Article = C_Article
  cover C_Noun = C_Noun
  cover C_Preposition = C_Preposition
  cover C_Pronoun = C_Pronoun
  cover C_Verb = C_Verb
  cover (Choice_C_Pos cd i x y) = Choice_C_Pos (incCover cd) i (cover x) (cover y)
  cover (Choices_C_Pos cd i xs) = Choices_C_Pos (incCover cd) i (map cover xs)
  cover (Fail_C_Pos cd info) = Fail_C_Pos (incCover cd) info
  cover (Guard_C_Pos cd c e) = Guard_C_Pos (incCover cd) c (cover e)


data C_Word
     = C_Word (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List C_Pos)
     | Choice_C_Word Cover ID C_Word C_Word
     | Choices_C_Word Cover ID ([C_Word])
     | Fail_C_Word Cover FailInfo
     | Guard_C_Word Cover Constraints C_Word

instance Show C_Word where
  showsPrec d (Choice_C_Word cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_Word cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_Word cd c e) = showsGuard d cd c e
  showsPrec _ (Fail_C_Word cd info) = showChar '!'
  showsPrec _ (C_Word x1 x2) = (showString "(Word") . ((showChar ' ') . ((shows x1) . ((showChar ' ') . ((shows x2) . (showChar ')')))))


instance Read C_Word where
  readsPrec d s = readParen (d > 10) (\r -> [ (C_Word x1 x2,r2) | (_,r0) <- readQualified "Vocab" "Word" r, (x1,r1) <- readsPrec 11 r0, (x2,r2) <- readsPrec 11 r1]) s


instance NonDet C_Word where
  choiceCons = Choice_C_Word
  choicesCons = Choices_C_Word
  failCons = Fail_C_Word
  guardCons = Guard_C_Word
  try (Choice_C_Word cd i x y) = tryChoice cd i x y
  try (Choices_C_Word cd i xs) = tryChoices cd i xs
  try (Fail_C_Word cd info) = Fail cd info
  try (Guard_C_Word cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_Word cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_Word cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_Word cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_Word cd i _) = error ("Vocab.Word.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_Word cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_Word cd c e) = f cd c e
  match _ _ _ _ _ f x = f x


instance Generable C_Word where
  generate s = Choices_C_Word defCover (freeID [2] s) [(C_Word (generate (leftSupply s)) (generate (rightSupply s)))]


instance NormalForm C_Word where
  ($!!) cont (C_Word x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_Word y1 y2) cs) $!! x2) cs) $!! x1) cs
  ($!!) cont (Choice_C_Word cd i x y) cs = nfChoice cont cd i x y cs
  ($!!) cont (Choices_C_Word cd i xs) cs = nfChoices cont cd i xs cs
  ($!!) cont (Guard_C_Word cd c e) cs = guardCons cd c ((cont $!! e) (addCs c cs))
  ($!!) _ (Fail_C_Word cd info) _ = failCons cd info
  ($##) cont (C_Word x1 x2) cs = ((\y1 cs -> ((\y2 cs -> cont (C_Word y1 y2) cs) $## x2) cs) $## x1) cs
  ($##) cont (Choice_C_Word cd i x y) cs = gnfChoice cont cd i x y cs
  ($##) cont (Choices_C_Word cd i xs) cs = gnfChoices cont cd i xs cs
  ($##) cont (Guard_C_Word cd c e) cs = guardCons cd c ((cont $## e) (addCs c cs))
  ($##) _ (Fail_C_Word cd info) _ = failCons cd info
  ($!<) cont (C_Word x1 x2) = (\y1 -> (\y2 -> cont (C_Word y1 y2)) $!< x2) $!< x1
  ($!<) cont (Choice_C_Word cd i x y) = nfChoiceIO cont cd i x y
  ($!<) cont (Choices_C_Word cd i xs) = nfChoicesIO cont cd i xs
  ($!<) cont x = cont x
  searchNF search cont (C_Word x1 x2) = search (\y1 -> search (\y2 -> cont (C_Word y1 y2)) x2) x1
  searchNF _ _ x = error ("Vocab.Word.searchNF: no constructor: " ++ (show x))


instance Unifiable C_Word where
  (=.=) (C_Word x1 x2) (C_Word y1 y2) cs = (((x1 =:= y1) cs) & ((x2 =:= y2) cs)) cs
  (=.=) _ _ _ = Fail_C_Success defCover defFailInfo
  (=.<=) (C_Word x1 x2) (C_Word y1 y2) cs = (((x1 =:<= y1) cs) & ((x2 =:<= y2) cs)) cs
  (=.<=) _ _ _ = Fail_C_Success defCover defFailInfo
  bind i (C_Word x2 x3) = ((i :=: (ChooseN 0 2)):(concat [(bind (leftID i) x2),(bind (rightID i) x3)]))
  bind i (Choice_C_Word cd j x y) = [(ConstraintChoice cd j (bind i x) (bind i y))]
  bind i (Choices_C_Word cd j@(FreeID _ _) xs) = bindOrNarrow i cd j xs
  bind i (Choices_C_Word cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (bind i) xs))]
  bind _ (Choices_C_Word cd i _) = error ("Vocab.Word.bind: Choices with ChoiceID: " ++ (show i))
  bind _ (Fail_C_Word cd info) = [(Unsolvable info)]
  bind i (Guard_C_Word cd c e) = (getConstrList c) ++ (bind i e)
  lazyBind i (C_Word x2 x3) = [(i :=: (ChooseN 0 2)),((leftID i) :=: (LazyBind (lazyBind (leftID i) x2))),((rightID i) :=: (LazyBind (lazyBind (rightID i) x3)))]
  lazyBind i (Choice_C_Word cd j x y) = [(ConstraintChoice cd j (lazyBind i x) (lazyBind i y))]
  lazyBind i (Choices_C_Word cd j@(FreeID _ _) xs) = lazyBindOrNarrow i cd j xs
  lazyBind i (Choices_C_Word cd j@(NarrowedID _ _) xs) = [(ConstraintChoices cd j (map (lazyBind i) xs))]
  lazyBind _ (Choices_C_Word cd i _) = error ("Vocab.Word.lazyBind: Choices with ChoiceID: " ++ (show i))
  lazyBind _ (Fail_C_Word cd info) = [(Unsolvable info)]
  lazyBind i (Guard_C_Word cd c e) = (getConstrList c) ++ [(i :=: (LazyBind (lazyBind i e)))]


instance Curry_Prelude.Curry C_Word where
  (=?=) (Choice_C_Word cd i x y) z cs = narrow cd i ((x Curry_Prelude.=?= z) cs) ((y Curry_Prelude.=?= z) cs)
  (=?=) (Choices_C_Word cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.=?= y) cs) xs
  (=?=) (Guard_C_Word cd c e) y cs = guardCons cd c ((e Curry_Prelude.=?= y) (addCs c cs))
  (=?=) (Fail_C_Word cd info) _ _ = failCons cd info
  (=?=) z (Choice_C_Word cd i x y) cs = narrow cd i ((z Curry_Prelude.=?= x) cs) ((z Curry_Prelude.=?= y) cs)
  (=?=) y (Choices_C_Word cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.=?= x) cs) xs
  (=?=) y (Guard_C_Word cd c e) cs = guardCons cd c ((y Curry_Prelude.=?= e) (addCs c cs))
  (=?=) _ (Fail_C_Word cd info) _ = failCons cd info
  (=?=) (C_Word x1 x2) (C_Word y1 y2) cs = Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.=?= y2) cs) cs
  (<?=) (Choice_C_Word cd i x y) z cs = narrow cd i ((x Curry_Prelude.<?= z) cs) ((y Curry_Prelude.<?= z) cs)
  (<?=) (Choices_C_Word cd i xs) y cs = narrows cs cd i (\x -> (x Curry_Prelude.<?= y) cs) xs
  (<?=) (Guard_C_Word cd c e) y cs = guardCons cd c ((e Curry_Prelude.<?= y) (addCs c cs))
  (<?=) (Fail_C_Word cd info) _ _ = failCons cd info
  (<?=) z (Choice_C_Word cd i x y) cs = narrow cd i ((z Curry_Prelude.<?= x) cs) ((z Curry_Prelude.<?= y) cs)
  (<?=) y (Choices_C_Word cd i xs) cs = narrows cs cd i (\x -> (y Curry_Prelude.<?= x) cs) xs
  (<?=) y (Guard_C_Word cd c e) cs = guardCons cd c ((y Curry_Prelude.<?= e) (addCs c cs))
  (<?=) _ (Fail_C_Word cd info) _ = failCons cd info
  (<?=) (C_Word x1 x2) (C_Word y1 y2) cs = Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_lt x1 y1 cs) (Curry_Prelude.d_OP_ampersand_ampersand ((x1 Curry_Prelude.=?= y1) cs) ((x2 Curry_Prelude.<?= y2) cs) cs) cs


instance Coverable C_Word where
  cover (C_Word x1 x2) = C_Word (cover x1) (cover x2)
  cover (Choice_C_Word cd i x y) = Choice_C_Word (incCover cd) i (cover x) (cover y)
  cover (Choices_C_Word cd i xs) = Choices_C_Word (incCover cd) i (map cover xs)
  cover (Fail_C_Word cd info) = Fail_C_Word (incCover cd) info
  cover (Guard_C_Word cd c e) = Guard_C_Word (incCover cd) c (cover e)


d_C_posToString :: C_Pos -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_C_posToString x1 x3500 = d_OP__case_25 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Adjective x3500) x3500

d_C_posFromString :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> C_Pos
d_C_posFromString x1 x3500 = d_OP__case_18 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'j'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List))))))))) x3500) x3500

d_C_wordName :: C_Word -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_C_wordName x1 x3500 = case x1 of
     (C_Word x2 x3) -> x2
     (Choice_C_Word x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_wordName x1002 x3500) (d_C_wordName x1003 x3500)
     (Choices_C_Word x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_wordName z x3500) x1002
     (Guard_C_Word x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_wordName x1002) $! (addCs x1001 x3500))
     (Fail_C_Word x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_wordPos :: C_Word -> ConstStore -> Curry_Prelude.OP_List C_Pos
d_C_wordPos x1 x3500 = case x1 of
     (C_Word x2 x3) -> x3
     (Choice_C_Word x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_wordPos x1002 x3500) (d_C_wordPos x1003 x3500)
     (Choices_C_Word x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_wordPos z x3500) x1002
     (Guard_C_Word x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_wordPos x1002) $! (addCs x1001 x3500))
     (Fail_C_Word x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_isPos' :: C_Pos -> ConstStore -> C_Word -> ConstStore -> Curry_Prelude.C_Bool
d_C_isPos' x1 x3500 = Curry_Prelude.d_OP_dot (Curry_Prelude.d_C_elem x1 x3500) d_C_wordPos x3500

nd_C_isPos' :: C_Pos -> IDSupply -> ConstStore -> Func C_Word Curry_Prelude.C_Bool
nd_C_isPos' x1 x3000 x3500 = let
     x2002 = x3000
      in (seq x2002 (let
          x2001 = leftSupply x2002
          x2000 = rightSupply x2002
           in (seq x2001 (seq x2000 (Curry_Prelude.nd_OP_dot (Curry_Prelude.nd_C_elem x1 x2000 x3500) (wrapDX id d_C_wordPos) x2001 x3500)))))

d_C_addWord :: Curry_Prelude.OP_List C_Word -> C_Word -> ConstStore -> Curry_Prelude.OP_List C_Word
d_C_addWord x1 x2 x3500 = case x2 of
     (C_Word x3 x4) -> let
          x5 = Curry_BinarySort.d_C_split' (Curry_Prelude.d_OP_dot (Curry_Prelude.d_OP_eq_eq x3) d_C_wordName x3500) (Curry_Prelude.d_OP_dot (Curry_Prelude.d_OP_gt x3) d_C_wordName x3500) x1 x3500
          x6 = d_OP_addWord_dot___hash_selFP2_hash_as x5 x3500
          x7 = d_OP_addWord_dot___hash_selFP3_hash_mw x5 x3500
          x8 = d_OP_addWord_dot___hash_selFP4_hash_bs x5 x3500
           in (Curry_Prelude.d_OP_plus_plus x6 (Curry_Prelude.d_OP_plus_plus (Curry_Prelude.OP_Cons (d_OP__case_11 x3 x4 x7 x3500) Curry_Prelude.OP_List) x8 x3500) x3500)
     (Choice_C_Word x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_addWord x1 x1002 x3500) (d_C_addWord x1 x1003 x3500)
     (Choices_C_Word x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_addWord x1 z x3500) x1002
     (Guard_C_Word x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_addWord x1 x1002) $! (addCs x1001 x3500))
     (Fail_C_Word x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_addWord_dot___hash_selFP2_hash_as :: Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List C_Word) (Curry_Prelude.C_Maybe C_Word) (Curry_Prelude.OP_List C_Word) -> ConstStore -> Curry_Prelude.OP_List C_Word
d_OP_addWord_dot___hash_selFP2_hash_as x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple3 x2 x3 x4) -> x2
     (Curry_Prelude.Choice_OP_Tuple3 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_addWord_dot___hash_selFP2_hash_as x1002 x3500) (d_OP_addWord_dot___hash_selFP2_hash_as x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple3 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_addWord_dot___hash_selFP2_hash_as z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple3 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_addWord_dot___hash_selFP2_hash_as x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple3 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_addWord_dot___hash_selFP3_hash_mw :: Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List C_Word) (Curry_Prelude.C_Maybe C_Word) (Curry_Prelude.OP_List C_Word) -> ConstStore -> Curry_Prelude.C_Maybe C_Word
d_OP_addWord_dot___hash_selFP3_hash_mw x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple3 x2 x3 x4) -> x3
     (Curry_Prelude.Choice_OP_Tuple3 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_addWord_dot___hash_selFP3_hash_mw x1002 x3500) (d_OP_addWord_dot___hash_selFP3_hash_mw x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple3 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_addWord_dot___hash_selFP3_hash_mw z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple3 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_addWord_dot___hash_selFP3_hash_mw x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple3 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_addWord_dot___hash_selFP4_hash_bs :: Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List C_Word) (Curry_Prelude.C_Maybe C_Word) (Curry_Prelude.OP_List C_Word) -> ConstStore -> Curry_Prelude.OP_List C_Word
d_OP_addWord_dot___hash_selFP4_hash_bs x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple3 x2 x3 x4) -> x4
     (Curry_Prelude.Choice_OP_Tuple3 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_addWord_dot___hash_selFP4_hash_bs x1002 x3500) (d_OP_addWord_dot___hash_selFP4_hash_bs x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple3 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_addWord_dot___hash_selFP4_hash_bs z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple3 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_addWord_dot___hash_selFP4_hash_bs x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple3 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_addWords :: Curry_Prelude.OP_List C_Word -> Curry_Prelude.OP_List C_Word -> ConstStore -> Curry_Prelude.OP_List C_Word
d_C_addWords x1 x2 x3500 = case x1 of
     Curry_Prelude.OP_List -> x2
     (Curry_Prelude.OP_Cons x3 x4) -> Curry_Prelude.d_OP_dollar_hash_hash (d_C_addWords x4) (d_C_addWord x2 x3 x3500) x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_addWords x1002 x2 x3500) (d_C_addWords x1003 x2 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_addWords z x2 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_addWords x1002 x2) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_getWord :: Curry_Prelude.OP_List C_Word -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.C_Maybe C_Word
d_C_getWord x1 x2 x3500 = Curry_Prelude.d_C_apply (Curry_List.d_C_find (Curry_Prelude.d_OP_dot (Curry_Prelude.d_OP_eq_eq x2) d_C_wordName x3500) x3500) x1 x3500

d_C_isPos :: C_Pos -> Curry_Prelude.OP_List C_Word -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.C_Bool
d_C_isPos x1 x2 x3 x3500 = Curry_Prelude.d_OP_dollar (Curry_Maybe.d_C_fromMaybe Curry_Prelude.C_False) (Curry_Maybe.d_OP_gt_gt_minus (d_C_getWord x2 x3 x3500) (Curry_Prelude.d_OP_dot (acceptCs id Curry_Prelude.C_Just) (d_C_isPos' x1 x3500) x3500) x3500) x3500

d_C_isAdjective :: ConstStore -> Curry_Prelude.OP_List C_Word -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.C_Bool
d_C_isAdjective x3500 = acceptCs id (d_C_isPos C_Adjective)

nd_C_isAdjective :: IDSupply -> ConstStore -> Func (Curry_Prelude.OP_List C_Word) (Func (Curry_Prelude.OP_List Curry_Prelude.C_Char) Curry_Prelude.C_Bool)
nd_C_isAdjective x3000 x3500 = wrapDX (wrapDX id) (acceptCs id (d_C_isPos C_Adjective))

d_C_isAdverb :: ConstStore -> Curry_Prelude.OP_List C_Word -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.C_Bool
d_C_isAdverb x3500 = acceptCs id (d_C_isPos C_Adverb)

nd_C_isAdverb :: IDSupply -> ConstStore -> Func (Curry_Prelude.OP_List C_Word) (Func (Curry_Prelude.OP_List Curry_Prelude.C_Char) Curry_Prelude.C_Bool)
nd_C_isAdverb x3000 x3500 = wrapDX (wrapDX id) (acceptCs id (d_C_isPos C_Adverb))

d_C_isArticle :: ConstStore -> Curry_Prelude.OP_List C_Word -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.C_Bool
d_C_isArticle x3500 = acceptCs id (d_C_isPos C_Article)

nd_C_isArticle :: IDSupply -> ConstStore -> Func (Curry_Prelude.OP_List C_Word) (Func (Curry_Prelude.OP_List Curry_Prelude.C_Char) Curry_Prelude.C_Bool)
nd_C_isArticle x3000 x3500 = wrapDX (wrapDX id) (acceptCs id (d_C_isPos C_Article))

d_C_isPreposition :: ConstStore -> Curry_Prelude.OP_List C_Word -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.C_Bool
d_C_isPreposition x3500 = acceptCs id (d_C_isPos C_Preposition)

nd_C_isPreposition :: IDSupply -> ConstStore -> Func (Curry_Prelude.OP_List C_Word) (Func (Curry_Prelude.OP_List Curry_Prelude.C_Char) Curry_Prelude.C_Bool)
nd_C_isPreposition x3000 x3500 = wrapDX (wrapDX id) (acceptCs id (d_C_isPos C_Preposition))

d_C_isPronoun :: ConstStore -> Curry_Prelude.OP_List C_Word -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.C_Bool
d_C_isPronoun x3500 = acceptCs id (d_C_isPos C_Pronoun)

nd_C_isPronoun :: IDSupply -> ConstStore -> Func (Curry_Prelude.OP_List C_Word) (Func (Curry_Prelude.OP_List Curry_Prelude.C_Char) Curry_Prelude.C_Bool)
nd_C_isPronoun x3000 x3500 = wrapDX (wrapDX id) (acceptCs id (d_C_isPos C_Pronoun))

d_C_removeSuffix :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_C_removeSuffix x1 x2 x3500 = Curry_Prelude.d_OP_dollar (Curry_Prelude.d_C_reverse x3500) (Curry_Prelude.d_OP_dollar (d_OP_removeSuffix_dot_f_dot_41 (Curry_Prelude.d_C_apply (Curry_Prelude.d_C_reverse x3500) x1 x3500)) (Curry_Prelude.d_C_apply (Curry_Prelude.d_C_reverse x3500) x2 x3500) x3500) x3500

d_OP_removeSuffix_dot_f_dot_41 :: Curry_Prelude.Curry t0 => Curry_Prelude.OP_List t0 -> Curry_Prelude.OP_List t0 -> ConstStore -> Curry_Prelude.OP_List t0
d_OP_removeSuffix_dot_f_dot_41 x1 x2 x3500 = d_OP__case_9 x1 x2 (Curry_List.d_C_isPrefixOf x1 x2 x3500) x3500

d_C_isNoun :: Curry_Prelude.OP_List C_Word -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.C_Bool
d_C_isNoun x1 x2 x3500 = Curry_Prelude.d_OP_bar_bar (d_C_isPos C_Noun x1 x2 x3500) (Curry_Prelude.d_OP_bar_bar (d_C_isPos C_Noun x1 (d_C_removeSuffix (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) Curry_Prelude.OP_List) x2 x3500) x3500) (d_C_isPos C_Noun x1 (d_C_removeSuffix (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) Curry_Prelude.OP_List)) x2 x3500) x3500) x3500) x3500

d_C_isVerb :: Curry_Prelude.OP_List C_Word -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.C_Bool
d_C_isVerb x1 x2 x3500 = Curry_Prelude.d_OP_bar_bar (d_C_isPos C_Verb x1 x2 x3500) (Curry_Prelude.d_OP_bar_bar (d_C_isPos C_Verb x1 (d_C_removeSuffix (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) Curry_Prelude.OP_List) x2 x3500) x3500) (d_C_isPos C_Verb x1 (d_C_removeSuffix (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)) x2 x3500) x3500) x3500) x3500

d_C_loadVocab :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.C_IO (Curry_Prelude.OP_List C_Word)
d_C_loadVocab x1 x3500 = Curry_Prelude.d_OP_gt_gt_eq (Curry_XML.d_C_readXmlFile x1 x3500) (Curry_Prelude.d_OP_dot Curry_Prelude.d_C_return (Curry_Prelude.d_OP_dot (Curry_Prelude.d_C_map d_OP_loadVocab_dot_f_dot_49) (Curry_XML2.d_C_getElemsByTagName (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) x3500) x3500) x3500) x3500

d_OP_loadVocab_dot_f_dot_49 :: Curry_XML.C_XmlExp -> ConstStore -> C_Word
d_OP_loadVocab_dot_f_dot_49 x1 x3500 = case x1 of
     (Curry_XML.C_XElem x2 x3 x4) -> d_OP__case_8 x3 x2 x3500
     (Curry_XML.Choice_C_XmlExp x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_loadVocab_dot_f_dot_49 x1002 x3500) (d_OP_loadVocab_dot_f_dot_49 x1003 x3500)
     (Curry_XML.Choices_C_XmlExp x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_loadVocab_dot_f_dot_49 z x3500) x1002
     (Curry_XML.Guard_C_XmlExp x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_loadVocab_dot_f_dot_49 x1002) $! (addCs x1001 x3500))
     (Curry_XML.Fail_C_XmlExp x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_vocabToXML :: ConstStore -> Curry_Prelude.OP_List C_Word -> ConstStore -> Curry_XML.C_XmlExp
d_C_vocabToXML x3500 = Curry_Prelude.d_OP_dot (acceptCs id (Curry_XML.C_XElem (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List))))) Curry_Prelude.OP_List)) (Curry_Prelude.d_C_map d_OP_vocabToXML_dot_f_dot_54) x3500

nd_C_vocabToXML :: IDSupply -> ConstStore -> Func (Curry_Prelude.OP_List C_Word) Curry_XML.C_XmlExp
nd_C_vocabToXML x3000 x3500 = let
     x2000 = x3000
      in (seq x2000 (Curry_Prelude.nd_OP_dot (wrapDX id (acceptCs id (Curry_XML.C_XElem (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List))))) Curry_Prelude.OP_List))) (wrapNX id (Curry_Prelude.nd_C_map (wrapDX id d_OP_vocabToXML_dot_f_dot_54))) x2000 x3500))

d_OP_vocabToXML_dot_f_dot_54 :: C_Word -> ConstStore -> Curry_XML.C_XmlExp
d_OP_vocabToXML_dot_f_dot_54 x1 x3500 = case x1 of
     (C_Word x2 x3) -> Curry_XML.C_XElem (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'm'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List)))) x2) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) Curry_Prelude.OP_List))) (Curry_Prelude.d_OP_dollar Curry_Prelude.d_C_unwords (Curry_Prelude.d_C_map d_C_posToString x3 x3500) x3500)) Curry_Prelude.OP_List)) Curry_Prelude.OP_List
     (Choice_C_Word x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_vocabToXML_dot_f_dot_54 x1002 x3500) (d_OP_vocabToXML_dot_f_dot_54 x1003 x3500)
     (Choices_C_Word x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_vocabToXML_dot_f_dot_54 z x3500) x1002
     (Guard_C_Word x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_vocabToXML_dot_f_dot_54 x1002) $! (addCs x1001 x3500))
     (Fail_C_Word x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_writeVocab :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.OP_List C_Word -> ConstStore -> Curry_Prelude.C_IO Curry_Prelude.OP_Unit
d_C_writeVocab x1 x3500 = Curry_Prelude.d_OP_dot (Curry_XML.d_C_writeXmlFile x1) (d_C_vocabToXML x3500) x3500

nd_C_writeVocab :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> IDSupply -> ConstStore -> Func (Curry_Prelude.OP_List C_Word) (Curry_Prelude.C_IO Curry_Prelude.OP_Unit)
nd_C_writeVocab x1 x3000 x3500 = let
     x2002 = x3000
      in (seq x2002 (let
          x2001 = leftSupply x2002
          x2000 = rightSupply x2002
           in (seq x2001 (seq x2000 (Curry_Prelude.nd_OP_dot (wrapDX id (Curry_XML.d_C_writeXmlFile x1)) (nd_C_vocabToXML x2000 x3500) x2001 x3500)))))

d_OP__case_8 x3 x2 x3500 = case x2 of
     (Curry_Prelude.OP_Cons x5 x6) -> d_OP__case_7 x3 x6 x5 x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_8 x3 x1002 x3500) (d_OP__case_8 x3 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_8 x3 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_8 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_8 x3 x2 x3000 x3500 = case x2 of
     (Curry_Prelude.OP_Cons x5 x6) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_7 x3 x6 x5 x2000 x3500))
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_8 x3 x1002 x3000 x3500) (nd_OP__case_8 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_8 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_8 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_7 x3 x6 x5 x3500 = case x5 of
     (Curry_Prelude.C_Char 'w'#) -> d_OP__case_6 x3 x6 x3500
     (Curry_Prelude.CurryChar x5000) -> matchChar [('w',d_OP__case_6 x3 x6 x3500)] x5000 x3500
     (Curry_Prelude.Choice_C_Char x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_7 x3 x6 x1002 x3500) (d_OP__case_7 x3 x6 x1003 x3500)
     (Curry_Prelude.Choices_C_Char x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_7 x3 x6 z x3500) x1002
     (Curry_Prelude.Guard_C_Char x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_7 x3 x6 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Char x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_7 x3 x6 x5 x3000 x3500 = case x5 of
     (Curry_Prelude.C_Char 'w'#) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_6 x3 x6 x2000 x3500))
     (Curry_Prelude.CurryChar x5000) -> matchChar [('w',let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_6 x3 x6 x2000 x3500)))] x5000 x3500
     (Curry_Prelude.Choice_C_Char x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_7 x3 x6 x1002 x3000 x3500) (nd_OP__case_7 x3 x6 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Char x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_7 x3 x6 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Char x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_7 x3 x6 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Char x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_6 x3 x6 x3500 = case x6 of
     (Curry_Prelude.OP_Cons x7 x8) -> d_OP__case_5 x3 x8 x7 x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_6 x3 x1002 x3500) (d_OP__case_6 x3 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_6 x3 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_6 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_6 x3 x6 x3000 x3500 = case x6 of
     (Curry_Prelude.OP_Cons x7 x8) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_5 x3 x8 x7 x2000 x3500))
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_6 x3 x1002 x3000 x3500) (nd_OP__case_6 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_6 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_6 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_5 x3 x8 x7 x3500 = case x7 of
     (Curry_Prelude.C_Char 'o'#) -> d_OP__case_4 x3 x8 x3500
     (Curry_Prelude.CurryChar x5000) -> matchChar [('o',d_OP__case_4 x3 x8 x3500)] x5000 x3500
     (Curry_Prelude.Choice_C_Char x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_5 x3 x8 x1002 x3500) (d_OP__case_5 x3 x8 x1003 x3500)
     (Curry_Prelude.Choices_C_Char x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_5 x3 x8 z x3500) x1002
     (Curry_Prelude.Guard_C_Char x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_5 x3 x8 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Char x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_5 x3 x8 x7 x3000 x3500 = case x7 of
     (Curry_Prelude.C_Char 'o'#) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_4 x3 x8 x2000 x3500))
     (Curry_Prelude.CurryChar x5000) -> matchChar [('o',let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_4 x3 x8 x2000 x3500)))] x5000 x3500
     (Curry_Prelude.Choice_C_Char x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_5 x3 x8 x1002 x3000 x3500) (nd_OP__case_5 x3 x8 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Char x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_5 x3 x8 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Char x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_5 x3 x8 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Char x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_4 x3 x8 x3500 = case x8 of
     (Curry_Prelude.OP_Cons x9 x10) -> d_OP__case_3 x3 x10 x9 x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_4 x3 x1002 x3500) (d_OP__case_4 x3 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_4 x3 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_4 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_4 x3 x8 x3000 x3500 = case x8 of
     (Curry_Prelude.OP_Cons x9 x10) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_3 x3 x10 x9 x2000 x3500))
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_4 x3 x1002 x3000 x3500) (nd_OP__case_4 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_4 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_4 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_3 x3 x10 x9 x3500 = case x9 of
     (Curry_Prelude.C_Char 'r'#) -> d_OP__case_2 x3 x10 x3500
     (Curry_Prelude.CurryChar x5000) -> matchChar [('r',d_OP__case_2 x3 x10 x3500)] x5000 x3500
     (Curry_Prelude.Choice_C_Char x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_3 x3 x10 x1002 x3500) (d_OP__case_3 x3 x10 x1003 x3500)
     (Curry_Prelude.Choices_C_Char x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_3 x3 x10 z x3500) x1002
     (Curry_Prelude.Guard_C_Char x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_3 x3 x10 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Char x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_3 x3 x10 x9 x3000 x3500 = case x9 of
     (Curry_Prelude.C_Char 'r'#) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_2 x3 x10 x2000 x3500))
     (Curry_Prelude.CurryChar x5000) -> matchChar [('r',let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_2 x3 x10 x2000 x3500)))] x5000 x3500
     (Curry_Prelude.Choice_C_Char x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_3 x3 x10 x1002 x3000 x3500) (nd_OP__case_3 x3 x10 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Char x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_3 x3 x10 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Char x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_3 x3 x10 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Char x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_2 x3 x10 x3500 = case x10 of
     (Curry_Prelude.OP_Cons x11 x12) -> d_OP__case_1 x3 x12 x11 x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_2 x3 x1002 x3500) (d_OP__case_2 x3 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_2 x3 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_2 x3 x10 x3000 x3500 = case x10 of
     (Curry_Prelude.OP_Cons x11 x12) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_1 x3 x12 x11 x2000 x3500))
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_2 x3 x1002 x3000 x3500) (nd_OP__case_2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_1 x3 x12 x11 x3500 = case x11 of
     (Curry_Prelude.C_Char 'd'#) -> d_OP__case_0 x3 x12 x3500
     (Curry_Prelude.CurryChar x5000) -> matchChar [('d',d_OP__case_0 x3 x12 x3500)] x5000 x3500
     (Curry_Prelude.Choice_C_Char x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_1 x3 x12 x1002 x3500) (d_OP__case_1 x3 x12 x1003 x3500)
     (Curry_Prelude.Choices_C_Char x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_1 x3 x12 z x3500) x1002
     (Curry_Prelude.Guard_C_Char x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_1 x3 x12 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Char x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_1 x3 x12 x11 x3000 x3500 = case x11 of
     (Curry_Prelude.C_Char 'd'#) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_0 x3 x12 x2000 x3500))
     (Curry_Prelude.CurryChar x5000) -> matchChar [('d',let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_0 x3 x12 x2000 x3500)))] x5000 x3500
     (Curry_Prelude.Choice_C_Char x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_1 x3 x12 x1002 x3000 x3500) (nd_OP__case_1 x3 x12 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Char x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_1 x3 x12 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Char x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_1 x3 x12 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Char x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_0 x3 x12 x3500 = case x12 of
     Curry_Prelude.OP_List -> Curry_Prelude.d_OP_dollar (acceptCs id (C_Word (Curry_Prelude.d_OP_dollar Curry_Maybe.d_C_fromJust (Curry_Prelude.d_C_lookup (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'm'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List)))) x3 x3500) x3500))) (Curry_Prelude.d_OP_dollar (Curry_Prelude.d_C_map d_C_posFromString) (Curry_Prelude.d_OP_dollar Curry_Prelude.d_C_words (Curry_Prelude.d_OP_dollar Curry_Maybe.d_C_fromJust (Curry_Prelude.d_C_lookup (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) Curry_Prelude.OP_List))) x3 x3500) x3500) x3500) x3500) x3500
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_0 x3 x1002 x3500) (d_OP__case_0 x3 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_0 x3 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_0 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_0 x3 x12 x3000 x3500 = case x12 of
     Curry_Prelude.OP_List -> let
          x2007 = x3000
           in (seq x2007 (let
               x2006 = leftSupply x2007
               x2008 = rightSupply x2007
                in (seq x2006 (seq x2008 (let
                    x2000 = leftSupply x2008
                    x2005 = rightSupply x2008
                     in (seq x2000 (seq x2005 (Curry_Prelude.nd_OP_dollar (wrapDX id (acceptCs id (C_Word (Curry_Prelude.nd_OP_dollar (wrapDX id Curry_Maybe.d_C_fromJust) (Curry_Prelude.d_C_lookup (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'm'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List)))) x3 x3500) x2000 x3500)))) (let
                         x2004 = leftSupply x2005
                         x2003 = rightSupply x2005
                          in (seq x2004 (seq x2003 (Curry_Prelude.nd_OP_dollar (wrapNX id (Curry_Prelude.nd_C_map (wrapDX id d_C_posFromString))) (let
                              x2002 = leftSupply x2003
                              x2001 = rightSupply x2003
                               in (seq x2002 (seq x2001 (Curry_Prelude.nd_OP_dollar (wrapDX id Curry_Prelude.d_C_words) (Curry_Prelude.nd_OP_dollar (wrapDX id Curry_Maybe.d_C_fromJust) (Curry_Prelude.d_C_lookup (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) Curry_Prelude.OP_List))) x3 x3500) x2001 x3500) x2002 x3500)))) x2004 x3500)))) x2006 x3500))))))))
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_0 x3 x1002 x3000 x3500) (nd_OP__case_0 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_0 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_0 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_9 x1 x2 x3 x3500 = case x3 of
     Curry_Prelude.C_True -> Curry_Prelude.d_C_drop (Curry_Prelude.d_C_length x1 x3500) x2 x3500
     Curry_Prelude.C_False -> x2
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_9 x1 x2 x1002 x3500) (d_OP__case_9 x1 x2 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_9 x1 x2 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_9 x1 x2 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_9 x1 x2 x3 x3000 x3500 = case x3 of
     Curry_Prelude.C_True -> Curry_Prelude.d_C_drop (Curry_Prelude.d_C_length x1 x3500) x2 x3500
     Curry_Prelude.C_False -> x2
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_9 x1 x2 x1002 x3000 x3500) (nd_OP__case_9 x1 x2 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_9 x1 x2 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_9 x1 x2 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_11 x3 x4 x7 x3500 = case x7 of
     (Curry_Prelude.C_Just x9) -> d_OP__case_10 x3 x4 x9 x3500
     Curry_Prelude.C_Nothing -> C_Word x3 x4
     (Curry_Prelude.Choice_C_Maybe x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_11 x3 x4 x1002 x3500) (d_OP__case_11 x3 x4 x1003 x3500)
     (Curry_Prelude.Choices_C_Maybe x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_11 x3 x4 z x3500) x1002
     (Curry_Prelude.Guard_C_Maybe x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_11 x3 x4 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Maybe x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_11 x3 x4 x7 x3000 x3500 = case x7 of
     (Curry_Prelude.C_Just x9) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_10 x3 x4 x9 x2000 x3500))
     Curry_Prelude.C_Nothing -> C_Word x3 x4
     (Curry_Prelude.Choice_C_Maybe x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_11 x3 x4 x1002 x3000 x3500) (nd_OP__case_11 x3 x4 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Maybe x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_11 x3 x4 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Maybe x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_11 x3 x4 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Maybe x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_10 x3 x4 x9 x3500 = case x9 of
     (C_Word x10 x11) -> C_Word x3 (Curry_List.d_C_nub (Curry_Prelude.d_OP_plus_plus x4 x11 x3500) x3500)
     (Choice_C_Word x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_10 x3 x4 x1002 x3500) (d_OP__case_10 x3 x4 x1003 x3500)
     (Choices_C_Word x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_10 x3 x4 z x3500) x1002
     (Guard_C_Word x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_10 x3 x4 x1002) $! (addCs x1001 x3500))
     (Fail_C_Word x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_10 x3 x4 x9 x3000 x3500 = case x9 of
     (C_Word x10 x11) -> C_Word x3 (Curry_List.d_C_nub (Curry_Prelude.d_OP_plus_plus x4 x11 x3500) x3500)
     (Choice_C_Word x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_10 x3 x4 x1002 x3000 x3500) (nd_OP__case_10 x3 x4 x1003 x3000 x3500)
     (Choices_C_Word x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_10 x3 x4 z x3000 x3500) x1002
     (Guard_C_Word x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_10 x3 x4 x1002 x3000) $! (addCs x1001 x3500))
     (Fail_C_Word x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_18 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Adjective
     Curry_Prelude.C_False -> d_OP__case_17 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List)))))) x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_18 x1 x1002 x3500) (d_OP__case_18 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_18 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_18 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_18 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Adjective
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_17 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List)))))) x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_18 x1 x1002 x3000 x3500) (nd_OP__case_18 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_18 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_18 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_17 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Adverb
     Curry_Prelude.C_False -> d_OP__case_16 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'l'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List))))))) x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_17 x1 x1002 x3500) (d_OP__case_17 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_17 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_17 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_17 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Adverb
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_16 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'l'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List))))))) x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_17 x1 x1002 x3000 x3500) (nd_OP__case_17 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_17 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_17 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_16 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Article
     Curry_Prelude.C_False -> d_OP__case_15 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'u'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List)))) x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_16 x1 x1002 x3500) (d_OP__case_16 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_16 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_16 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_16 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Article
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_15 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'u'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List)))) x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_16 x1 x1002 x3000 x3500) (nd_OP__case_16 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_16 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_16 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_15 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Noun
     Curry_Prelude.C_False -> d_OP__case_14 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List))))))))))) x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_15 x1 x1002 x3500) (d_OP__case_15 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_15 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_15 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_15 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Noun
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_14 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List))))))))))) x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_15 x1 x1002 x3000 x3500) (nd_OP__case_15 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_15 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_15 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_14 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Preposition
     Curry_Prelude.C_False -> d_OP__case_13 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'u'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List))))))) x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_14 x1 x1002 x3500) (d_OP__case_14 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_14 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_14 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_14 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Preposition
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_13 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'u'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List))))))) x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_14 x1 x1002 x3000 x3500) (nd_OP__case_14 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_14 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_14 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_13 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Pronoun
     Curry_Prelude.C_False -> d_OP__case_12 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List)))) x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_13 x1 x1002 x3500) (d_OP__case_13 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_13 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_13 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_13 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Pronoun
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_12 x1 (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List)))) x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_13 x1 x1002 x3000 x3500) (nd_OP__case_13 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_13 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_13 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_12 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Verb
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_12 x1 x1002 x3500) (d_OP__case_12 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_12 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_12 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_12 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> C_Verb
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_12 x1 x1002 x3000 x3500) (nd_OP__case_12 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_12 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_12 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_25 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'j'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List))))))))
     Curry_Prelude.C_False -> d_OP__case_24 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Adverb x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_25 x1 x1002 x3500) (d_OP__case_25 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_25 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_25 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_25 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'j'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List))))))))
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_24 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Adverb x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_25 x1 x1002 x3000 x3500) (nd_OP__case_25 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_25 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_25 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_24 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List)))))
     Curry_Prelude.C_False -> d_OP__case_23 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Article x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_24 x1 x1002 x3500) (d_OP__case_24 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_24 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_24 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_24 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List)))))
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_23 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Article x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_24 x1 x1002 x3000 x3500) (nd_OP__case_24 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_24 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_24 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_23 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'l'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List))))))
     Curry_Prelude.C_False -> d_OP__case_22 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Noun x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_23 x1 x1002 x3500) (d_OP__case_23 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_23 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_23 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_23 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'l'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List))))))
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_22 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Noun x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_23 x1 x1002 x3000 x3500) (nd_OP__case_23 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_23 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_23 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_22 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'u'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List)))
     Curry_Prelude.C_False -> d_OP__case_21 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Preposition x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_22 x1 x1002 x3500) (d_OP__case_22 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_22 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_22 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_22 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'u'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List)))
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_21 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Preposition x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_22 x1 x1002 x3000 x3500) (nd_OP__case_22 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_22 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_22 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_21 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List))))))))))
     Curry_Prelude.C_False -> d_OP__case_20 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Pronoun x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_21 x1 x1002 x3500) (d_OP__case_21 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_21 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_21 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_21 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List))))))))))
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_20 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Pronoun x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_21 x1 x1002 x3000 x3500) (nd_OP__case_21 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_21 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_21 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_20 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'u'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List))))))
     Curry_Prelude.C_False -> d_OP__case_19 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Verb x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_20 x1 x1002 x3500) (d_OP__case_20 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_20 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_20 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_20 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'u'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List))))))
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_19 x1 (Curry_Prelude.d_OP_eq_eq x1 C_Verb x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_20 x1 x1002 x3000 x3500) (nd_OP__case_20 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_20 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_20 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_19 x1 x2 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List)))
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_19 x1 x1002 x3500) (d_OP__case_19 x1 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_19 x1 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_19 x1 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_19 x1 x2 x3000 x3500 = case x2 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List)))
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_19 x1 x1002 x3000 x3500) (nd_OP__case_19 x1 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_19 x1 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_19 x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo
