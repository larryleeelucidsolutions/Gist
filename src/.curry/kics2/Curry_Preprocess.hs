{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module Curry_Preprocess (d_C_isTerminalPunctuation, d_C_sentences, d_C_stripPunctuation, d_C_decapitalize) where

import Basics
import qualified Curry_Char
import qualified Curry_Prelude
d_C_isTerminalPunctuation :: Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.C_Bool
d_C_isTerminalPunctuation x1 x3500 = Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.C_Char '.'#) x3500) (Curry_Prelude.d_OP_bar_bar (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.C_Char '!'#) x3500) (Curry_Prelude.d_OP_eq_eq x1 (Curry_Prelude.C_Char '?'#) x3500) x3500) x3500

d_C_sentences :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_List Curry_Prelude.C_Char)
d_C_sentences x1 x3500 = case x1 of
     Curry_Prelude.OP_List -> Curry_Prelude.OP_List
     (Curry_Prelude.OP_Cons x2 x3) -> let
          x4 = d_C_sentences x3 x3500
           in (d_OP__case_0 x2 x4 (Curry_Prelude.d_OP_bar_bar (d_C_isTerminalPunctuation x2 x3500) (Curry_Prelude.d_C_null x4 x3500) x3500) x3500)
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_sentences x1002 x3500) (d_C_sentences x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_sentences z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_sentences x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_stripPunctuation :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_C_stripPunctuation x1 x3500 = Curry_Prelude.d_C_filter d_OP_stripPunctuation_dot___hash_lambda1 x1 x3500

d_OP_stripPunctuation_dot___hash_lambda1 :: Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.C_Bool
d_OP_stripPunctuation_dot___hash_lambda1 x1 x3500 = Curry_Prelude.d_OP_bar_bar (Curry_Char.d_C_isAlpha x1 x3500) (Curry_Char.d_C_isSpace x1 x3500) x3500

d_C_decapitalize :: Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_C_decapitalize x1 x3500 = Curry_Prelude.d_C_map Curry_Char.d_C_toLower x1 x3500

d_OP__case_0 x2 x4 x5 x3500 = case x5 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons x2 Curry_Prelude.OP_List) x4
     Curry_Prelude.C_False -> Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons x2 (Curry_Prelude.d_C_head x4 x3500)) (Curry_Prelude.d_C_tail x4 x3500)
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_0 x2 x4 x1002 x3500) (d_OP__case_0 x2 x4 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_0 x2 x4 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_0 x2 x4 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_0 x2 x4 x5 x3000 x3500 = case x5 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons x2 Curry_Prelude.OP_List) x4
     Curry_Prelude.C_False -> Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons x2 (Curry_Prelude.d_C_head x4 x3500)) (Curry_Prelude.d_C_tail x4 x3500)
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_0 x2 x4 x1002 x3000 x3500) (nd_OP__case_0 x2 x4 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_0 x2 x4 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_0 x2 x4 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo
