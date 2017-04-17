{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module Curry_BinarySort (d_C_pivot, d_C_split, d_C_split', nd_C_split', d_C_merge, nd_C_merge) where

import Basics
import qualified Curry_Prelude
d_C_pivot :: Curry_Prelude.Curry t0 => Curry_Prelude.OP_List t0 -> ConstStore -> Curry_Prelude.C_Int
d_C_pivot x1 x3500 = Curry_Prelude.d_C_div (Curry_Prelude.d_OP_minus (Curry_Prelude.d_C_length x1 x3500) (Curry_Prelude.C_Int 1#) x3500) (Curry_Prelude.C_Int 2#) x3500

d_C_split :: Curry_Prelude.Curry t0 => Curry_Prelude.OP_List t0 -> ConstStore -> Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List t0) t0 (Curry_Prelude.OP_List t0)
d_C_split x1 x3500 = let
     x2 = Curry_Prelude.d_C_splitAt (d_C_pivot x1 x3500) x1 x3500
     x3 = d_OP_split_dot___hash_selFP2_hash_as x2 x3500
     x4 = d_OP_split_dot___hash_selFP3_hash_x x2 x3500
     x5 = d_OP_split_dot___hash_selFP4_hash_bs x2 x3500
      in (Curry_Prelude.OP_Tuple3 x3 x4 x5)

d_OP_split_dot___hash_selFP2_hash_as :: Curry_Prelude.Curry t13 => Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List t13) (Curry_Prelude.OP_List t13) -> ConstStore -> Curry_Prelude.OP_List t13
d_OP_split_dot___hash_selFP2_hash_as x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple2 x2 x3) -> d_OP__case_10 x2 x3 x3500
     (Curry_Prelude.Choice_OP_Tuple2 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_split_dot___hash_selFP2_hash_as x1002 x3500) (d_OP_split_dot___hash_selFP2_hash_as x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple2 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_split_dot___hash_selFP2_hash_as z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple2 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_split_dot___hash_selFP2_hash_as x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple2 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_split_dot___hash_selFP3_hash_x :: Curry_Prelude.Curry t13 => Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List t13) (Curry_Prelude.OP_List t13) -> ConstStore -> t13
d_OP_split_dot___hash_selFP3_hash_x x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple2 x2 x3) -> d_OP__case_9 x3 x3500
     (Curry_Prelude.Choice_OP_Tuple2 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_split_dot___hash_selFP3_hash_x x1002 x3500) (d_OP_split_dot___hash_selFP3_hash_x x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple2 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_split_dot___hash_selFP3_hash_x z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple2 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_split_dot___hash_selFP3_hash_x x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple2 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_split_dot___hash_selFP4_hash_bs :: Curry_Prelude.Curry t13 => Curry_Prelude.OP_Tuple2 (Curry_Prelude.OP_List t13) (Curry_Prelude.OP_List t13) -> ConstStore -> Curry_Prelude.OP_List t13
d_OP_split_dot___hash_selFP4_hash_bs x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple2 x2 x3) -> d_OP__case_8 x3 x3500
     (Curry_Prelude.Choice_OP_Tuple2 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_split_dot___hash_selFP4_hash_bs x1002 x3500) (d_OP_split_dot___hash_selFP4_hash_bs x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple2 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_split_dot___hash_selFP4_hash_bs z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple2 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_split_dot___hash_selFP4_hash_bs x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple2 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_split' :: Curry_Prelude.Curry t0 => (t0 -> ConstStore -> Curry_Prelude.C_Bool) -> (t0 -> ConstStore -> Curry_Prelude.C_Bool) -> Curry_Prelude.OP_List t0 -> ConstStore -> Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List t0) (Curry_Prelude.C_Maybe t0) (Curry_Prelude.OP_List t0)
d_C_split' x1 x2 x3 x3500 = d_OP__case_7 x1 x2 x3 (Curry_Prelude.d_C_null x3 x3500) x3500

nd_C_split' :: Curry_Prelude.Curry t0 => Func t0 Curry_Prelude.C_Bool -> Func t0 Curry_Prelude.C_Bool -> Curry_Prelude.OP_List t0 -> IDSupply -> ConstStore -> Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List t0) (Curry_Prelude.C_Maybe t0) (Curry_Prelude.OP_List t0)
nd_C_split' x1 x2 x3 x3000 x3500 = let
     x2000 = x3000
      in (seq x2000 (nd_OP__case_7 x1 x2 x3 (Curry_Prelude.d_C_null x3 x3500) x2000 x3500))

d_OP_split'_dot___hash_selFP14_hash_as :: Curry_Prelude.Curry t19 => Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List t19) t19 (Curry_Prelude.OP_List t19) -> ConstStore -> Curry_Prelude.OP_List t19
d_OP_split'_dot___hash_selFP14_hash_as x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple3 x2 x3 x4) -> x2
     (Curry_Prelude.Choice_OP_Tuple3 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_split'_dot___hash_selFP14_hash_as x1002 x3500) (d_OP_split'_dot___hash_selFP14_hash_as x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple3 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_split'_dot___hash_selFP14_hash_as z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple3 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_split'_dot___hash_selFP14_hash_as x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple3 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_split'_dot___hash_selFP15_hash_x :: Curry_Prelude.Curry t19 => Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List t19) t19 (Curry_Prelude.OP_List t19) -> ConstStore -> t19
d_OP_split'_dot___hash_selFP15_hash_x x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple3 x2 x3 x4) -> x3
     (Curry_Prelude.Choice_OP_Tuple3 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_split'_dot___hash_selFP15_hash_x x1002 x3500) (d_OP_split'_dot___hash_selFP15_hash_x x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple3 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_split'_dot___hash_selFP15_hash_x z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple3 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_split'_dot___hash_selFP15_hash_x x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple3 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_split'_dot___hash_selFP16_hash_bs :: Curry_Prelude.Curry t19 => Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List t19) t19 (Curry_Prelude.OP_List t19) -> ConstStore -> Curry_Prelude.OP_List t19
d_OP_split'_dot___hash_selFP16_hash_bs x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple3 x2 x3 x4) -> x4
     (Curry_Prelude.Choice_OP_Tuple3 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_split'_dot___hash_selFP16_hash_bs x1002 x3500) (d_OP_split'_dot___hash_selFP16_hash_bs x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple3 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_split'_dot___hash_selFP16_hash_bs z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple3 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_split'_dot___hash_selFP16_hash_bs x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple3 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_split'_dot___hash_selFP7_hash_as' :: Curry_Prelude.Curry t19 => Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List t19) (Curry_Prelude.C_Maybe t19) (Curry_Prelude.OP_List t19) -> ConstStore -> Curry_Prelude.OP_List t19
d_OP_split'_dot___hash_selFP7_hash_as' x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple3 x2 x3 x4) -> x2
     (Curry_Prelude.Choice_OP_Tuple3 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_split'_dot___hash_selFP7_hash_as' x1002 x3500) (d_OP_split'_dot___hash_selFP7_hash_as' x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple3 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_split'_dot___hash_selFP7_hash_as' z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple3 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_split'_dot___hash_selFP7_hash_as' x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple3 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_split'_dot___hash_selFP8_hash_x' :: Curry_Prelude.Curry t19 => Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List t19) (Curry_Prelude.C_Maybe t19) (Curry_Prelude.OP_List t19) -> ConstStore -> Curry_Prelude.C_Maybe t19
d_OP_split'_dot___hash_selFP8_hash_x' x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple3 x2 x3 x4) -> x3
     (Curry_Prelude.Choice_OP_Tuple3 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_split'_dot___hash_selFP8_hash_x' x1002 x3500) (d_OP_split'_dot___hash_selFP8_hash_x' x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple3 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_split'_dot___hash_selFP8_hash_x' z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple3 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_split'_dot___hash_selFP8_hash_x' x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple3 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_split'_dot___hash_selFP9_hash_bs' :: Curry_Prelude.Curry t19 => Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List t19) (Curry_Prelude.C_Maybe t19) (Curry_Prelude.OP_List t19) -> ConstStore -> Curry_Prelude.OP_List t19
d_OP_split'_dot___hash_selFP9_hash_bs' x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple3 x2 x3 x4) -> x4
     (Curry_Prelude.Choice_OP_Tuple3 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_split'_dot___hash_selFP9_hash_bs' x1002 x3500) (d_OP_split'_dot___hash_selFP9_hash_bs' x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple3 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_split'_dot___hash_selFP9_hash_bs' z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple3 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_split'_dot___hash_selFP9_hash_bs' x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple3 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_split'_dot___hash_selFP11_hash_as' :: Curry_Prelude.Curry t19 => Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List t19) (Curry_Prelude.C_Maybe t19) (Curry_Prelude.OP_List t19) -> ConstStore -> Curry_Prelude.OP_List t19
d_OP_split'_dot___hash_selFP11_hash_as' x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple3 x2 x3 x4) -> x2
     (Curry_Prelude.Choice_OP_Tuple3 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_split'_dot___hash_selFP11_hash_as' x1002 x3500) (d_OP_split'_dot___hash_selFP11_hash_as' x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple3 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_split'_dot___hash_selFP11_hash_as' z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple3 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_split'_dot___hash_selFP11_hash_as' x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple3 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_split'_dot___hash_selFP12_hash_x' :: Curry_Prelude.Curry t19 => Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List t19) (Curry_Prelude.C_Maybe t19) (Curry_Prelude.OP_List t19) -> ConstStore -> Curry_Prelude.C_Maybe t19
d_OP_split'_dot___hash_selFP12_hash_x' x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple3 x2 x3 x4) -> x3
     (Curry_Prelude.Choice_OP_Tuple3 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_split'_dot___hash_selFP12_hash_x' x1002 x3500) (d_OP_split'_dot___hash_selFP12_hash_x' x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple3 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_split'_dot___hash_selFP12_hash_x' z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple3 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_split'_dot___hash_selFP12_hash_x' x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple3 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_split'_dot___hash_selFP13_hash_bs' :: Curry_Prelude.Curry t19 => Curry_Prelude.OP_Tuple3 (Curry_Prelude.OP_List t19) (Curry_Prelude.C_Maybe t19) (Curry_Prelude.OP_List t19) -> ConstStore -> Curry_Prelude.OP_List t19
d_OP_split'_dot___hash_selFP13_hash_bs' x1 x3500 = case x1 of
     (Curry_Prelude.OP_Tuple3 x2 x3 x4) -> x4
     (Curry_Prelude.Choice_OP_Tuple3 x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_split'_dot___hash_selFP13_hash_bs' x1002 x3500) (d_OP_split'_dot___hash_selFP13_hash_bs' x1003 x3500)
     (Curry_Prelude.Choices_OP_Tuple3 x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_split'_dot___hash_selFP13_hash_bs' z x3500) x1002
     (Curry_Prelude.Guard_OP_Tuple3 x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_split'_dot___hash_selFP13_hash_bs' x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_Tuple3 x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_merge :: Curry_Prelude.Curry t0 => (t0 -> ConstStore -> t0 -> ConstStore -> Curry_Prelude.C_Bool) -> Curry_Prelude.OP_List t0 -> Curry_Prelude.OP_List t0 -> ConstStore -> Curry_Prelude.OP_List t0
d_C_merge x1 x2 x3 x3500 = d_OP__case_3 x1 x2 x3 (Curry_Prelude.d_C_null x2 x3500) x3500

nd_C_merge :: Curry_Prelude.Curry t0 => Func t0 (Func t0 Curry_Prelude.C_Bool) -> Curry_Prelude.OP_List t0 -> Curry_Prelude.OP_List t0 -> IDSupply -> ConstStore -> Curry_Prelude.OP_List t0
nd_C_merge x1 x2 x3 x3000 x3500 = let
     x2000 = x3000
      in (seq x2000 (nd_OP__case_3 x1 x2 x3 (Curry_Prelude.d_C_null x2 x3500) x2000 x3500))

d_OP_merge_dot___hash_selFP21_hash_x :: Curry_Prelude.Curry t49 => Curry_Prelude.OP_List t49 -> ConstStore -> t49
d_OP_merge_dot___hash_selFP21_hash_x x1 x3500 = case x1 of
     (Curry_Prelude.OP_Cons x2 x3) -> x2
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_merge_dot___hash_selFP21_hash_x x1002 x3500) (d_OP_merge_dot___hash_selFP21_hash_x x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_merge_dot___hash_selFP21_hash_x z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_merge_dot___hash_selFP21_hash_x x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_merge_dot___hash_selFP22_hash_xs' :: Curry_Prelude.Curry t49 => Curry_Prelude.OP_List t49 -> ConstStore -> Curry_Prelude.OP_List t49
d_OP_merge_dot___hash_selFP22_hash_xs' x1 x3500 = case x1 of
     (Curry_Prelude.OP_Cons x2 x3) -> x3
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_merge_dot___hash_selFP22_hash_xs' x1002 x3500) (d_OP_merge_dot___hash_selFP22_hash_xs' x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_merge_dot___hash_selFP22_hash_xs' z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_merge_dot___hash_selFP22_hash_xs' x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_merge_dot___hash_selFP19_hash_y :: Curry_Prelude.Curry t49 => Curry_Prelude.OP_List t49 -> ConstStore -> t49
d_OP_merge_dot___hash_selFP19_hash_y x1 x3500 = case x1 of
     (Curry_Prelude.OP_Cons x2 x3) -> x2
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_merge_dot___hash_selFP19_hash_y x1002 x3500) (d_OP_merge_dot___hash_selFP19_hash_y x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_merge_dot___hash_selFP19_hash_y z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_merge_dot___hash_selFP19_hash_y x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_merge_dot___hash_selFP20_hash_ys' :: Curry_Prelude.Curry t49 => Curry_Prelude.OP_List t49 -> ConstStore -> Curry_Prelude.OP_List t49
d_OP_merge_dot___hash_selFP20_hash_ys' x1 x3500 = case x1 of
     (Curry_Prelude.OP_Cons x2 x3) -> x3
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_merge_dot___hash_selFP20_hash_ys' x1002 x3500) (d_OP_merge_dot___hash_selFP20_hash_ys' x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_merge_dot___hash_selFP20_hash_ys' z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_merge_dot___hash_selFP20_hash_ys' x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_3 x1 x2 x3 x4 x3500 = case x4 of
     Curry_Prelude.C_True -> x3
     Curry_Prelude.C_False -> d_OP__case_2 x1 x2 x3 (Curry_Prelude.d_C_null x3 x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_3 x1 x2 x3 x1002 x3500) (d_OP__case_3 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_3 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_3 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_3 x1 x2 x3 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_True -> x3
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_2 x1 x2 x3 (Curry_Prelude.d_C_null x3 x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_3 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_3 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_3 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_3 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_2 x1 x2 x3 x4 x3500 = case x4 of
     Curry_Prelude.C_True -> x2
     Curry_Prelude.C_False -> d_OP__case_1 x1 x2 x3 (Curry_Prelude.d_C_otherwise x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_2 x1 x2 x3 x1002 x3500) (d_OP__case_2 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_2 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_2 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_2 x1 x2 x3 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_True -> x2
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_1 x1 x2 x3 (Curry_Prelude.d_C_otherwise x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_2 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_2 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_2 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_2 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_1 x1 x2 x3 x8 x3500 = case x8 of
     Curry_Prelude.C_True -> let
          x4 = d_OP_merge_dot___hash_selFP21_hash_x x2 x3500
          x5 = d_OP_merge_dot___hash_selFP22_hash_xs' x2 x3500
          x6 = d_OP_merge_dot___hash_selFP19_hash_y x3 x3500
          x7 = d_OP_merge_dot___hash_selFP20_hash_ys' x3 x3500
           in (d_OP__case_0 x1 x2 x3 x4 x5 x6 x7 (Curry_Prelude.d_C_apply (Curry_Prelude.d_C_apply x1 x4 x3500) x6 x3500) x3500)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_1 x1 x2 x3 x1002 x3500) (d_OP__case_1 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_1 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_1 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_1 x1 x2 x3 x8 x3000 x3500 = case x8 of
     Curry_Prelude.C_True -> let
          x2004 = x3000
           in (seq x2004 (let
               x4 = d_OP_merge_dot___hash_selFP21_hash_x x2 x3500
               x5 = d_OP_merge_dot___hash_selFP22_hash_xs' x2 x3500
               x6 = d_OP_merge_dot___hash_selFP19_hash_y x3 x3500
               x7 = d_OP_merge_dot___hash_selFP20_hash_ys' x3 x3500
                in (let
                    x2003 = leftSupply x2004
                    x2002 = rightSupply x2004
                     in (seq x2003 (seq x2002 (nd_OP__case_0 x1 x2 x3 x4 x5 x6 x7 (let
                         x2001 = leftSupply x2002
                         x2000 = rightSupply x2002
                          in (seq x2001 (seq x2000 (Curry_Prelude.nd_C_apply (Curry_Prelude.nd_C_apply x1 x4 x2000 x3500) x6 x2001 x3500)))) x2003 x3500))))))
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_1 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_1 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_1 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_1 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_0 x1 x2 x3 x4 x5 x6 x7 x8 x3500 = case x8 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Cons x4 (d_C_merge x1 x5 x3 x3500)
     Curry_Prelude.C_False -> Curry_Prelude.OP_Cons x6 (d_C_merge x1 x2 x7 x3500)
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_0 x1 x2 x3 x4 x5 x6 x7 x1002 x3500) (d_OP__case_0 x1 x2 x3 x4 x5 x6 x7 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_0 x1 x2 x3 x4 x5 x6 x7 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_0 x1 x2 x3 x4 x5 x6 x7 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_0 x1 x2 x3 x4 x5 x6 x7 x8 x3000 x3500 = case x8 of
     Curry_Prelude.C_True -> let
          x2000 = x3000
           in (seq x2000 (Curry_Prelude.OP_Cons x4 (nd_C_merge x1 x5 x3 x2000 x3500)))
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (Curry_Prelude.OP_Cons x6 (nd_C_merge x1 x2 x7 x2000 x3500)))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_0 x1 x2 x3 x4 x5 x6 x7 x1002 x3000 x3500) (nd_OP__case_0 x1 x2 x3 x4 x5 x6 x7 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_0 x1 x2 x3 x4 x5 x6 x7 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_0 x1 x2 x3 x4 x5 x6 x7 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_7 x1 x2 x3 x4 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Tuple3 Curry_Prelude.OP_List Curry_Prelude.C_Nothing Curry_Prelude.OP_List
     Curry_Prelude.C_False -> d_OP__case_6 x1 x2 x3 (Curry_Prelude.d_C_otherwise x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_7 x1 x2 x3 x1002 x3500) (d_OP__case_7 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_7 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_7 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_7 x1 x2 x3 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Tuple3 Curry_Prelude.OP_List Curry_Prelude.C_Nothing Curry_Prelude.OP_List
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_6 x1 x2 x3 (Curry_Prelude.d_C_otherwise x3500) x2000 x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_7 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_7 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_7 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_7 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_6 x1 x2 x3 x8 x3500 = case x8 of
     Curry_Prelude.C_True -> let
          x4 = d_C_split x3 x3500
          x5 = d_OP_split'_dot___hash_selFP14_hash_as x4 x3500
          x6 = d_OP_split'_dot___hash_selFP15_hash_x x4 x3500
          x7 = d_OP_split'_dot___hash_selFP16_hash_bs x4 x3500
           in (d_OP__case_5 x1 x2 x5 x6 x7 (Curry_Prelude.d_C_apply x1 x6 x3500) x3500)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_6 x1 x2 x3 x1002 x3500) (d_OP__case_6 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_6 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_6 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_6 x1 x2 x3 x8 x3000 x3500 = case x8 of
     Curry_Prelude.C_True -> let
          x2002 = x3000
           in (seq x2002 (let
               x4 = d_C_split x3 x3500
               x5 = d_OP_split'_dot___hash_selFP14_hash_as x4 x3500
               x6 = d_OP_split'_dot___hash_selFP15_hash_x x4 x3500
               x7 = d_OP_split'_dot___hash_selFP16_hash_bs x4 x3500
                in (let
                    x2001 = leftSupply x2002
                    x2000 = rightSupply x2002
                     in (seq x2001 (seq x2000 (nd_OP__case_5 x1 x2 x5 x6 x7 (Curry_Prelude.nd_C_apply x1 x6 x2000 x3500) x2001 x3500))))))
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_6 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_6 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_6 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_6 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_5 x1 x2 x5 x6 x7 x8 x3500 = case x8 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Tuple3 x5 (Curry_Prelude.C_Just x6) x7
     Curry_Prelude.C_False -> d_OP__case_4 x1 x2 x5 x6 x7 (Curry_Prelude.d_C_apply x2 x6 x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_5 x1 x2 x5 x6 x7 x1002 x3500) (d_OP__case_5 x1 x2 x5 x6 x7 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_5 x1 x2 x5 x6 x7 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_5 x1 x2 x5 x6 x7 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_5 x1 x2 x5 x6 x7 x8 x3000 x3500 = case x8 of
     Curry_Prelude.C_True -> Curry_Prelude.OP_Tuple3 x5 (Curry_Prelude.C_Just x6) x7
     Curry_Prelude.C_False -> let
          x2002 = x3000
           in (seq x2002 (let
               x2001 = leftSupply x2002
               x2000 = rightSupply x2002
                in (seq x2001 (seq x2000 (nd_OP__case_4 x1 x2 x5 x6 x7 (Curry_Prelude.nd_C_apply x2 x6 x2000 x3500) x2001 x3500)))))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_5 x1 x2 x5 x6 x7 x1002 x3000 x3500) (nd_OP__case_5 x1 x2 x5 x6 x7 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_5 x1 x2 x5 x6 x7 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_5 x1 x2 x5 x6 x7 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_4 x1 x2 x5 x6 x7 x16 x3500 = case x16 of
     Curry_Prelude.C_True -> let
          x8 = d_C_split' x1 x2 x7 x3500
          x9 = d_OP_split'_dot___hash_selFP7_hash_as' x8 x3500
          x10 = d_OP_split'_dot___hash_selFP8_hash_x' x8 x3500
          x11 = d_OP_split'_dot___hash_selFP9_hash_bs' x8 x3500
           in (Curry_Prelude.OP_Tuple3 (Curry_Prelude.d_OP_plus_plus x5 (Curry_Prelude.OP_Cons x6 x9) x3500) x10 x11)
     Curry_Prelude.C_False -> let
          x12 = d_C_split' x1 x2 x5 x3500
          x13 = d_OP_split'_dot___hash_selFP11_hash_as' x12 x3500
          x14 = d_OP_split'_dot___hash_selFP12_hash_x' x12 x3500
          x15 = d_OP_split'_dot___hash_selFP13_hash_bs' x12 x3500
           in (Curry_Prelude.OP_Tuple3 x13 x14 (Curry_Prelude.d_OP_plus_plus x15 (Curry_Prelude.OP_Cons x6 x7) x3500))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_4 x1 x2 x5 x6 x7 x1002 x3500) (d_OP__case_4 x1 x2 x5 x6 x7 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_4 x1 x2 x5 x6 x7 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_4 x1 x2 x5 x6 x7 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_4 x1 x2 x5 x6 x7 x16 x3000 x3500 = case x16 of
     Curry_Prelude.C_True -> let
          x2000 = x3000
           in (seq x2000 (let
               x8 = nd_C_split' x1 x2 x7 x2000 x3500
               x9 = d_OP_split'_dot___hash_selFP7_hash_as' x8 x3500
               x10 = d_OP_split'_dot___hash_selFP8_hash_x' x8 x3500
               x11 = d_OP_split'_dot___hash_selFP9_hash_bs' x8 x3500
                in (Curry_Prelude.OP_Tuple3 (Curry_Prelude.d_OP_plus_plus x5 (Curry_Prelude.OP_Cons x6 x9) x3500) x10 x11)))
     Curry_Prelude.C_False -> let
          x2000 = x3000
           in (seq x2000 (let
               x12 = nd_C_split' x1 x2 x5 x2000 x3500
               x13 = d_OP_split'_dot___hash_selFP11_hash_as' x12 x3500
               x14 = d_OP_split'_dot___hash_selFP12_hash_x' x12 x3500
               x15 = d_OP_split'_dot___hash_selFP13_hash_bs' x12 x3500
                in (Curry_Prelude.OP_Tuple3 x13 x14 (Curry_Prelude.d_OP_plus_plus x15 (Curry_Prelude.OP_Cons x6 x7) x3500))))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_4 x1 x2 x5 x6 x7 x1002 x3000 x3500) (nd_OP__case_4 x1 x2 x5 x6 x7 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_4 x1 x2 x5 x6 x7 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_4 x1 x2 x5 x6 x7 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_8 x3 x3500 = case x3 of
     (Curry_Prelude.OP_Cons x4 x5) -> x5
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_8 x1002 x3500) (d_OP__case_8 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_8 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_8 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_8 x3 x3000 x3500 = case x3 of
     (Curry_Prelude.OP_Cons x4 x5) -> x5
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_8 x1002 x3000 x3500) (nd_OP__case_8 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_8 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_8 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_9 x3 x3500 = case x3 of
     (Curry_Prelude.OP_Cons x4 x5) -> x4
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_9 x1002 x3500) (d_OP__case_9 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_9 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_9 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_9 x3 x3000 x3500 = case x3 of
     (Curry_Prelude.OP_Cons x4 x5) -> x4
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_9 x1002 x3000 x3500) (nd_OP__case_9 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_9 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_9 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_10 x2 x3 x3500 = case x3 of
     (Curry_Prelude.OP_Cons x4 x5) -> x2
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_10 x2 x1002 x3500) (d_OP__case_10 x2 x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_10 x2 z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_10 x2 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_10 x2 x3 x3000 x3500 = case x3 of
     (Curry_Prelude.OP_Cons x4 x5) -> x2
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_10 x2 x1002 x3000 x3500) (nd_OP__case_10 x2 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_10 x2 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_10 x2 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo
