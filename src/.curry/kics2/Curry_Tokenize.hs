{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module Curry_Tokenize (nd_C_tokenize) where

import Basics
import qualified Curry_Parse
import qualified Curry_Prelude
import qualified Curry_Preprocess
import qualified Curry_Vocab
nd_C_tokenizeWord :: Curry_Prelude.OP_List Curry_Vocab.C_Word -> Curry_Prelude.C_Int -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> IDSupply -> ConstStore -> Curry_Parse.C_Token (Curry_Prelude.OP_List Curry_Prelude.C_Char)
nd_C_tokenizeWord x1 x2 x3 x3000 x3500 = let
     x2087 = x3000
      in (seq x2087 (let
          x2086 = leftSupply x2087
          x2088 = rightSupply x2087
           in (seq x2086 (seq x2088 (let
               x2053 = leftSupply x2088
               x2085 = rightSupply x2088
                in (seq x2053 (seq x2085 (Curry_Prelude.nd_OP_qmark (let
                    x2052 = leftSupply x2053
                    x2054 = rightSupply x2053
                     in (seq x2052 (seq x2054 (let
                         x2049 = leftSupply x2054
                         x2051 = rightSupply x2054
                          in (seq x2049 (seq x2051 (Curry_Prelude.nd_OP_qmark (let
                              x2048 = leftSupply x2049
                              x2050 = rightSupply x2049
                               in (seq x2048 (seq x2050 (let
                                   x2039 = leftSupply x2050
                                   x2047 = rightSupply x2050
                                    in (seq x2039 (seq x2047 (Curry_Prelude.nd_OP_qmark (let
                                        x2038 = leftSupply x2039
                                        x2040 = rightSupply x2039
                                         in (seq x2038 (seq x2040 (let
                                             x2029 = leftSupply x2040
                                             x2037 = rightSupply x2040
                                              in (seq x2029 (seq x2037 (Curry_Prelude.nd_OP_qmark (let
                                                  x2028 = leftSupply x2029
                                                  x2030 = rightSupply x2029
                                                   in (seq x2028 (seq x2030 (let
                                                       x2025 = leftSupply x2030
                                                       x2027 = rightSupply x2030
                                                        in (seq x2025 (seq x2027 (Curry_Prelude.nd_OP_qmark (let
                                                            x2024 = leftSupply x2025
                                                            x2026 = rightSupply x2025
                                                             in (seq x2024 (seq x2026 (let
                                                                 x2015 = leftSupply x2026
                                                                 x2023 = rightSupply x2026
                                                                  in (seq x2015 (seq x2023 (Curry_Prelude.nd_OP_qmark (let
                                                                      x2014 = leftSupply x2015
                                                                      x2016 = rightSupply x2015
                                                                       in (seq x2014 (seq x2016 (let
                                                                           x2006 = leftSupply x2016
                                                                           x2013 = rightSupply x2016
                                                                            in (seq x2006 (seq x2013 (Curry_Prelude.nd_OP_qmark (let
                                                                                x2005 = leftSupply x2006
                                                                                x2004 = rightSupply x2006
                                                                                 in (seq x2005 (seq x2004 (nd_OP__case_8 x1 x2 x3 (let
                                                                                     x2003 = leftSupply x2004
                                                                                     x2002 = rightSupply x2004
                                                                                      in (seq x2003 (seq x2002 (Curry_Prelude.nd_C_apply (let
                                                                                          x2001 = leftSupply x2002
                                                                                          x2000 = rightSupply x2002
                                                                                           in (seq x2001 (seq x2000 (Curry_Prelude.nd_C_apply (Curry_Vocab.nd_C_isAdjective x2000 x3500) x1 x2001 x3500)))) x3 x2003 x3500)))) x2005 x3500)))) (let
                                                                                x2012 = leftSupply x2013
                                                                                x2011 = rightSupply x2013
                                                                                 in (seq x2012 (seq x2011 (nd_OP__case_7 x1 x2 x3 (let
                                                                                     x2010 = leftSupply x2011
                                                                                     x2009 = rightSupply x2011
                                                                                      in (seq x2010 (seq x2009 (Curry_Prelude.nd_C_apply (let
                                                                                          x2008 = leftSupply x2009
                                                                                          x2007 = rightSupply x2009
                                                                                           in (seq x2008 (seq x2007 (Curry_Prelude.nd_C_apply (Curry_Vocab.nd_C_isAdverb x2007 x3500) x1 x2008 x3500)))) x3 x2010 x3500)))) x2012 x3500)))) x2014 x3500))))))) (let
                                                                      x2022 = leftSupply x2023
                                                                      x2021 = rightSupply x2023
                                                                       in (seq x2022 (seq x2021 (nd_OP__case_6 x1 x2 x3 (let
                                                                           x2020 = leftSupply x2021
                                                                           x2019 = rightSupply x2021
                                                                            in (seq x2020 (seq x2019 (Curry_Prelude.nd_C_apply (let
                                                                                x2018 = leftSupply x2019
                                                                                x2017 = rightSupply x2019
                                                                                 in (seq x2018 (seq x2017 (Curry_Prelude.nd_C_apply (Curry_Vocab.nd_C_isArticle x2017 x3500) x1 x2018 x3500)))) x3 x2020 x3500)))) x2022 x3500)))) x2024 x3500))))))) (nd_OP__case_5 x1 x2 x3 (Curry_Vocab.d_C_isNoun x1 x3 x3500) x2027 x3500) x2028 x3500))))))) (let
                                                  x2036 = leftSupply x2037
                                                  x2035 = rightSupply x2037
                                                   in (seq x2036 (seq x2035 (nd_OP__case_4 x1 x2 x3 (let
                                                       x2034 = leftSupply x2035
                                                       x2033 = rightSupply x2035
                                                        in (seq x2034 (seq x2033 (Curry_Prelude.nd_C_apply (let
                                                            x2032 = leftSupply x2033
                                                            x2031 = rightSupply x2033
                                                             in (seq x2032 (seq x2031 (Curry_Prelude.nd_C_apply (Curry_Vocab.nd_C_isPreposition x2031 x3500) x1 x2032 x3500)))) x3 x2034 x3500)))) x2036 x3500)))) x2038 x3500))))))) (let
                                        x2046 = leftSupply x2047
                                        x2045 = rightSupply x2047
                                         in (seq x2046 (seq x2045 (nd_OP__case_3 x1 x2 x3 (let
                                             x2044 = leftSupply x2045
                                             x2043 = rightSupply x2045
                                              in (seq x2044 (seq x2043 (Curry_Prelude.nd_C_apply (let
                                                  x2042 = leftSupply x2043
                                                  x2041 = rightSupply x2043
                                                   in (seq x2042 (seq x2041 (Curry_Prelude.nd_C_apply (Curry_Vocab.nd_C_isPronoun x2041 x3500) x1 x2042 x3500)))) x3 x2044 x3500)))) x2046 x3500)))) x2048 x3500))))))) (nd_OP__case_2 x1 x2 x3 (Curry_Vocab.d_C_isVerb x1 x3 x3500) x2051 x3500) x2052 x3500))))))) (let
                    x2084 = leftSupply x2085
                    x2083 = rightSupply x2085
                     in (seq x2084 (seq x2083 (nd_OP__case_1 x1 x2 x3 (let
                         x2059 = leftSupply x2083
                         x2082 = rightSupply x2083
                          in (seq x2059 (seq x2082 (Curry_Prelude.d_OP_ampersand_ampersand (Curry_Prelude.d_C_not (let
                              x2058 = leftSupply x2059
                              x2057 = rightSupply x2059
                               in (seq x2058 (seq x2057 (Curry_Prelude.nd_C_apply (let
                                   x2056 = leftSupply x2057
                                   x2055 = rightSupply x2057
                                    in (seq x2056 (seq x2055 (Curry_Prelude.nd_C_apply (Curry_Vocab.nd_C_isAdjective x2055 x3500) x1 x2056 x3500)))) x3 x2058 x3500)))) x3500) (let
                              x2064 = leftSupply x2082
                              x2081 = rightSupply x2082
                               in (seq x2064 (seq x2081 (Curry_Prelude.d_OP_ampersand_ampersand (Curry_Prelude.d_C_not (let
                                   x2063 = leftSupply x2064
                                   x2062 = rightSupply x2064
                                    in (seq x2063 (seq x2062 (Curry_Prelude.nd_C_apply (let
                                        x2061 = leftSupply x2062
                                        x2060 = rightSupply x2062
                                         in (seq x2061 (seq x2060 (Curry_Prelude.nd_C_apply (Curry_Vocab.nd_C_isAdverb x2060 x3500) x1 x2061 x3500)))) x3 x2063 x3500)))) x3500) (let
                                   x2069 = leftSupply x2081
                                   x2080 = rightSupply x2081
                                    in (seq x2069 (seq x2080 (Curry_Prelude.d_OP_ampersand_ampersand (Curry_Prelude.d_C_not (let
                                        x2068 = leftSupply x2069
                                        x2067 = rightSupply x2069
                                         in (seq x2068 (seq x2067 (Curry_Prelude.nd_C_apply (let
                                             x2066 = leftSupply x2067
                                             x2065 = rightSupply x2067
                                              in (seq x2066 (seq x2065 (Curry_Prelude.nd_C_apply (Curry_Vocab.nd_C_isArticle x2065 x3500) x1 x2066 x3500)))) x3 x2068 x3500)))) x3500) (let
                                        x2074 = leftSupply x2080
                                        x2079 = rightSupply x2080
                                         in (seq x2074 (seq x2079 (Curry_Prelude.d_OP_ampersand_ampersand (Curry_Prelude.d_C_not (let
                                             x2073 = leftSupply x2074
                                             x2072 = rightSupply x2074
                                              in (seq x2073 (seq x2072 (Curry_Prelude.nd_C_apply (let
                                                  x2071 = leftSupply x2072
                                                  x2070 = rightSupply x2072
                                                   in (seq x2071 (seq x2070 (Curry_Prelude.nd_C_apply (Curry_Vocab.nd_C_isPreposition x2070 x3500) x1 x2071 x3500)))) x3 x2073 x3500)))) x3500) (Curry_Prelude.d_OP_ampersand_ampersand (Curry_Prelude.d_C_not (let
                                             x2078 = leftSupply x2079
                                             x2077 = rightSupply x2079
                                              in (seq x2078 (seq x2077 (Curry_Prelude.nd_C_apply (let
                                                  x2076 = leftSupply x2077
                                                  x2075 = rightSupply x2077
                                                   in (seq x2076 (seq x2075 (Curry_Prelude.nd_C_apply (Curry_Vocab.nd_C_isPronoun x2075 x3500) x1 x2076 x3500)))) x3 x2078 x3500)))) x3500) (Curry_Prelude.d_OP_ampersand_ampersand (Curry_Prelude.d_C_not (Curry_Vocab.d_C_isNoun x1 x3 x3500) x3500) (Curry_Prelude.d_C_not (Curry_Vocab.d_C_isVerb x1 x3 x3500) x3500) x3500) x3500) x3500)))) x3500)))) x3500)))) x3500)))) x2084 x3500)))) x2086 x3500))))))))

nd_C_tokenize :: Curry_Prelude.OP_List Curry_Vocab.C_Word -> IDSupply -> ConstStore -> Func (Curry_Prelude.OP_List Curry_Prelude.C_Char) (Curry_Prelude.OP_List (Curry_Prelude.OP_List (Curry_Parse.C_Token (Curry_Prelude.OP_List Curry_Prelude.C_Char))))
nd_C_tokenize x1 x3000 x3500 = let
     x2006 = x3000
      in (seq x2006 (let
          x2005 = leftSupply x2006
          x2004 = rightSupply x2006
           in (seq x2005 (seq x2004 (Curry_Prelude.nd_OP_dot (wrapNX id (nd_OP_tokenize_dot_f_dot_18 x1 (Curry_Prelude.C_Int 0#))) (let
               x2003 = leftSupply x2004
               x2002 = rightSupply x2004
                in (seq x2003 (seq x2002 (Curry_Prelude.nd_OP_dot (wrapNX id (Curry_Prelude.nd_C_map (wrapDX id Curry_Prelude.d_C_words))) (let
                    x2001 = leftSupply x2002
                    x2000 = rightSupply x2002
                     in (seq x2001 (seq x2000 (Curry_Prelude.nd_OP_dot (wrapNX id (Curry_Prelude.nd_C_map (wrapDX id Curry_Preprocess.d_C_stripPunctuation))) (Curry_Prelude.nd_OP_dot (wrapDX id Curry_Preprocess.d_C_sentences) (wrapDX id Curry_Preprocess.d_C_decapitalize) x2000 x3500) x2001 x3500)))) x2003 x3500)))) x2005 x3500)))))

nd_OP_tokenize_dot_f_dot_18 :: Curry_Prelude.OP_List Curry_Vocab.C_Word -> Curry_Prelude.C_Int -> Curry_Prelude.OP_List (Curry_Prelude.OP_List (Curry_Prelude.OP_List Curry_Prelude.C_Char)) -> IDSupply -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_List (Curry_Parse.C_Token (Curry_Prelude.OP_List Curry_Prelude.C_Char)))
nd_OP_tokenize_dot_f_dot_18 x1 x2 x3 x3000 x3500 = case x3 of
     Curry_Prelude.OP_List -> Curry_Prelude.OP_List
     (Curry_Prelude.OP_Cons x4 x5) -> let
          x2000 = x3000
           in (seq x2000 (nd_OP__case_0 x1 x2 x5 x4 x2000 x3500))
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP_tokenize_dot_f_dot_18 x1 x2 x1002 x3000 x3500) (nd_OP_tokenize_dot_f_dot_18 x1 x2 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP_tokenize_dot_f_dot_18 x1 x2 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP_tokenize_dot_f_dot_18 x1 x2 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_tokenize_dot_f_dot_18_dot___hash_selFP2_hash_as :: Curry_Prelude.OP_List (Curry_Prelude.OP_List (Curry_Parse.C_Token (Curry_Prelude.OP_List Curry_Prelude.C_Char))) -> ConstStore -> Curry_Prelude.OP_List (Curry_Parse.C_Token (Curry_Prelude.OP_List Curry_Prelude.C_Char))
d_OP_tokenize_dot_f_dot_18_dot___hash_selFP2_hash_as x1 x3500 = case x1 of
     (Curry_Prelude.OP_Cons x2 x3) -> x2
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_tokenize_dot_f_dot_18_dot___hash_selFP2_hash_as x1002 x3500) (d_OP_tokenize_dot_f_dot_18_dot___hash_selFP2_hash_as x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_tokenize_dot_f_dot_18_dot___hash_selFP2_hash_as z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_tokenize_dot_f_dot_18_dot___hash_selFP2_hash_as x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP_tokenize_dot_f_dot_18_dot___hash_selFP3_hash_bss :: Curry_Prelude.OP_List (Curry_Prelude.OP_List (Curry_Parse.C_Token (Curry_Prelude.OP_List Curry_Prelude.C_Char))) -> ConstStore -> Curry_Prelude.OP_List (Curry_Prelude.OP_List (Curry_Parse.C_Token (Curry_Prelude.OP_List Curry_Prelude.C_Char)))
d_OP_tokenize_dot_f_dot_18_dot___hash_selFP3_hash_bss x1 x3500 = case x1 of
     (Curry_Prelude.OP_Cons x2 x3) -> x3
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP_tokenize_dot_f_dot_18_dot___hash_selFP3_hash_bss x1002 x3500) (d_OP_tokenize_dot_f_dot_18_dot___hash_selFP3_hash_bss x1003 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP_tokenize_dot_f_dot_18_dot___hash_selFP3_hash_bss z x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP_tokenize_dot_f_dot_18_dot___hash_selFP3_hash_bss x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_0 x1 x2 x5 x4 x3000 x3500 = case x4 of
     Curry_Prelude.OP_List -> let
          x2000 = x3000
           in (seq x2000 (Curry_Prelude.OP_Cons Curry_Prelude.OP_List (nd_OP_tokenize_dot_f_dot_18 x1 x2 x5 x2000 x3500)))
     (Curry_Prelude.OP_Cons x6 x7) -> let
          x2002 = x3000
           in (seq x2002 (let
               x2000 = leftSupply x2002
               x2001 = rightSupply x2002
                in (seq x2000 (seq x2001 (let
                    x8 = nd_OP_tokenize_dot_f_dot_18 x1 (Curry_Prelude.d_OP_plus x2 (Curry_Prelude.C_Int 1#) x3500) (Curry_Prelude.OP_Cons x7 x5) x2000 x3500
                    x9 = d_OP_tokenize_dot_f_dot_18_dot___hash_selFP2_hash_as x8 x3500
                    x10 = d_OP_tokenize_dot_f_dot_18_dot___hash_selFP3_hash_bss x8 x3500
                     in (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (nd_C_tokenizeWord x1 x2 x6 x2001 x3500) x9) x10))))))
     (Curry_Prelude.Choice_OP_List x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_0 x1 x2 x5 x1002 x3000 x3500) (nd_OP__case_0 x1 x2 x5 x1003 x3000 x3500)
     (Curry_Prelude.Choices_OP_List x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_0 x1 x2 x5 z x3000 x3500) x1002
     (Curry_Prelude.Guard_OP_List x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_0 x1 x2 x5 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_OP_List x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_1 x1 x2 x3 x4 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_1 x1 x2 x3 x1002 x3500) (d_OP__case_1 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_1 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_1 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_1 x1 x2 x3 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_1 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_1 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_1 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_1 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_2 x1 x2 x3 x4 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_2 x1 x2 x3 x1002 x3500) (d_OP__case_2 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_2 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_2 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_2 x1 x2 x3 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_2 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_2 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_2 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_2 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_3 x1 x2 x3 x4 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'u'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List))))))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_3 x1 x2 x3 x1002 x3500) (d_OP__case_3 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_3 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_3 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_3 x1 x2 x3 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'u'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List))))))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_3 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_3 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_3 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_3 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_4 x1 x2 x3 x4 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List))))))))))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_4 x1 x2 x3 x1002 x3500) (d_OP__case_4 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_4 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_4 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_4 x1 x2 x3 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 's'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List))))))))))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_4 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_4 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_4 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_4 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_5 x1 x2 x3 x4 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'u'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_5 x1 x2 x3 x1002 x3500) (d_OP__case_5 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_5 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_5 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_5 x1 x2 x3 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'u'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'n'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_5 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_5 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_5 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_5 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_6 x1 x2 x3 x4 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'l'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List))))))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_6 x1 x2 x3 x1002 x3500) (d_OP__case_6 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_6 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_6 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_6 x1 x2 x3 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'l'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List))))))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_6 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_6 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_6 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_6 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_7 x1 x2 x3 x4 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List)))))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_7 x1 x2 x3 x1002 x3500) (d_OP__case_7 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_7 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_7 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_7 x1 x2 x3 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'b'#) Curry_Prelude.OP_List)))))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_7 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_7 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_7 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_7 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_OP__case_8 x1 x2 x3 x4 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'j'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List))))))))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_8 x1 x2 x3 x1002 x3500) (d_OP__case_8 x1 x2 x3 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_8 x1 x2 x3 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_8 x1 x2 x3 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_8 x1 x2 x3 x4 x3000 x3500 = case x4 of
     Curry_Prelude.C_True -> Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'a'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'j'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'c'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 't'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'v'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) Curry_Prelude.OP_List))))))))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Nonterminal (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'w'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'o'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'd'#) Curry_Prelude.OP_List)))) (Curry_Prelude.OP_Cons (Curry_Prelude.OP_Cons (Curry_Parse.C_Terminal x3 x2) Curry_Prelude.OP_List) Curry_Prelude.OP_List)) Curry_Prelude.OP_List) Curry_Prelude.OP_List)
     Curry_Prelude.C_False -> Curry_Prelude.d_C_failed x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_8 x1 x2 x3 x1002 x3000 x3500) (nd_OP__case_8 x1 x2 x3 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_8 x1 x2 x3 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_8 x1 x2 x3 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo
