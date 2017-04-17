{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module Curry_RDFTurtle (d_C_URIToDoc, nd_C_URIToDoc, d_C_RDFNodeToDoc, nd_C_RDFNodeToDoc, d_C_RDFPredicateToDoc, nd_C_RDFPredicateToDoc, d_C_RDFTripleToDoc, nd_C_RDFTripleToDoc, d_C_RDFPrefixToDoc, nd_C_RDFPrefixToDoc, d_C_RDFGraphToDoc, nd_C_RDFGraphToDoc, d_C_RDFGraphToString, nd_C_RDFGraphToString) where

import Basics
import qualified Curry_Maybe
import qualified Curry_Prelude
import qualified Curry_Pretty
import qualified Curry_RDF
d_C_URIToDoc :: Curry_Prelude.OP_List Curry_RDF.C_RDFPrefix -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> ConstStore -> Curry_Pretty.C_Doc
d_C_URIToDoc x1 x2 x3500 = d_OP__case_0 x1 x2 (Curry_Prelude.d_OP_dollar Curry_Maybe.d_C_isJust (Curry_Prelude.d_C_apply (Curry_RDF.d_C_getRDFPrefixByURI x2 x3500) x1 x3500) x3500) x3500

nd_C_URIToDoc :: Curry_Prelude.OP_List Curry_RDF.C_RDFPrefix -> Curry_Prelude.OP_List Curry_Prelude.C_Char -> IDSupply -> ConstStore -> Curry_Pretty.C_Doc
nd_C_URIToDoc x1 x2 x3000 x3500 = let
     x2006 = x3000
      in (seq x2006 (let
          x2005 = leftSupply x2006
          x2004 = rightSupply x2006
           in (seq x2005 (seq x2004 (nd_OP__case_0 x1 x2 (let
               x2003 = leftSupply x2004
               x2002 = rightSupply x2004
                in (seq x2003 (seq x2002 (Curry_Prelude.nd_OP_dollar (wrapDX id Curry_Maybe.d_C_isJust) (let
                    x2001 = leftSupply x2002
                    x2000 = rightSupply x2002
                     in (seq x2001 (seq x2000 (Curry_Prelude.nd_C_apply (Curry_RDF.nd_C_getRDFPrefixByURI x2 x2000 x3500) x1 x2001 x3500)))) x2003 x3500)))) x2005 x3500)))))

d_C_RDFNodeToDoc :: Curry_Prelude.OP_List Curry_RDF.C_RDFPrefix -> Curry_RDF.C_RDFNode -> ConstStore -> Curry_Pretty.C_Doc
d_C_RDFNodeToDoc x1 x2 x3500 = case x2 of
     (Curry_RDF.C_RDFNode x3) -> d_C_URIToDoc x1 x3 x3500
     (Curry_RDF.C_BlankRDFNode x4) -> Curry_Prelude.d_OP_dollar (Curry_Pretty.d_C_angles x3500) (Curry_Pretty.d_C_text x4 x3500) x3500
     (Curry_RDF.C_LiteralRDFNode x5) -> Curry_Prelude.d_OP_dollar (Curry_Pretty.d_C_dquotes x3500) (Curry_Pretty.d_C_text x5 x3500) x3500
     (Curry_RDF.Choice_C_RDFNode x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_RDFNodeToDoc x1 x1002 x3500) (d_C_RDFNodeToDoc x1 x1003 x3500)
     (Curry_RDF.Choices_C_RDFNode x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_RDFNodeToDoc x1 z x3500) x1002
     (Curry_RDF.Guard_C_RDFNode x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_RDFNodeToDoc x1 x1002) $! (addCs x1001 x3500))
     (Curry_RDF.Fail_C_RDFNode x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_C_RDFNodeToDoc :: Curry_Prelude.OP_List Curry_RDF.C_RDFPrefix -> Curry_RDF.C_RDFNode -> IDSupply -> ConstStore -> Curry_Pretty.C_Doc
nd_C_RDFNodeToDoc x1 x2 x3000 x3500 = case x2 of
     (Curry_RDF.C_RDFNode x3) -> let
          x2000 = x3000
           in (seq x2000 (nd_C_URIToDoc x1 x3 x2000 x3500))
     (Curry_RDF.C_BlankRDFNode x4) -> let
          x2003 = x3000
           in (seq x2003 (let
               x2002 = leftSupply x2003
               x2004 = rightSupply x2003
                in (seq x2002 (seq x2004 (let
                    x2000 = leftSupply x2004
                    x2001 = rightSupply x2004
                     in (seq x2000 (seq x2001 (Curry_Prelude.nd_OP_dollar (Curry_Pretty.nd_C_angles x2000 x3500) (Curry_Pretty.nd_C_text x4 x2001 x3500) x2002 x3500))))))))
     (Curry_RDF.C_LiteralRDFNode x5) -> let
          x2003 = x3000
           in (seq x2003 (let
               x2002 = leftSupply x2003
               x2004 = rightSupply x2003
                in (seq x2002 (seq x2004 (let
                    x2000 = leftSupply x2004
                    x2001 = rightSupply x2004
                     in (seq x2000 (seq x2001 (Curry_Prelude.nd_OP_dollar (Curry_Pretty.nd_C_dquotes x2000 x3500) (Curry_Pretty.nd_C_text x5 x2001 x3500) x2002 x3500))))))))
     (Curry_RDF.Choice_C_RDFNode x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_C_RDFNodeToDoc x1 x1002 x3000 x3500) (nd_C_RDFNodeToDoc x1 x1003 x3000 x3500)
     (Curry_RDF.Choices_C_RDFNode x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_C_RDFNodeToDoc x1 z x3000 x3500) x1002
     (Curry_RDF.Guard_C_RDFNode x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_C_RDFNodeToDoc x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_RDF.Fail_C_RDFNode x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_RDFPredicateToDoc :: Curry_Prelude.OP_List Curry_RDF.C_RDFPrefix -> Curry_RDF.C_RDFPredicate -> ConstStore -> Curry_Pretty.C_Doc
d_C_RDFPredicateToDoc x1 x2 x3500 = case x2 of
     (Curry_RDF.C_RDFPredicate x3 x4) -> d_C_URIToDoc x1 x3 x3500
     (Curry_RDF.Choice_C_RDFPredicate x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_RDFPredicateToDoc x1 x1002 x3500) (d_C_RDFPredicateToDoc x1 x1003 x3500)
     (Curry_RDF.Choices_C_RDFPredicate x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_RDFPredicateToDoc x1 z x3500) x1002
     (Curry_RDF.Guard_C_RDFPredicate x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_RDFPredicateToDoc x1 x1002) $! (addCs x1001 x3500))
     (Curry_RDF.Fail_C_RDFPredicate x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_C_RDFPredicateToDoc :: Curry_Prelude.OP_List Curry_RDF.C_RDFPrefix -> Curry_RDF.C_RDFPredicate -> IDSupply -> ConstStore -> Curry_Pretty.C_Doc
nd_C_RDFPredicateToDoc x1 x2 x3000 x3500 = case x2 of
     (Curry_RDF.C_RDFPredicate x3 x4) -> let
          x2000 = x3000
           in (seq x2000 (nd_C_URIToDoc x1 x3 x2000 x3500))
     (Curry_RDF.Choice_C_RDFPredicate x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_C_RDFPredicateToDoc x1 x1002 x3000 x3500) (nd_C_RDFPredicateToDoc x1 x1003 x3000 x3500)
     (Curry_RDF.Choices_C_RDFPredicate x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_C_RDFPredicateToDoc x1 z x3000 x3500) x1002
     (Curry_RDF.Guard_C_RDFPredicate x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_C_RDFPredicateToDoc x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_RDF.Fail_C_RDFPredicate x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_RDFTripleToDoc :: Curry_Prelude.OP_List Curry_RDF.C_RDFPrefix -> Curry_RDF.C_RDFTriple -> ConstStore -> Curry_Pretty.C_Doc
d_C_RDFTripleToDoc x1 x2 x3500 = case x2 of
     (Curry_RDF.C_RDFTriple x3 x4 x5) -> Curry_Prelude.d_C_apply (Curry_Prelude.d_C_apply (Curry_Pretty.d_OP_lt_plus_gt x3500) (Curry_Prelude.d_C_apply (Curry_Prelude.d_C_apply (Curry_Pretty.d_OP_lt_plus_gt x3500) (Curry_Prelude.d_C_apply (Curry_Prelude.d_C_apply (Curry_Pretty.d_OP_lt_plus_gt x3500) (d_C_RDFNodeToDoc x1 x3 x3500) x3500) (d_C_RDFPredicateToDoc x1 x4 x3500) x3500) x3500) (d_C_RDFNodeToDoc x1 x5 x3500) x3500) x3500) (Curry_Pretty.d_C_dot x3500) x3500
     (Curry_RDF.Choice_C_RDFTriple x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_RDFTripleToDoc x1 x1002 x3500) (d_C_RDFTripleToDoc x1 x1003 x3500)
     (Curry_RDF.Choices_C_RDFTriple x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_RDFTripleToDoc x1 z x3500) x1002
     (Curry_RDF.Guard_C_RDFTriple x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_RDFTripleToDoc x1 x1002) $! (addCs x1001 x3500))
     (Curry_RDF.Fail_C_RDFTriple x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_C_RDFTripleToDoc :: Curry_Prelude.OP_List Curry_RDF.C_RDFPrefix -> Curry_RDF.C_RDFTriple -> IDSupply -> ConstStore -> Curry_Pretty.C_Doc
nd_C_RDFTripleToDoc x1 x2 x3000 x3500 = case x2 of
     (Curry_RDF.C_RDFTriple x3 x4 x5) -> let
          x2023 = x3000
           in (seq x2023 (let
               x2022 = leftSupply x2023
               x2024 = rightSupply x2023
                in (seq x2022 (seq x2024 (let
                    x2019 = leftSupply x2024
                    x2021 = rightSupply x2024
                     in (seq x2019 (seq x2021 (Curry_Prelude.nd_C_apply (let
                         x2018 = leftSupply x2019
                         x2020 = rightSupply x2019
                          in (seq x2018 (seq x2020 (let
                              x2000 = leftSupply x2020
                              x2016 = rightSupply x2020
                               in (seq x2000 (seq x2016 (Curry_Prelude.nd_C_apply (Curry_Pretty.nd_OP_lt_plus_gt x2000 x3500) (let
                                   x2015 = leftSupply x2016
                                   x2017 = rightSupply x2016
                                    in (seq x2015 (seq x2017 (let
                                        x2012 = leftSupply x2017
                                        x2014 = rightSupply x2017
                                         in (seq x2012 (seq x2014 (Curry_Prelude.nd_C_apply (let
                                             x2011 = leftSupply x2012
                                             x2013 = rightSupply x2012
                                              in (seq x2011 (seq x2013 (let
                                                  x2001 = leftSupply x2013
                                                  x2009 = rightSupply x2013
                                                   in (seq x2001 (seq x2009 (Curry_Prelude.nd_C_apply (Curry_Pretty.nd_OP_lt_plus_gt x2001 x3500) (let
                                                       x2008 = leftSupply x2009
                                                       x2010 = rightSupply x2009
                                                        in (seq x2008 (seq x2010 (let
                                                            x2005 = leftSupply x2010
                                                            x2007 = rightSupply x2010
                                                             in (seq x2005 (seq x2007 (Curry_Prelude.nd_C_apply (let
                                                                 x2004 = leftSupply x2005
                                                                 x2006 = rightSupply x2005
                                                                  in (seq x2004 (seq x2006 (let
                                                                      x2002 = leftSupply x2006
                                                                      x2003 = rightSupply x2006
                                                                       in (seq x2002 (seq x2003 (Curry_Prelude.nd_C_apply (Curry_Pretty.nd_OP_lt_plus_gt x2002 x3500) (nd_C_RDFNodeToDoc x1 x3 x2003 x3500) x2004 x3500))))))) (nd_C_RDFPredicateToDoc x1 x4 x2007 x3500) x2008 x3500))))))) x2011 x3500))))))) (nd_C_RDFNodeToDoc x1 x5 x2014 x3500) x2015 x3500))))))) x2018 x3500))))))) (Curry_Pretty.nd_C_dot x2021 x3500) x2022 x3500))))))))
     (Curry_RDF.Choice_C_RDFTriple x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_C_RDFTripleToDoc x1 x1002 x3000 x3500) (nd_C_RDFTripleToDoc x1 x1003 x3000 x3500)
     (Curry_RDF.Choices_C_RDFTriple x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_C_RDFTripleToDoc x1 z x3000 x3500) x1002
     (Curry_RDF.Guard_C_RDFTriple x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_C_RDFTripleToDoc x1 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_RDF.Fail_C_RDFTriple x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_RDFPrefixToDoc :: Curry_RDF.C_RDFPrefix -> ConstStore -> Curry_Pretty.C_Doc
d_C_RDFPrefixToDoc x1 x3500 = case x1 of
     (Curry_RDF.C_RDFPrefix x2 x3) -> Curry_Prelude.d_C_apply (Curry_Prelude.d_C_apply (Curry_Pretty.d_OP_lt_plus_gt x3500) (Curry_Prelude.d_C_apply (Curry_Prelude.d_C_apply (Curry_Pretty.d_OP_lt_plus_gt x3500) (Curry_Pretty.d_OP_lt_gt (Curry_Prelude.d_C_apply (Curry_Prelude.d_C_apply (Curry_Pretty.d_OP_lt_plus_gt x3500) (Curry_Pretty.d_C_text (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '@'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'f'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'x'#) Curry_Prelude.OP_List))))))) x3500) x3500) (Curry_Pretty.d_C_text x2 x3500) x3500) (Curry_Pretty.d_C_colon x3500) x3500) x3500) (Curry_Prelude.d_C_apply (Curry_Pretty.d_C_angles x3500) (Curry_Pretty.d_C_text x3 x3500) x3500) x3500) x3500) (Curry_Pretty.d_C_dot x3500) x3500
     (Curry_RDF.Choice_C_RDFPrefix x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_RDFPrefixToDoc x1002 x3500) (d_C_RDFPrefixToDoc x1003 x3500)
     (Curry_RDF.Choices_C_RDFPrefix x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_RDFPrefixToDoc z x3500) x1002
     (Curry_RDF.Guard_C_RDFPrefix x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_RDFPrefixToDoc x1002) $! (addCs x1001 x3500))
     (Curry_RDF.Fail_C_RDFPrefix x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_C_RDFPrefixToDoc :: Curry_RDF.C_RDFPrefix -> IDSupply -> ConstStore -> Curry_Pretty.C_Doc
nd_C_RDFPrefixToDoc x1 x3000 x3500 = case x1 of
     (Curry_RDF.C_RDFPrefix x2 x3) -> let
          x2031 = x3000
           in (seq x2031 (let
               x2030 = leftSupply x2031
               x2032 = rightSupply x2031
                in (seq x2030 (seq x2032 (let
                    x2027 = leftSupply x2032
                    x2029 = rightSupply x2032
                     in (seq x2027 (seq x2029 (Curry_Prelude.nd_C_apply (let
                         x2026 = leftSupply x2027
                         x2028 = rightSupply x2027
                          in (seq x2026 (seq x2028 (let
                              x2000 = leftSupply x2028
                              x2024 = rightSupply x2028
                               in (seq x2000 (seq x2024 (Curry_Prelude.nd_C_apply (Curry_Pretty.nd_OP_lt_plus_gt x2000 x3500) (let
                                   x2023 = leftSupply x2024
                                   x2025 = rightSupply x2024
                                    in (seq x2023 (seq x2025 (let
                                        x2016 = leftSupply x2025
                                        x2021 = rightSupply x2025
                                         in (seq x2016 (seq x2021 (Curry_Prelude.nd_C_apply (let
                                             x2015 = leftSupply x2016
                                             x2017 = rightSupply x2016
                                              in (seq x2015 (seq x2017 (let
                                                  x2001 = leftSupply x2017
                                                  x2013 = rightSupply x2017
                                                   in (seq x2001 (seq x2013 (Curry_Prelude.nd_C_apply (Curry_Pretty.nd_OP_lt_plus_gt x2001 x3500) (let
                                                       x2012 = leftSupply x2013
                                                       x2014 = rightSupply x2013
                                                        in (seq x2012 (seq x2014 (let
                                                            x2009 = leftSupply x2014
                                                            x2011 = rightSupply x2014
                                                             in (seq x2009 (seq x2011 (Curry_Pretty.nd_OP_lt_gt (let
                                                                 x2008 = leftSupply x2009
                                                                 x2010 = rightSupply x2009
                                                                  in (seq x2008 (seq x2010 (let
                                                                      x2005 = leftSupply x2010
                                                                      x2007 = rightSupply x2010
                                                                       in (seq x2005 (seq x2007 (Curry_Prelude.nd_C_apply (let
                                                                           x2004 = leftSupply x2005
                                                                           x2006 = rightSupply x2005
                                                                            in (seq x2004 (seq x2006 (let
                                                                                x2002 = leftSupply x2006
                                                                                x2003 = rightSupply x2006
                                                                                 in (seq x2002 (seq x2003 (Curry_Prelude.nd_C_apply (Curry_Pretty.nd_OP_lt_plus_gt x2002 x3500) (Curry_Pretty.nd_C_text (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char '@'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'p'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'r'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'e'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'f'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'i'#) (Curry_Prelude.OP_Cons (Curry_Prelude.C_Char 'x'#) Curry_Prelude.OP_List))))))) x2003 x3500) x2004 x3500))))))) (Curry_Pretty.nd_C_text x2 x2007 x3500) x2008 x3500))))))) (Curry_Pretty.nd_C_colon x2011 x3500) x2012 x3500))))))) x2015 x3500))))))) (let
                                             x2020 = leftSupply x2021
                                             x2022 = rightSupply x2021
                                              in (seq x2020 (seq x2022 (let
                                                  x2018 = leftSupply x2022
                                                  x2019 = rightSupply x2022
                                                   in (seq x2018 (seq x2019 (Curry_Prelude.nd_C_apply (Curry_Pretty.nd_C_angles x2018 x3500) (Curry_Pretty.nd_C_text x3 x2019 x3500) x2020 x3500))))))) x2023 x3500))))))) x2026 x3500))))))) (Curry_Pretty.nd_C_dot x2029 x3500) x2030 x3500))))))))
     (Curry_RDF.Choice_C_RDFPrefix x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_C_RDFPrefixToDoc x1002 x3000 x3500) (nd_C_RDFPrefixToDoc x1003 x3000 x3500)
     (Curry_RDF.Choices_C_RDFPrefix x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_C_RDFPrefixToDoc z x3000 x3500) x1002
     (Curry_RDF.Guard_C_RDFPrefix x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_C_RDFPrefixToDoc x1002 x3000) $! (addCs x1001 x3500))
     (Curry_RDF.Fail_C_RDFPrefix x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_RDFGraphToDoc :: Curry_RDF.C_RDFGraph -> ConstStore -> Curry_Pretty.C_Doc
d_C_RDFGraphToDoc x1 x3500 = case x1 of
     (Curry_RDF.C_RDFGraph x2 x3) -> Curry_Pretty.d_OP_lt_gt (Curry_Prelude.d_C_apply (Curry_Prelude.d_C_apply (Curry_Pretty.d_OP_lt_dollar_dollar_gt x3500) (Curry_Prelude.d_OP_dollar (Curry_Pretty.d_C_vcat x3500) (Curry_Prelude.d_C_map d_C_RDFPrefixToDoc x2 x3500) x3500) x3500) (Curry_Pretty.d_C_linebreak x3500) x3500) (Curry_Prelude.d_OP_dollar (Curry_Pretty.d_C_vcat x3500) (Curry_Prelude.d_C_map (d_C_RDFTripleToDoc x2) x3 x3500) x3500) x3500
     (Curry_RDF.Choice_C_RDFGraph x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_C_RDFGraphToDoc x1002 x3500) (d_C_RDFGraphToDoc x1003 x3500)
     (Curry_RDF.Choices_C_RDFGraph x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_C_RDFGraphToDoc z x3500) x1002
     (Curry_RDF.Guard_C_RDFGraph x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_C_RDFGraphToDoc x1002) $! (addCs x1001 x3500))
     (Curry_RDF.Fail_C_RDFGraph x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_C_RDFGraphToDoc :: Curry_RDF.C_RDFGraph -> IDSupply -> ConstStore -> Curry_Pretty.C_Doc
nd_C_RDFGraphToDoc x1 x3000 x3500 = case x1 of
     (Curry_RDF.C_RDFGraph x2 x3) -> let
          x2019 = x3000
           in (seq x2019 (let
               x2018 = leftSupply x2019
               x2020 = rightSupply x2019
                in (seq x2018 (seq x2020 (let
                    x2011 = leftSupply x2020
                    x2016 = rightSupply x2020
                     in (seq x2011 (seq x2016 (Curry_Pretty.nd_OP_lt_gt (let
                         x2010 = leftSupply x2011
                         x2012 = rightSupply x2011
                          in (seq x2010 (seq x2012 (let
                              x2007 = leftSupply x2012
                              x2009 = rightSupply x2012
                               in (seq x2007 (seq x2009 (Curry_Prelude.nd_C_apply (let
                                   x2006 = leftSupply x2007
                                   x2008 = rightSupply x2007
                                    in (seq x2006 (seq x2008 (let
                                        x2000 = leftSupply x2008
                                        x2004 = rightSupply x2008
                                         in (seq x2000 (seq x2004 (Curry_Prelude.nd_C_apply (Curry_Pretty.nd_OP_lt_dollar_dollar_gt x2000 x3500) (let
                                             x2003 = leftSupply x2004
                                             x2005 = rightSupply x2004
                                              in (seq x2003 (seq x2005 (let
                                                  x2001 = leftSupply x2005
                                                  x2002 = rightSupply x2005
                                                   in (seq x2001 (seq x2002 (Curry_Prelude.nd_OP_dollar (Curry_Pretty.nd_C_vcat x2001 x3500) (Curry_Prelude.nd_C_map (wrapNX id nd_C_RDFPrefixToDoc) x2 x2002 x3500) x2003 x3500))))))) x2006 x3500))))))) (Curry_Pretty.nd_C_linebreak x2009 x3500) x2010 x3500))))))) (let
                         x2015 = leftSupply x2016
                         x2017 = rightSupply x2016
                          in (seq x2015 (seq x2017 (let
                              x2013 = leftSupply x2017
                              x2014 = rightSupply x2017
                               in (seq x2013 (seq x2014 (Curry_Prelude.nd_OP_dollar (Curry_Pretty.nd_C_vcat x2013 x3500) (Curry_Prelude.nd_C_map (wrapNX id (nd_C_RDFTripleToDoc x2)) x3 x2014 x3500) x2015 x3500))))))) x2018 x3500))))))))
     (Curry_RDF.Choice_C_RDFGraph x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_C_RDFGraphToDoc x1002 x3000 x3500) (nd_C_RDFGraphToDoc x1003 x3000 x3500)
     (Curry_RDF.Choices_C_RDFGraph x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_C_RDFGraphToDoc z x3000 x3500) x1002
     (Curry_RDF.Guard_C_RDFGraph x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_C_RDFGraphToDoc x1002 x3000) $! (addCs x1001 x3500))
     (Curry_RDF.Fail_C_RDFGraph x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

d_C_RDFGraphToString :: Curry_Prelude.C_Int -> ConstStore -> Curry_RDF.C_RDFGraph -> ConstStore -> Curry_Prelude.OP_List Curry_Prelude.C_Char
d_C_RDFGraphToString x1 x3500 = Curry_Prelude.d_OP_dot (Curry_Pretty.d_C_pretty x1) d_C_RDFGraphToDoc x3500

nd_C_RDFGraphToString :: Curry_Prelude.C_Int -> IDSupply -> ConstStore -> Func Curry_RDF.C_RDFGraph (Curry_Prelude.OP_List Curry_Prelude.C_Char)
nd_C_RDFGraphToString x1 x3000 x3500 = let
     x2000 = x3000
      in (seq x2000 (Curry_Prelude.nd_OP_dot (wrapNX id (Curry_Pretty.nd_C_pretty x1)) (wrapNX id nd_C_RDFGraphToDoc) x2000 x3500))

d_OP__case_0 x1 x2 x3 x3500 = case x3 of
     Curry_Prelude.C_True -> Curry_Prelude.d_OP_dollar Curry_Pretty.d_C_text (Curry_RDF.d_C_prefixURI x1 x2 x3500) x3500
     Curry_Prelude.C_False -> Curry_Prelude.d_OP_dollar (Curry_Pretty.d_C_angles x3500) (Curry_Pretty.d_C_text x2 x3500) x3500
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (d_OP__case_0 x1 x2 x1002 x3500) (d_OP__case_0 x1 x2 x1003 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> d_OP__case_0 x1 x2 z x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((d_OP__case_0 x1 x2 x1002) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo

nd_OP__case_0 x1 x2 x3 x3000 x3500 = case x3 of
     Curry_Prelude.C_True -> let
          x2000 = x3000
           in (seq x2000 (Curry_Prelude.nd_OP_dollar (wrapNX id Curry_Pretty.nd_C_text) (Curry_RDF.d_C_prefixURI x1 x2 x3500) x2000 x3500))
     Curry_Prelude.C_False -> let
          x2003 = x3000
           in (seq x2003 (let
               x2002 = leftSupply x2003
               x2004 = rightSupply x2003
                in (seq x2002 (seq x2004 (let
                    x2000 = leftSupply x2004
                    x2001 = rightSupply x2004
                     in (seq x2000 (seq x2001 (Curry_Prelude.nd_OP_dollar (Curry_Pretty.nd_C_angles x2000 x3500) (Curry_Pretty.nd_C_text x2 x2001 x3500) x2002 x3500))))))))
     (Curry_Prelude.Choice_C_Bool x1000 x1001 x1002 x1003) -> narrow x1000 x1001 (nd_OP__case_0 x1 x2 x1002 x3000 x3500) (nd_OP__case_0 x1 x2 x1003 x3000 x3500)
     (Curry_Prelude.Choices_C_Bool x1000 x1001 x1002) -> narrows x3500 x1000 x1001 (\z -> nd_OP__case_0 x1 x2 z x3000 x3500) x1002
     (Curry_Prelude.Guard_C_Bool x1000 x1001 x1002) -> guardCons x1000 x1001 ((nd_OP__case_0 x1 x2 x1002 x3000) $! (addCs x1001 x3500))
     (Curry_Prelude.Fail_C_Bool x1000 x1001) -> failCons x1000 x1001
     _ -> failCons defCover defFailInfo
