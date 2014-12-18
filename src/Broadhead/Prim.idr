module Broadhead.Prim

import Broadhead.CharSet
import Broadhead.Core

data PS : Type -> Type where
  MkPS : (List c) -> PS c

data Res c r = POk (PS c) r
             | PErr (List String)

PSF : Type -> Type -> Type
PSF c r = PS c -> Res c r

parse : BP t i o -> PSF Char o
parse PEmpty i = POk i $ believe_me "empty"
parse (PPrim _) i = POk i $ believe_me "prim"
parse (PEqual c) (MkPS (x :: xs)) = if x == c
                                       then POk (MkPS xs) c
                                       else PErr $ pure $ "Expected " ++ (show c)
parse (PCSet cs) (MkPS (x :: xs)) = if (x) `elem` csetValue cs
                                       then POk (MkPS (xs)) x
                                       else PErr ["Expected " ++ show cs]
parse (PNot x) i = case parse x i of
                        POk _ _  => PErr ["Not"]
                        PErr _   => POk i $ believe_me "not"
parse (PStar {o} x) i = sm i (the (List o) []) where
  sm : (PS Char) -> List o -> Res Char (List o)
  sm st acc = case parse x st of
                   POk st' r => sm st' (r :: acc)
                   PErr _    => POk st (the (List o) (reverse acc))
parse (PChoice {n} l) i = case n of
                               Z     => PErr ["No choice matches"]
                               (S n) => case parse (head l) i of
                                             POk s t => POk s t
                                             _       => parse (PChoice $ tail l) i
parse (PSeq a b) i = case parse a i of
                          PErr e  => PErr e
                          POk s t => case b of
                                          (PPrim f) => POk s (f t)
                                          _         => parse b s
parse (PJoin a b) i = case parse a i of
                           PErr e  => PErr e
                           POk s t => case parse b s of
                                           PErr e'   => PErr e'
                                           POk s' t' => POk s' (t,t')
parse (PParWire _ _) i = PErr ["Parsed parwire.  That shouldn't have happened"]
parse _ (MkPS Nil) = PErr ["EOF"]
parse _ _ = PErr ["Unknown"]
