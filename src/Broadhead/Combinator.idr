module Broadhead.Combinator

import Broadhead.Arrow
import Broadhead.CharSet
import Broadhead.Core
import Control.Arrow
import Control.Category

empty : BP t i o
empty = PEmpty

many : BP t i o -> BP t i (List o)
many = PStar

some : BP t i o -> BP t i (List o)
some x = (x &&& (PStar x)) >>> arrow (\(b,bs) => (b::bs))

notFollowedBy : BP t i o -> BP t i o
notFollowedBy = PNot

sepBy : BP t i o -> BP t i o' -> BP t i (List o)
sepBy p s = many (p &&& s >>^ fst)

sepBy1 : BP t i o -> BP t i o' -> BP t i (List o)
sepBy1 p s = (many (p &&& s >>^ fst) &&& p) >>^ (\(bs,b) => bs++[b])

nTimes : (n : Nat) -> BP t i o -> BP t i (Vect (S n) o)
nTimes (S Z)     p = p >>^ pure
nTimes (S (S n)) p = (p &&& nTimes (S n) p) >>^  (\(b,bs) => (b::bs))

between : BP t i p -> BP t p c -> BP t p o -> BP t i o
between open close real = open >>> (real &&& close) >>^ fst

optional : BP t i o -> BP t i (Maybe o)
optional iarr = PChoice [iarr >>> PPrim Just, PPrim (const Nothing)]
