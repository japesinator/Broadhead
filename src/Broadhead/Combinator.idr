module Broadhead.Combinator

import Broadhead.Arrow
import Broadhead.CharSet
import Broadhead.Core
import Control.Arrow
import Control.Category

empty : BP i o
empty = PEmpty

many : BP i o -> BP i (List o)
many = PStar

some : BP i o -> BP i (List o)
some x = (x &&& (PStar x)) >>> arrow (\(b,bs) => (b::bs))

notFollowedBy : BP i o -> BP i o
notFollowedBy = PNot

sepBy : BP i o -> BP i o' -> BP i (List o)
sepBy p s = many (p &&& s >>^ fst)

sepBy1 : BP i o -> BP i o' -> BP i (List o)
sepBy1 p s = (many (p &&& s >>^ fst) &&& p) >>^ (\(bs,b) => bs++[b])

nTimes : (n : Nat) -> BP i o -> BP i (Vect (S n) o)
nTimes (S Z)     p = p >>^ pure
nTimes (S (S n)) p = (p &&& nTimes (S n) p) >>^  (\(b,bs) => (b::bs))

between : BP i p -> BP p c -> BP p o -> BP i o
between open close real = open >>> (real &&& close) >>^ fst

optional : BP i o -> BP i (Maybe o)
optional iarr = PChoice [iarr >>> PPrim Just, PPrim (const Nothing)]
