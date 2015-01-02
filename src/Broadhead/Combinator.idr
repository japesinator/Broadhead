module Broadhead.Combinator

import Broadhead.Arrow
import Broadhead.CharSet
import Broadhead.Core
import Control.Arrow
import Control.Category

infixr 1 >>^
private
(>>^) : Arrow a => a b c -> (c -> d) -> a b d
a >>^ f = a >>> arrow f

||| Match nothing at all
empty : BP i o
empty = PEmpty

||| Match a bunch of occurences of some parser
many : BP i o -> BP i (List o)
many = PStar

||| Match at least one occurence of some parser
some : BP i o -> BP i (List o)
some x = (x &&& (PStar x)) >>> arrow (\(b,bs) => (b::bs))

||| Match a thing as long as it isn't followed by something else
notFollowedBy : BP i o -> BP i o
notFollowedBy = PNot

||| Match a list of things seperated by other things
sepBy : BP i o -> BP i o' -> BP i (List o)
sepBy p s = many (p &&& s >>^ fst)

||| Match at least one thing seperated by other things
sepBy1 : BP i o -> BP i o' -> BP i (List o)
sepBy1 p s = (many (p &&& s >>^ fst) &&& p) >>^ (\(bs,b) => bs++[b])

||| Match n occurences of something
nTimes : (n : Nat) -> BP i o -> BP i (Vect (S n) o)
nTimes (S Z)     p = p >>^ pure
nTimes (S (S n)) p = (p &&& nTimes (S n) p) >>^  (\(b,bs) => (b::bs))

||| Match a thing inbetween an opening and closing thing
between : BP i p -> BP p c -> BP p o -> BP i o
between open close real = open >>> (real &&& close) >>^ fst

||| Match something. Or don't. It's whatever, man
optional : BP i o -> BP i (Maybe o)
optional iarr = PChoice [iarr >>> PPrim Just, PPrim (const Nothing)]
