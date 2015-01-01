module Broadhead.Combinator

import Broadhead.Arrow
import Broadhead.CharSet
import Broadhead.Core
import Control.Arrow
import Control.Category

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
sepBy p s = many (p &&& s `comp` fst) where
  comp : Arrow a => a b c -> (c -> d) -> a b d
  comp a f = a >>> arrow f

||| Match at least one thing seperated by other things
sepBy1 : BP i o -> BP i o' -> BP i (List o)
sepBy1 p s = (many (p &&& s `comp` fst) &&& p) `comp` (\(bs,b) => bs++[b]) where
  comp : Arrow a => a b c -> (c -> d) -> a b d
  comp a f = a >>> arrow f

||| Match n occurences of something
nTimes : (n : Nat) -> BP i o -> BP i (Vect (S n) o)
nTimes (S Z)     p = p `comp` pure where
  comp : Arrow a => a b c -> (c -> d) -> a b d
  comp a f = a >>> arrow f
nTimes (S (S n)) p = (p &&& nTimes (S n) p) `comp`  (\(b,bs) => (b::bs)) where
  comp : Arrow a => a b c -> (c -> d) -> a b d
  comp a f = a >>> arrow f


||| Match a thing inbetween an opening and closing thing
between : BP i p -> BP p c -> BP p o -> BP i o
between open close real = open >>> (real &&& close) `comp` fst where
  comp : Arrow a => a b c -> (c -> d) -> a b d
  comp a f = a >>> arrow f

||| Match something. Or don't. It's whatever, man
optional : BP i o -> BP i (Maybe o)
optional iarr = PChoice [iarr >>> PPrim Just, PPrim (const Nothing)]
