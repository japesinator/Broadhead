module Broadhead.Core

import Broadhead.Arrow
import Broadhead.CharSet
import Control.Arrow
import Control.Category

infixr 5 <->>
infixr 5 <<->
infixr 5 <-=>
infixr 5 <==>

data BP : Type -> Type -> Type -> Type where
  PEmpty   :                                       BP t i       o
  PPrim    :                           (i -> o) -> BP t i       o
  PCSet    :                            CharSet -> BP t i       Char
  PNot     :                       BP t i    o  -> BP t i       o
  PStar    : {o : Type} ->         BP t i    o  -> BP t i       (List o)
  PChoice  : {n : Nat} -> Vect n $ BP t i    o  -> BP t i       o
  PSeq     : BP t i  p          -> BP t p    o  -> BP t i       o
  PJoin    : BP t i  o1         -> BP t i    o2 -> BP t i       (o1,o2)
  PParWire : BP t i1 o1         -> BP t i2   o2 -> BP t (i1,i2) (o1,o2)

(<->>) : BP t i p -> BP t p o -> BP t i o
(<->>) = PSeq

(<<->) : BP t p o -> BP t i p -> BP t i o
a <<-> b = PSeq b a

(<-=>) : BP t i o1 -> BP t i o2 -> BP t i (o1, o2)
(<-=>) = PJoin

(<==>) : BP t i1 o1 -> BP t i2 o2 -> BP t (i1,i2) (o1, o2)
(<==>) = PParWire

instance Category (BP t) where
  id    = PPrim id
  b . a = a <->> b

instance Arrow (BP t) where
  arrow   = PPrim
  first a = a <==> id
  second  = PParWire id
  (***)   = (<==>)
  (&&&)   = (<-=>)

instance ArrowZero (BP t) where
  zeroArrow = PEmpty

instance ArrowPlus (BP t) where
  (PChoice a) <++> (PChoice b) = PChoice (a ++ b)
  a           <++> (PChoice b) = PChoice (a :: b)
  a           <++> b           = PChoice [a ,  b]
