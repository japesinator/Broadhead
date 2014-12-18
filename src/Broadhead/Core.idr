module Broadhead.Core

import Broadhead.Arrow
import Broadhead.CharSet
import Control.Arrow
import Control.Category

infixr 5 <->>
infixr 5 <<->
infixr 5 <-=>
infixr 5 <==>

data BP :  Type -> Type -> Type where
  PEmpty   :                                     BP i       o
  PPrim    :                         (i -> o) -> BP i       o
  PEqual   :                          Char    -> BP i       Char
  PCSet    :                          CharSet -> BP i       Char
  PNot     :                       BP i    o  -> BP i       o
  PStar    : {o : Type} ->         BP i    o  -> BP i       (List o)
  PChoice  : {n : Nat} -> Vect n $ BP i    o  -> BP i       o
  PSeq     : BP i  p            -> BP p    o  -> BP i       o
  PJoin    : BP i  o1           -> BP i    o2 -> BP i       (o1,o2)
  PParWire : BP i1 o1           -> BP i2   o2 -> BP (i1,i2) (o1,o2)

(<->>) : BP i p -> BP p o -> BP i o
(<->>) = PSeq

(<<->) : BP p o -> BP i p -> BP i o
a <<-> b = PSeq b a

(<-=>) : BP i o1 -> BP i o2 -> BP i (o1, o2)
(<-=>) = PJoin

(<==>) : BP i1 o1 -> BP i2 o2 -> BP (i1,i2) (o1, o2)
(<==>) = PParWire

instance Category BP where
  id    = PPrim id
  b . a = a <->> b

instance Arrow BP where
  arrow   = PPrim
  first a = a <==> id
  second  = PParWire id
  (***)   = (<==>)
  (&&&)   = (<-=>)

instance ArrowZero BP where
  zeroArrow = PEmpty

instance ArrowPlus BP where
  (PChoice a) <++> (PChoice b) = PChoice (a ++ b)
  a           <++> (PChoice b) = PChoice (a :: b)
  a           <++> b           = PChoice [a ,  b]
