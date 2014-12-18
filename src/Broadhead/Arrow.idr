module Broadhead.Arrow

import Control.Arrow
import Control.Category

infixr 5 <++>
infixr 2 +++
infixr 2 \|/
infixr 1 >>^

class Arrow arr => ArrowZero (arr : Type -> Type -> Type) where
  zeroArrow : arr a b

class ArrowZero arr => ArrowPlus (arr : Type -> Type -> Type) where
  (<++>) : arr a b -> arr a b -> arr a b

class Arrow arr => ArrowChoice (arr : Type -> Type -> Type) where
  left : arr a b -> arr (Either a c) (Either b c)

  right : arr a b -> arr (Either c a) (Either c b)
  right f = arrow swap >>> left f >>> arrow swap where
    swap : Either a b -> Either b a
    swap (Left x) = Right x
    swap (Right x) = Left x

  (+++) : arr a b -> arr c d -> arr (Either a c) (Either b d)
  f +++ g = left f >>> right g

  (\|/) : arr a b -> arr c b -> arr (Either a c) b
  f \|/ g = f +++ g >>> arrow fromEither

instance Monad m => ArrowChoice (Kleislimorphism m) where
  left  f                     = f          +++ (arrow id)
  right f                     = (arrow id) +++ f
  f           +++ g           = (f >>> (arrow Left)) \|/ (g >>> (arrow Right))
  (Kleisli f) \|/ (Kleisli g) = Kleisli (either f g)

class Arrow arr => ArrowApply (arr : Type -> Type -> Type) where
  app : arr (arr a b, a) b

instance Monad m => ArrowApply (Kleislimorphism m) where
  app = Kleisli $ \(Kleisli f, x) => f x

data ArrowMonad : (Type -> Type -> Type) -> Type -> Type where
  MkArrowMonad : (runArrowMonad : arr (the Type ()) a) -> ArrowMonad arr a

runArrowMonad : ArrowMonad arr a -> arr (the Type ()) a
runArrowMonad (MkArrowMonad a) = a

instance Arrow a => Functor (ArrowMonad a) where
  map f (MkArrowMonad m) = MkArrowMonad $ m >>> arrow f

instance Arrow a => Applicative (ArrowMonad a) where
  pure x = MkArrowMonad $ arrow $ \_ => x
  (MkArrowMonad f) <$> (MkArrowMonad x) = MkArrowMonad $ f &&& x >>> arrow (uncurry id)

instance ArrowApply a => Monad (ArrowMonad a) where
  (MkArrowMonad m) >>= f =
    MkArrowMonad $ m >>> (arrow $ \x => (runArrowMonad (f x), ())) >>> app

class Arrow arr => ArrowLoop (arr : Type -> Type -> Type) where
  loop : arr (Pair a c) (Pair b c) -> arr a b

(>>^) : Arrow a => a b c -> (c -> d) -> a b d
a >>^ f = a >>> arrow f
