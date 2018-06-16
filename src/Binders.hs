{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Binders where

import Control.Monad (ap, join)
import GHC.Generics

-- * Functors of endofunctors

-- TODO: doc, explain the restriction for actually being a natural
-- transformation.
type f ~> g = forall a. f a -> g a

-- TODO: doc, esp. laws
class
    (forall f. Functor f => Functor (h f))
    => Functor1 (h :: (* -> *) -> * -> *)
  where
    fmap1 :: (f ~> g) -> h f ~> h g

    default fmap1
      :: (Generic1 (h f), Generic1 (h g), GFunctor1 (Rep1 (h f)) (Rep1 (h g)) f g)
      => (f ~> g) -> h f ~> h g
    fmap1 alpha = to1 . gfmap1 alpha . from1

-- TODO: add link to "functorial strength" on wikipedia
-- | The intuition behind @Strong1 h@ is that @h@ acts on monads. Indeed if
-- @f=g=m@ is a monad, then @\x -> strength1 x join :: h m (m a) -> h m a@. This
-- is a limited explanation, but I don't know much more yet.
--
-- As additional background, for the curious programmer: from a mathematical
-- point of view, 'strenght1' is a functorial strength. For regular functors, a
-- strength is a function @(f a, b) -> f (a, b)@. But for regular functor, there
-- is always such a strength: @\(fa, b) -> (, b) <$> fa@ (this strength is
-- implicitly but critically used in the definition of the do-notation).
-- However functors of endofunctors don't necessarily have a strength (in fact
-- 'Var' below doesn't have one). So we need an additional type class to record
-- that functors are strong.
--
-- Like in the infamous phrase "a monad is a monoid in the category of
-- endofunctors", the natural product of endofunctors is composition. It is not
-- hard to verify that, up to 'map1', the type of 'strength1' is equivalent to
-- @h f `Compose` g ~> h (f `Compose` g)@. We choose this formulation because it
-- avoids annotations to convert between @Compose f g a@ and @f (g a)@.
--
-- In any case, this is a natural notion from a mathematics point of view. And
-- not as /ad hoc/ as it may appear at first glance.
class Functor1 h => Strong1 h where
  strength1 :: h f (g a) -> (forall b. f (g b) -> j b) -> h j a

-- TODO: doc
data Either2
  (h :: (* -> *) -> * -> *) (j :: (* -> *) -> * -> *) (f :: * -> *) (a :: *)
  = Left2 (h f a)
  | Right2  (j f a)
  deriving (Generic1, Functor)

instance (Functor1 h, Functor1 j) => Functor1 (Either2 h j)

instance (Strong1 h, Strong1 j) => Strong1 (Either2 h j) where
  strength1 (Left2 x) alpha = Left2 $ strength1 x alpha
  strength1 (Right2 y) alpha = Right2 $ strength1 y alpha

-- TODO: doc, remark that, from an AST point of view, this is the prototypical
-- new thing. Show that this is not strong (/e.g./ Var Identity (Const ()) Void).
data Var (f :: * -> *) (a :: *) = Var a
  deriving (Generic1, Functor)

instance Functor1 Var where

-- * Non-uniform fixed point

-- TODO: doc, relation between this and non-uniform data type (example:
-- perfectly balanced binary tree @data Tree a = Leaf a | Node (Tree (a, a)))@)
newtype Mu (h :: (* -> *) -> * -> *) (a :: *) = Roll { unroll :: h (Mu h) a }

instance Functor1 h => Functor (Mu h) where
  fmap f (Roll t) = Roll $ fmap f t

instance Strong1 h => Applicative (Mu (Var `Either2` h)) where
  pure x = Roll . Left2 $ Var x
  (<*>) = ap

-- TODO: clearly we should have @Var `Either2` _@ as a macro-operator.
instance Strong1 h => Monad (Mu (Var `Either2` h)) where
  t >>= subst = joinTerm $ fmap subst t
    where
      joinTerm
        :: Strong1 h
        => Mu (Var `Either2` h) (Mu (Var `Either2` h) a)
        -> Mu (Var `Either2` h) a
      joinTerm (Roll (Left2 (Var v))) = v
      joinTerm (Roll (Right2 u)) = Roll . Right2 $ strength1 u join

-- TODO: link to catamorphisms, @Mu@ is the initial algebra yadda yadda.
cata1 :: Functor1 h => (h f ~> f) -> Mu h ~> f
cata1 alg (Roll t) = alg $ fmap1 (cata1 alg) t

-- * Deriving instances

-- ** Deriving 'Functor1'

-- TODO: explain what needs to be done to derive things

-- | A class for deriving 'Functor1' instances generic types. We would really
-- need a @Generic2@ framework (because our types have two arguments). Instead
-- we use an encoding trick, related to the way lenses are defined in the
-- <http://hackage.haskell.org/package/lens lens library>. This trick is due to
-- Csongor Kiss, and documented in
-- <http://kcsongor.github.io/generic-deriving-bifunctor/ this blog post>.
--
-- The intuition is that the first two argument @h@ and @j@ of the type class,
-- are stand-ins for @h' f@ and @h' g@.
class GFunctor1 (h :: * -> *) (j :: * -> *) (f :: * -> *) (g :: * -> *) where
  gfmap1 :: (f ~> g) -> (h ~> j)

instance {-# INCOHERENT #-} GFunctor1 (Rec1 f) (Rec1 g) f g where
  gfmap1 alpha (Rec1 a) = Rec1 $ alpha a

instance {-# INCOHERENT #-} GFunctor1 (Rec1 i) (Rec1 i) f g where
  gfmap1 _ = id

instance {-# INCOHERENT #-} Functor1 h => GFunctor1 (Rec1 (h f)) (Rec1 (h g)) f g where
  gfmap1 alpha (Rec1 a) = Rec1 $ fmap1 alpha a

instance GFunctor1 V1 V1 f g where
  gfmap1 _ = id

instance GFunctor1 U1 U1 f g where
  gfmap1 _ = id

instance GFunctor1 Par1 Par1 f g where
  gfmap1 _ = id

instance GFunctor1 (K1 i c) (K1 i c) g f where
  gfmap1 _ = id

instance GFunctor1 h j f g => GFunctor1 (M1 i c h) (M1 i c j) f g where
  gfmap1 alpha (M1 a) = M1 $ gfmap1 alpha a

instance
    (GFunctor1 h1 j1 f g, GFunctor1 h2 j2 f g)
    => GFunctor1 (h1 :+: h2) (j1 :+: j2) f g
  where
    gfmap1 alpha (L1 a) = L1 $ gfmap1 alpha a
    gfmap1 alpha (R1 a) = R1 $ gfmap1 alpha a

instance
    (GFunctor1 h1 j1 f g, GFunctor1 h2 j2 f g)
    => GFunctor1 (h1 :*: h2) (j1 :*: j2) f g
  where
    gfmap1 alpha (a :*: b) = gfmap1 alpha a :*: gfmap1 alpha b

instance
    (GFunctor1 h1 j1 f g, GFunctor1 h2 j2 f g, Functor h1)
    => GFunctor1 (h1 :.: h2) (j1 :.: j2) f g
  where
    gfmap1 alpha (Comp1 a) = Comp1 $ gfmap1 alpha (fmap (gfmap1 alpha) a)

--  LocalWords:  monads monad functorial functor functors endofunctors monoid
