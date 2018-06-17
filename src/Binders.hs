{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Binders
 ( -- * Functors of endofunctors
   -- $functor1-and-pfunctor1

   -- ** Simple functors
   -- $functor1
   type (~>)
 , Functor1
 , Strong1
 , Either2
 , Var
   -- ** Parametric functors
   -- $pfunctor1
 , PFunctor1
   -- * Non-uniform fixed point
   -- $fixed-points

   -- ** Simple fixed point
   -- $mu
 , Mu(..)
 , cata1
   -- ** Mutually recursive fixed point
   -- $mmu
 , MMu
 , pcata1
   -- * Deriving instances
   -- $generic-deriving

   -- ** Deriving 'Functor1'
   -- $deriving-functor1
 , GFunctor1
   -- ** Deriving 'Strong1'
   -- $deriving-strong1
 , GStrong1
 ) where

import Data.Kind
import Control.Monad (ap, join)
import GHC.Generics

-- $functor1-and-pfunctor1

-- $functor1

-- TODO: doc, explain the restriction for actually being a natural
-- transformation.
type f ~> g = forall a. f a -> g a

-- TODO: doc, esp. laws
class
    (forall f. Functor f => Functor (h f))
    => Functor1 (h :: (* -> *) -> * -> *)
  where
    fmap1 :: (Functor f, Functor g) => (f ~> g) -> h f ~> h g

    default fmap1
      :: ( Generic1 (h f), Generic1 (h g), GFunctor1 (Rep1 (h f)) (Rep1 (h g)) f g
         , Functor f, Functor g )
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
-- not as /ad hoc/ as it may appear at first glance. However, because we
-- wouldn't have interesting instance without it, we restrict @g@ to be an
-- applicative functor. There does not seem to be a need for @f@ to be
-- applicative as well, therefore we depart from usual mathematical practice and
-- only restrict @g@.
class Functor1 h => Strong1 h where
  strength1
    :: (Functor f, Applicative g, Functor i)
    => h f (g a) -> (forall b. f (g b) -> i b) -> h i a

  default strength1
    :: ( Generic1 (h f), Generic1 (h i), GStrong1 (Rep1 (h f)) (Rep1 (h i)) f  g i
       , Functor f, Applicative g, Functor i )
    => h f (g a) -> (forall b. f (g b) -> i b) -> h i a
  strength1 a alpha = to1 $ gstrength1 (from1 a) alpha

-- TODO: doc
data Either2
  (h :: (* -> *) -> * -> *) (j :: (* -> *) -> * -> *) (f :: * -> *) (a :: *)
  = Left2 (h f a)
  | Right2  (j f a)
  deriving (Generic1, Functor, Eq)

instance (Functor1 h, Functor1 j) => Functor1 (Either2 h j)

instance (Strong1 h, Strong1 j) => Strong1 (Either2 h j) where

-- TODO: doc, remark that, from an AST point of view, this is the prototypical
-- new thing. Show that this is not strong (/e.g./ Var Identity (Const ()) Void).
data Var (f :: * -> *) (a :: *) = Var a
  deriving (Generic1, Functor, Eq)

instance Functor1 Var where

-- $pfunctor1

class
    (forall f p. (forall q. Functor (f q)) => Functor (h f p))
    => PFunctor1 (h :: (k -> * -> *) -> k -> * -> *)
  where
    pfmap1
      :: (forall p. Functor (f p), forall q. Functor (g q))
      => (forall q. f q ~> g q) -> h f p ~> h g p

    -- default fmap1
    --   :: ( Generic1 (h f), Generic1 (h g), GFunctor1 (Rep1 (h f)) (Rep1 (h g)) f g
    --      , Functor f, Functor g )
    --   => (f ~> g) -> h f ~> h g
    -- fmap1 alpha = to1 . gfmap1 alpha . from1

-- $fixed-points

-- $mu

-- TODO: doc, relation between this and non-uniform data type (example:
-- perfectly balanced binary tree @data Tree a = Leaf a | Node (Tree (a, a)))@)
newtype Mu (h :: (* -> *) -> * -> *) (a :: *) = Roll { unroll :: h (Mu h) a }

deriving instance (Eq a, forall b f. (Eq b, forall c. Eq c => Eq (f c)) => Eq (h f b)) => Eq (Mu h a)

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
cata1 :: (Functor1 h, Functor f) => (h f ~> f) -> Mu h ~> f
cata1 alg (Roll t) = alg $ fmap1 (cata1 alg) t

-- ** Mutually recursive fixed point
-- $mmu

newtype MMu (h :: (k -> * -> *) -> k -> * -> *) (p :: k) (a :: *)
  = MRoll {unmroll :: h (MMu h) p a }

instance PFunctor1 h => Functor (MMu h p) where
  fmap f (MRoll t) = MRoll $ fmap f t

pcata1
  :: (PFunctor1 h, forall q. Functor (f q))
  => (forall q. h f q ~> f q) -> MMu h p ~> f p
pcata1 alg (MRoll t) = alg $ pfmap1 (pcata1 alg) t

-- $generic-deriving

-- $deriving-functor1

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

instance {-# INCOHERENT #-} (Functor1 h, Functor f, Functor g)
    => GFunctor1 (Rec1 (h f)) (Rec1 (h g)) f g
  where
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

-- For some reason the left-hand side of @:.:@ is not parsed as a 'Rep1', so we
-- need this instance when we recurse on the left-hand side of @:.:@.
instance {-# INCOHERENT #-} GFunctor1 f g f g where
  gfmap1 alpha a = alpha a

-- $deriving-strong1

-- TODO: explain what needs to be done to derive things

-- | A class for deriving 'Strong1' instances generic types. See the
-- documentation of 'Functor1' for details on the encoding.  You should read @h@
-- and @j@ below as being @h' f@ and @h' i@, respectively.
class GStrong1 (h :: * -> *) (j :: * -> *) (f :: * -> *) (g :: * -> *) (i :: * -> *) where
  gstrength1 :: h (g a) -> (forall b. f (g b) -> i b) -> j a

-- TODO: At the moment, I can't find other useful instances for 'Rec1'. Either I
-- will find more, or I will need to give a short explanation as a Haddock
-- comment.
instance {-# INCOHERENT #-} (Strong1 h, Functor f, Applicative g, Functor i)
    => GStrong1 (Rec1 (h f)) (Rec1 (h i)) f g i
  where
    gstrength1 (Rec1 a) alpha = Rec1 $ strength1 a alpha

instance {-# INCOHERENT #-} GStrong1 (Rec1 f) (Rec1 i) f g i
  where
    gstrength1 (Rec1 a) alpha = Rec1 $ alpha a

instance GStrong1 V1 V1 f g i where
  gstrength1 v _ = case v of {}

instance GStrong1 U1 U1 f g i where
  gstrength1 U1 _ = U1

-- TODO: Turn this into Haddock documentation
-- There is no:
--
-- > instance GStrong1 Par1 Par1 f g i where
--
-- As it would require a function @g a -> a@. Such as if @g@ is a comonad. But
-- 'Strong1' is abstract over @g@, so this would not be useful.

instance GStrong1 (K1 m c) (K1 m c) g f i where
  gstrength1 (K1 c) _ = K1 c

instance GStrong1 h j f g i => GStrong1 (M1 m c h) (M1 m c j) f g i where
  gstrength1 (M1 a) alpha = M1 $ gstrength1 a alpha

instance
    (GStrong1 h1 j1 f g i, GStrong1 h2 j2 f g i)
    => GStrong1 (h1 :+: h2) (j1 :+: j2) f g i
  where
    gstrength1 (L1 a) alpha  = L1 $ gstrength1 a alpha
    gstrength1 (R1 a) alpha = R1 $ gstrength1 a alpha

instance
    (GStrong1 h1 j1 f g i, GStrong1 h2 j2 f g i)
    => GStrong1 (h1 :*: h2) (j1 :*: j2) f g i
  where
    gstrength1 (a :*: b) alpha = gstrength1 a alpha :*: gstrength1 b alpha

instance
    (GStrong1 h1 j1 f g i, Traversable t, Functor h1, Traversable t, Applicative g)
    => GStrong1 (h1 :.: t) (j1 :.: t) f g i
  where
    gstrength1 (Comp1 a) alpha = Comp1 $ gstrength1 (fmap sequenceA a) alpha

-- For some reason the left-hand side of @:.:@ is not parsed as a 'Rep1', so we
-- need this instance when we recurse on the left-hand side of @:.:@.
instance {-# INCOHERENT #-} GStrong1 f i f g i
  where
    gstrength1 a alpha = alpha a


--  LocalWords:  monads monad functorial functor functors endofunctors monoid
--  LocalWords:  comonad applicative
