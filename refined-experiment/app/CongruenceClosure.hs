{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module CongruenceClosure
  ( CC
  , LiftRelation(..)
  , Unfix(..)
  , empty
  , add
  , merge
  , equivalent
    -- * Capability
  , HasCC
    -- * Congruence-closure monad
  , CCM
  , run
  , exec
  , eval
  )
where

import Capability.Sink
import Capability.Source
import Capability.State
import qualified Control.Lens as Lens
import Control.Monad
import qualified Control.Monad.State as State
import Data.Generics.Product
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics
import UnionFind (UnionFind, HasUnionFind)
import qualified UnionFind as UnionFind

class (Traversable f, forall a. Ord a => Ord (f a), LiftRelation f) => Unfix t f | t -> f where
  view :: t -> f t

class LiftRelation (b :: * -> *) where
  liftRelation :: Applicative f => (a->c-> f Bool) -> b a -> b c -> f Bool

-- We need a newtype because of the phantom recursivity. This will create a bit
-- of unnecessary boilerplate, but I don't know a way around it.
newtype Shallow f = Shallow { unShallow :: f (UnionFind.Point (Shallow f)) }

-- Spurious `Ord a`, here because of some incompleteness in the higher-order
-- constraint algorithm.
deriving newtype instance (forall a. (Eq a, Ord a) => Eq (f a)) => Eq (Shallow f)
deriving newtype instance (forall a. Ord a => Ord (f a)) => Ord (Shallow f)

data CC f = CC
  { union_find :: UnionFind (Shallow f)
  , super_terms :: Map (UnionFind.Point (Shallow f)) (Set (Shallow f))
  }
  deriving (Generic)

-- Ideally we want a capability which doesn't expose `HasUnionFind` (also with a
-- tag parameter). But this will do for now.
type HasCC f m = (HasState "cc" (CC f) m, HasUnionFind (Shallow f) m)

empty :: CC f
empty = CC
  { union_find = UnionFind.empty
  , super_terms = Map.empty
  }

add :: forall m t f. (Unfix t f, HasCC f m) => t -> m ()
add u0 = void $ go u0
  where
    go :: t -> m (UnionFind.Point (Shallow f))
    go u = do
      shallow_u <- Shallow <$> traverse go (view u)
      r <- UnionFind.pointOf shallow_u
      Lens.forOf_ traverse (unShallow shallow_u) (addAsSuperTerm shallow_u)
      return r

    addAsSuperTerm :: Shallow f -> UnionFind.Point (Shallow f) -> m ()
    addAsSuperTerm u p =
      modify @"cc" $ Lens.over (field @"super_terms") (Map.insertWith Set.union p (Set.singleton u))

equivalent :: forall m t f. (Unfix t f, HasCC f m) => t -> t -> m Bool
equivalent u v = join $
  UnionFind.equivalent <$> pointOf u <*> pointOf v

pointOf :: forall m t f. (Unfix t f, HasCC f m) => t -> m (UnionFind.Point (Shallow f))
pointOf u = do
  shallow_u <- traverse pointOf (view u)
  UnionFind.pointOf (Shallow shallow_u)

merge :: forall m t f. (Unfix t f, HasCC f m) => t -> t -> m ()
merge u v = join $
  merge' <$> pointOf u <*> pointOf v

merge' :: forall m f. (HasCC f m, forall a. Ord a => Ord (f a), LiftRelation f) => UnionFind.Point (Shallow f) -> UnionFind.Point (Shallow f) -> m ()
merge' u v = do
    whenM (not <$> UnionFind.equivalent u v) $ do
      u_repr0 <- UnionFind.repr u
      v_repr0 <- UnionFind.repr v
      UnionFind.union u v
      cc <- get @"cc"
      let
        u_sups = Map.findWithDefault Set.empty u_repr0 (super_terms cc)
        v_sups = Map.findWithDefault Set.empty v_repr0 (super_terms cc)
        uv_sups = u_sups `Set.union` v_sups
      u_repr1 <- UnionFind.repr u
      modify @"cc" $ Lens.over (field @"super_terms") (Map.insertWith Set.union u_repr1 uv_sups . Map.delete u_repr0 . Map.delete v_repr0)
      forM_ u_sups $ \u' ->
        forM_ v_sups $ \v' -> do
          whenM (congruent u' v') $ join $
            merge' <$> UnionFind.pointOf u' <*> UnionFind.pointOf v'

whenM :: Monad m => m Bool -> m () -> m ()
whenM mb act = do
  b <- mb
  when b act

congruent :: forall m f. (LiftRelation f, HasCC f m) => Shallow f -> Shallow f -> m Bool
congruent (Shallow u) (Shallow v) = liftRelation UnionFind.equivalent u v

newtype CCM f a = CCM (State.State (CC f) a)
  deriving newtype (Functor, Applicative, Monad)
  deriving (HasSource "cc" (CC f), HasSink "cc" (CC f), HasState "cc" (CC f)) via (MonadState (State.State (CC f)))
  deriving (HasSource "UnionFind" (UnionFind (Shallow f)), HasSink "UnionFind" (UnionFind (Shallow f)), HasUnionFind (Shallow f)) via (Rename "union_find" (Field "union_find" "cc" (CCM f)))

run :: CC f -> CCM f a -> (a, CC f)
run cc (CCM act) = State.runState act cc

exec :: CC f -> CCM f () -> CC f
exec cc act = snd $ run cc act

eval :: CC f -> CCM f a -> a
eval cc act = fst $ run cc act
