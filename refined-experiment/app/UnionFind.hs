{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}

module UnionFind
  ( UnionFind
  , Point
  , empty
  , pointOf
  , repr
  , union
  , equivalent
  -- * Capability
  , HasUnionFind
  -- * Union-find monad
  , UnionFindM
  , run
  , exec
  , eval
  )
where

import Capability.Sink
import Capability.Source
import Capability.State
import qualified Control.Monad.State as State
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- This implementation is very much inspired by and adapted from
-- https://github.com/nominolo/union-find/blob/master/src/Data/UnionFind/IntMap.hs

data UnionFind a = MkUnionFind
  { next :: Int
  , points :: Map a Int
  , classes :: IntMap (Link a)
  }

data Link a
    = Info {-# UNPACK #-} !Int a
      -- ^ This is the descriptive element of the equivalence class
      -- and its rank.
    | Link {-# UNPACK #-} !Int
      -- ^ Pointer to some other element of the equivalence class.
     deriving Show

newtype Point a = Point Int
  deriving (Eq, Ord)

empty :: UnionFind a
empty = MkUnionFind
  { next = 0
  , points = Map.empty
  , classes = IntMap.empty
  }

-- XXX: it would probably be smarter be abstract with respect to the tag
type HasUnionFind a = HasState "UnionFind" (UnionFind a)

pointOf :: (HasUnionFind a m, Ord a) => a -> m (Point a)
pointOf a = do
  uf <- get @"UnionFind"
  case Map.lookup a (points uf) of
    Just p -> return $ Point p
    Nothing -> do
      let p = next uf
      put @"UnionFind" $ MkUnionFind { next = p+1, points = Map.insert a p (points uf), classes = IntMap.insert p (Info 0 a) (classes uf) }
      return $ Point p

repr :: HasUnionFind a m => Point a -> m (Point a)
repr p = reprInfoM p (\n _rank _a -> return $ Point n)

reprInfoM :: HasUnionFind a m => Point a -> (Int -> Int -> a -> m r) -> m r
reprInfoM (Point n) k = do
  uf <- get @"UnionFind"
  go (classes uf) n
  where
    go cls !i =
      case cls IntMap.! i of
        Link i' -> go cls i'
        Info r a -> k i r a

union :: HasUnionFind a m => Point a -> Point a -> m ()
union p1 p2 =
  reprInfoM p1 $ \i1 r1 _a1 ->
  reprInfoM p2 $ \i2 r2 a2 -> do
    uf <- get @"UnionFind"
    if i1 == i2 then return () else
      case r1 `compare` r2 of
        LT ->
          -- No rank or descriptor update necessary
          let !classes1 = IntMap.insert i1 (Link i2) (classes uf) in
          put @"UnionFind" $ uf { classes = classes1 }
        EQ ->
          let
            !classes1 = IntMap.insert i1 (Link i2) (classes uf)
            !classes2 = IntMap.insert i2 (Info (r2 + 1) a2) classes1
          in
          put @"UnionFind" $ uf { classes = classes2 }
        GT ->
          let
            !classes1 = IntMap.insert i1 (Info r2 a2) (classes uf)
            !classes2 = IntMap.insert i2 (Link i1) classes1
          in
          put @"UnionFind" $ uf { classes = classes2 }

equivalent :: HasUnionFind a m => Point a -> Point a -> m Bool
equivalent p1 p2 =
  reprInfoM p1 $ \i1 _ _ ->
  reprInfoM p2 $ \i2 _ _ ->
  return $ i1 == i2

------------------------------------------------------------------------------
-- Concrete monad implementation

newtype UnionFindM a r = UnionFindM (State.State (UnionFind a) r)
  deriving newtype (Functor, Applicative, Monad)
  deriving (HasSource "UnionFind" (UnionFind a), HasSink "UnionFind" (UnionFind a), HasUnionFind a) via (MonadState (State.State (UnionFind a)))

run :: UnionFind a -> UnionFindM a r -> (r, UnionFind a)
run uf (UnionFindM act) = State.runState act uf

exec :: UnionFind a -> UnionFindM a () -> UnionFind a
exec uf act = snd $ run uf act

eval :: UnionFind a -> UnionFindM a r -> r
eval uf act = fst $ run uf act
