{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import Binders
import Data.Void (Void)
import GHC.Generics
import Prelude hiding (abs)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

data LamF (f :: * -> *) (a :: *)
  = Abs_ (f (Maybe a))
  | App_ (f a) (f a)
  deriving (Generic1, Functor)

deriving instance (Eq a, forall b. Eq b => Eq (f b)) => Eq (LamF f a)

instance Functor1 LamF where
instance Strong1 LamF where

type Lam a = Mu (Var `Either2` LamF) a

{-# COMPLETE Abs, (:@), V #-}

pattern Abs :: Lam (Maybe a) -> Lam a
pattern Abs t = Roll (Right2 (Abs_ t))

infixl 9 :@
pattern (:@) :: Lam a -> Lam a -> Lam a
pattern t :@ u = Roll (Right2 (t `App_` u))

pattern V :: a -> Lam a
pattern V x = Roll (Left2 (Var x))

instance Show a => Show (Lam a) where
  show (Abs t) = "λ.("++ show t ++")"
  show (t :@ u) = show t ++ " (" ++ show u ++ ")"
  show (V x) = show x

-- Precondition: only a non-negative integer
churchNum :: Int -> Lam a
churchNum n = Abs $ Abs $ churchNumRec n
  where
    churchNumRec :: Int -> Lam (Maybe (Maybe a))
    churchNumRec 0 = V Nothing
    churchNumRec i = V (Just Nothing) :@ churchNumRec (i-1)

(^+) :: (forall b. Lam b) -> (forall b. Lam b) -> Lam a
n ^+ p = Abs $ Abs $ n :@ V (Just Nothing) :@ (p :@ V (Just Nothing) :@ V Nothing)

eval :: Lam a -> Lam a
eval ((Abs t) :@ u) = eval $
  t >>= \case
    Nothing -> u
    Just a -> V a
eval (V x :@ u) = V x :@ eval u
eval (t :@ u) = eval (eval t :@ u)
eval (Abs t) = Abs $ eval t
eval t = t

main :: IO ()
main = hspec $ do
  describe "λ-calculus substitution" $ do
    prop "Church numeral addition is correct" $
      \(NonNegative n) (NonNegative p) ->
        eval (churchNum n ^+ churchNum p) === churchNum @Void (n+p)
