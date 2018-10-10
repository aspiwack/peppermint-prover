{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
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

import Control.Monad (guard)
import Data.Binder.Unfix
import Data.Void
import GHC.Generics
import Prelude hiding (abs)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

---------------------
-- Pure λ-calculus --
---------------------

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

-----------------------------
-- Simply typed λ-calculus --
-----------------------------

data Type
  = Base
  | Type :-> Type
  deriving (Eq, Show)
-- TODO: make (:->) associate to the right

data SLamF (f :: * -> *) (a :: *)
  = SAbs_ Type (f (Maybe a))
  | SApp_ (f a) (f a)
  deriving (Generic1, Functor, Functor1, Strong1)

type SLamF' = Var `Either2` SLamF
type SLam a = Mu SLamF' a

{-# COMPLETE SAbs, (::@), SV #-}

pattern SAbs :: Type -> f (Maybe a) -> SLamF' f a
pattern SAbs tau f = Right2 (SAbs_ tau f)
pattern SAbs' tau f = Roll (SAbs tau f)

infixl 9 ::@
pattern (::@) :: f a -> f a -> SLamF' f a
pattern t ::@ u = Right2 (t `SApp_` u)
pattern t ::@: u = Roll (t ::@ u)

pattern SV :: a -> SLamF' f a
pattern SV x = Left2 (Var x)
pattern SV' x = Roll (SV x)

type Typing = Assigned (Maybe Type) Type

typing :: SLamF' Typing ~> Typing
typing (SV x) = Assigned $ \env ->
  return $ env x
typing (SAbs tau f) = Assigned $ \env -> do
  res <- runAssigned f (env <+> tau)
  return $ tau :-> res
typing (u ::@ v) = Assigned $ \env -> do
  tau :-> res <- runAssigned u env
  tau' <- runAssigned v env
  guard (tau == tau')
  return res

typeOf :: SLam a -> (a -> Type) -> Maybe Type
typeOf u = runAssigned $ cata1 typing u

main :: IO ()
main = hspec $ do
  describe "λ-calculus substitution" $ do
    prop "Church numeral addition is correct" $
      \(NonNegative n) (NonNegative p) ->
        eval (churchNum n ^+ churchNum p) === churchNum @Void (n+p)
  describe "Simply typed λ-calculus" $ do
    it "type-checks identity" $ do
      typeOf (SAbs' Base $ SV' Nothing) absurd `shouldBe` Just (Base :-> Base)
    it "doesn't type-check self-application" $ do
      typeOf (SAbs' (Base :-> Base) $ SV' Nothing ::@: SV' Nothing) absurd `shouldBe` Nothing
    it "type-checks ($)" $ do
      typeOf (SAbs' (Base :-> Base) $ SAbs' Base $ SV' (Just Nothing) ::@: SV' Nothing) absurd `shouldBe` Just ((Base :-> Base) :-> (Base :-> Base))
    it "type-checks K" $ do
      typeOf (SAbs' Base $ SAbs' Base $ SV' (Just Nothing)) absurd `shouldBe` Just (Base :-> (Base :-> Base))
