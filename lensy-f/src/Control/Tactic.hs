{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Control.Tactic where

import Data.Void
import Data.Functor.Compose
import Control.Applicative
import Data.Functor.Identity
import Data.Array

newtype Tactic goal thm (m :: * -> *)
  = Mk { eval :: forall f. Applicative f => (goal -> Compose m f thm) -> goal -> Compose m f thm }

id :: Tactic goal thm m
id = Mk Prelude.id

thn :: Tactic goal thm m -> Tactic goal thm m -> Tactic goal thm m
thn a b = Mk $ eval a . eval b

fail :: Alternative m => Tactic goal thm m
fail = Mk $ \_k _goal -> empty

or :: Alternative m => Tactic goal thm m -> Tactic goal thm m -> Tactic goal thm m
or a b = Mk $ \k goal -> eval a k goal <|> eval b k goal

dispatch :: Monad m => Tactic goal thm m -> [Tactic goal thm m] -> Tactic goal thm m
dispatch a bs = Mk $ \k goal -> Compose $ do
  reified <- getCompose $ eval a (Compose . return . batch) goal
  getCompose $ runZipBatch (map (\b -> eval b k) bs) reified
  -- However convoluted this definition may look, this is nothing compared to
  -- the definition in the standard presentation of Milner's tactics.

proveWith :: forall goal thm m. Functor m => (goal -> m Void) -> Tactic goal thm m -> goal -> m thm
proveWith err tac goal = runIdentity <$> getCompose (go goal)
  where
    go :: goal -> Compose m Identity thm
    go = eval tac @Identity (Compose . vacuous . err)

--------------------------------------------------------------------------------
-- Utils

-- Got `Batch` from Bhavik Mehta's https://github.com/tweag/linear-base/pull/79
-- . It is the same type as `Ap (Mono x y)` in
-- https://elvishjerricco.github.io/2017/03/23/applicative-sorting.html . I
-- don't know if it has more history.

data Batch a b c = Done c | More a (Batch a b (b -> c))

instance Functor (Batch a b) where
  fmap f (Done c)   = Done (f c)
  fmap f (More x l) = More x ((f.) <$> l)

instance Applicative (Batch a b) where
  pure = Done
  Done f <*> l' = fmap f l'
  More x l <*> l' = More x (flip <$> l <*> l')

batch :: a -> Batch a b b
batch x = More x (Done Prelude.id)

runZipBatch :: Applicative f => [a -> f b] -> Batch a b c -> f c
runZipBatch [] (Done c) = pure c
runZipBatch (f:fs) (More x l) = runZipBatch fs l <*> f x
runZipBatch _ _ = error "Incorrect number of goals"
  -- We make no attempt at recovering from goal number mismatches. These are
  -- considered fatal errors.
