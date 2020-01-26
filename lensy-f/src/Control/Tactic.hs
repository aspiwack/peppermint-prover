{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | This module defines a generic type of tactics in the sense of proof
-- assistants. This library is well-suited to give the backbone of a tactic
-- system where you have a type of goals, proof obligation, or generally
-- something which needs to be /solved/; and you have a type of theorem, or
-- solution.
--
-- The type @'Tactic' m goal thm@ then models proof instructions of the form: if
-- you can resolve this new collection of sub-goals, then I can build a solution
-- for the current goal. Where goals are of type @goal@ and solutions of type
-- @thm@. The remaining parameter @m@ represents the kind of effects that the
-- tactics are permitted to perform (see, in particular 'proveWith'). It will
-- typically be a 'MonadPlus', even though the tactic combinators in this module
-- require weaker properties.
--
-- In practice you may want the monad @m@ to be very rich: you may want to
-- support logging, caching, etc… But the simplest examples of choice of @m@ are
-- 'Maybe' and '[]'. With 'Maybe', the semantics of @a `or` b@ is: if @a@
-- succeeds then @a@ else @b@. Using '[]' adds backtracking (which can be
-- formalised as the fact that @(a `or` b) `thn` c = (a `thn c) `or` (b `thn`
-- c)`.)
--
-- == Applicability and limitations
--
-- The main limitation of tactics such as here is that they can only consider
-- one goal at a time. If you need tactics which consider several goals at a
-- time to progress, these tactics won't do. At least not easily.
--
-- Another case where this is not particularly well-suited is if you have a
-- native notion of theorems-with-unproved-holes. Indeed, tactics can be seen as
-- a way to use functions to add holes to theorems. If you already have holes,
-- your tactics should probably be implemented in terms of these holes.
--
-- Both of these points are discussed, in the context of the Coq proof
-- assistant, in Chapter 4 of
-- <http://assert-false.net/arnaud/papers/thesis.spiwack.pdf my thesis>.
--
-- == Historical notes
--
-- Tactics were introduced in the original paper about the ML language, and are
-- generally attributed to Robin Milner. Tactics were defined as
--
-- @
-- type tactic = goal -> (goal list * (thm list -> thm))
-- @
--
-- where both lists are understood to have the same length. Tactics were used to
-- write proofs in the LCF proof assistant (ML was created to be the
-- Meta-Language of LCF).
--
-- Variants of this type, generally without lists appear in the literature, with
-- reference to Milner tactics. For example in
-- <https://link.springer.com/chapter/10.1007/978-3-642-37036-6_2 the compiler
-- forest> compiler passes are defined as
--
-- @
-- source→(source′×(target′→target))
-- @
--
-- With explicit reference to Milner's tactics.
--
-- A similar type also appears in Valeria de Paiva's categorical analysis of
-- Gödel's Dialectica interpretation
-- <https://github.com/vcvpaiva/DialecticaCategories>. I don't know if de Paiva
-- was aware of the connection at the time, but I've seen reference to her work
-- in comparison with Milner tactics.
--
-- The lenses appeared as a completely parallel and, as far as I know,
-- independent work. I believe lens to have been introduced in the context of
-- the <https://www.seas.upenn.edu/~harmony/ Boomerang> language. There, they
-- were given as a pair of a getter and a setter
--
-- @
-- (a -> b, a -> b -> a)
-- @
--
-- In the early version of the lens library for Haskell, Edward Kmett had
-- factored the first argument for efficiency:
--
-- @
-- a -> (a, b -> a)
-- @
--
-- It's obvious when everything is put on the same page, but I don't think
-- anybody realised that these types were all the same. Not to my knowledge,
-- anyway.
--
-- What's of interest though, is that the van Laarhoven presentation of lenses
-- admits a version which is precisely the same as a lens to a list of position:
-- traversals. What's nice about traversals is that we don't have to deal with
-- two list which must be the same length, but can't be proved to be so by the
-- type system. This, together with the already simplified composition of the
-- van Laarhoven presentation compared to @a->(b,b->a)@, let me write a much
-- simpler library.
--
-- There is a remaining lie which needs ironing out: Milner's tactics can
-- fail. Traversal can have no position to fill, but this corresponds to success
-- in Milner's tactic. So we need a little extra oomph. Which is achieve by
-- adding an appropriate monad in the right place in the definition. While we
-- are at it, I made the monad abstract, so the library can be multi-purpose.

module Control.Tactic where

import Control.Applicative
import Control.Monad
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Void
import Data.Vector (Vector)
import qualified Data.Vector as Vector

-- | Use 'Mk' to write new tactics. You probably never need to use 'eval'
-- yourself, unless you want to extend the combinator library.
--
-- The type of tactics uses @'Compose' m f thm@ rather than @m f thm@ because
-- @'Compose' m f@ is an applicative, therefore tactics can be built with the
-- applicative syntax. /e.g./
--
-- @
-- conj_tac = Mk go
--   where
--     go k (Conj l r) = prove_conj <$> k l <*> k r
--     go _ _ = empty
-- @
newtype Tactic goal thm (m :: * -> *)
  = Mk { eval :: forall f. Applicative f => (goal -> Compose m f thm) -> goal -> Compose m f thm }

-- | The identity tactic. It produce one subgoal: the original goal. Neutral
-- element of 'thn'.
id :: Tactic goal thm m
id = Mk Prelude.id

-- | @a `thn` b@ applies @b@ on each of the subgoals of @a@.
thn :: Tactic goal thm m -> Tactic goal thm m -> Tactic goal thm m
thn a b = Mk $ eval a . eval b

-- | Raises a failure. Neutral element of `or`.
fail :: Alternative m => Tactic goal thm m
fail = Mk $ \_k _goal -> empty

-- | Catches failures. The precise semantics depends on the monad @m@, @a
or :: MonadPlus m => Tactic goal thm m -> Tactic goal thm m -> Tactic goal thm m
or a b = Mk $ \k goal -> Compose $ do
  reified <- reify a goal <|> reify b goal
  getCompose $ runBatch k reified
  -- This is a bit gross, compared to the classical presentation. We do have to
  -- cut the computation off to check for errors before calling the continuation
  -- on the subgoals. Ah, well.

-- | @a `dispatch` [b1,…,bn]@ assumes that @a@ produces @n@ subgoals, in which
-- case, it applies @b1@ to the first goal, @b2@ to the second, …, @bn@ to the
-- nth goal. If @a@ produces another number of goals, then it fails with a fatal
-- error (which can't be caught by `or`).
dispatch :: Monad m => Tactic goal thm m -> [Tactic goal thm m] -> Tactic goal thm m
dispatch a bs = Mk $ \k goal -> Compose $ do
  reified <- reify a goal
  getCompose $ runZipBatch (map (\b -> eval b k) bs) reified
  -- However convoluted this definition may look, this is nothing compared to
  -- the definition in the standard presentation of Milner's tactics.

-- | @proveWith err tac goal@ attempts to solve @goal@ with the tactic @tac@. If
-- some goals remain unsolved after applying @tac@, then the remaining goals are
-- traversed with @err@ to produce the error message of your choosing.
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

-- Invariant :: lengthBatch (Ap n l r) = lengthBatch l + lengthBatch r = n
data Batch a b c where
  Pure :: c -> Batch a b c
  Single :: a -> (b -> c) -> Batch a b c
  Ap_ :: !Int -> (Batch a b (d->c)) -> (Batch a b d) -> Batch a b c

pattern Ap :: Batch a b (d -> c) -> Batch a b d -> Batch a b c
pattern Ap l r <- Ap_ _ l r
  where
    Ap l r = l `seq` r `seq` Ap_ (lengthBatch l + lengthBatch r) l r
{-# COMPLETE Pure,Single,Ap #-}

instance Functor (Batch a b) where
  fmap f = (pure f <*>)

instance Applicative (Batch a b) where
  pure = Pure
  (<*>) = Ap

lengthBatch :: Batch a b c -> Int
lengthBatch (Pure _) = 0
lengthBatch (Single _ _) = 1
lengthBatch (Ap_ n _ _) = n

batch :: a -> Batch a b b
batch a = Single a Prelude.id

runZipBatch :: forall f a b c. Applicative f => [a -> f b] -> Batch a b c -> f c
runZipBatch fs0 b =
    let fs = Vector.fromList fs0 in
    if Vector.length fs == lengthBatch b then
      go fs b
    else
      error "Incorrect number of goals"
  -- We make no attempt at recovering from goal number mismatches. These are
  -- considered fatal errors.
  where
    -- Invariant: the length of the vector equals the length of the batch.
    go :: forall x. Vector (a -> f b) -> Batch a b x -> f x
    go _ (Pure c) = pure c
    go fs (Single a g) = g <$> Vector.head fs a
      -- Note that `fs`, here, has size 1 because of the length invariant.
    go fs (Ap l r) = go fl l <*> go fr r
      where
        (fl, fr) = Vector.splitAt (lengthBatch l) fs

runBatch :: Applicative f => (a -> f b) -> Batch a b c -> f c
runBatch _ (Pure c) = pure c
runBatch f (Single a g) = g <$> f a
runBatch f (Ap l r) = runBatch f l <*> runBatch f r

-- Cuts off the tactic computation and returns the subgoals.
reify :: Applicative m => Tactic goal thm m -> goal -> m (Batch goal thm thm)
reify a goal = getCompose $ eval a (Compose . pure . batch) goal
