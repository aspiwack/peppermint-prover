{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE OverloadedLists #-}

module Data.Generics.DeBruijn where

import Prelude hiding (Traversable(..), drop, take)
import Control.Lens hiding (Context)
import GHC.Exts (IsList(..))
import GHC.Stack
import GHC.TypeLits
import Data.Proxy
import Data.Coerce
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Generics.Product as Generics

-- Historical note: Scrap Your Boilerplate paper: 2003. I know that this style
-- of programming was there in Coq in Feb 2005 when I first used the code
-- base. I don't know how long it had been there. Will investigate.
-- A good explanation of this style in the context of de Bruijn indices can be
-- found at https://www.twanvl.nl/blog/haskell/traversing-syntax-trees

-- Generalise this way? https://gist.github.com/ekmett/80ea0a22c99577013de8cb6cfe020971

-- TODO: in 9.0: add type signature
newtype Bind (n :: Nat) a = Bind a

-- TODO: should `Bind` have an API similar to the `Syntax` API? It can't quite
-- share the exact same API because it is not recursive. A traversable API? It
-- could work, but it 's a bit of a pain. Due to the fact that there are several
-- Notion of traversable depending on whether it's at the kind `g -> *` or `*`,
-- and the amusing funny-fun bureaucracy of managing the kind of context that we
-- need.
--
-- Having a notion of Traversable is rather interesting though: it let's me, for
-- instance, define `Syntax` for a fixed point operator. Much in the style of
-- http://www.cubix-framework.com/ . Edward Kmett's gist, above, gives an
-- approach to be sort-generic for this sort of things, but as it stands, it's
-- rather messy, and I don't want to go in that direction.
bind :: forall f ctx a b n. (KnownNat n, Functor f, Num ctx) => (ctx -> a -> f b) -> ctx -> Bind n a -> f (Bind n b)
bind f lvl (Bind x) = Bind <$> f (lvl + n) x
  where
    n :: ctx
    n = fromIntegral $ natVal (Proxy @n)

-- TODO: in 9.0: add type signature
--
-- TODO: make an example that would work with this library, with `Expr Tm`
-- instead of `Tm`, I suppose.
-- | This variant of 'Bind' lets you bind variables when you have several kinds of binders.
--
-- It uses the field names discovered by a 'Generic' instance.
--
-- > data Vars = Vars
-- >   { tyVar :: Int
-- >   , tmVar :: Int }
-- >   deriving (Generic)
-- >
-- > data Tm
-- >   = TyVar Int
-- >   | TmVar Int
-- >   | TyLam (Binds "tyVar" 1 Tm)
-- >   | Lam (Binds "tmVar" 1 Tm)
-- >   | TyApp Tm Ty
-- >   | App Tm Tm
newtype Binds (s :: Symbol) (n :: Nat) a = Binds a

binds :: forall f ctx a b s n i. (KnownNat n, Functor f, Generics.HasField' s ctx i, Num i) => (ctx -> a -> f b) -> ctx -> Binds s n a -> f (Binds s n b)
binds f lvls (Binds x) = Binds <$> f (over (Generics.field' @s) (+n) lvls) x
  where
    n :: i
    n = fromIntegral $ natVal (Proxy @n)

-- TODO: in 9.0: add type signature
class Syntax (a :: g -> *) where
  type Context a

  traverseSubs :: Applicative f => (forall e'. Context a -> a e' -> f (a e')) -> Context a -> a e -> f (a e)

  -- TODO: throughout: I don't like that the `a` (type) argument happens before
  -- the `f` argument. I use it everywhere for consistency, though. Two choices:
  -- either I can use type signatures to reorder the argument of `traverseSubs`,
  -- despite it being a type class method.  (it was discussed at some point I
  -- don't know if it ended up working out), or I can simply duplicate
  -- `traverseSubs`: once as the method, to define the type class, and once as a
  -- function, to have the convenient (type) argument order.
  --
  -- TODO: move into the type class in case one needs to override it to avoid the
  -- error.
  traverseSubs_ :: (Syntax a, Applicative f) => (forall e'. a e' -> f (a e')) -> a e -> f (a e)
  traverseSubs_ onSubs = traverseSubs (const onSubs) arbitrary
    where
      arbitrary = error "traversal accesses context directly, you may want to override the default traverseSubs_ implementation"

-- TODO: can I make the `g` parameter inferred, so that the first `_` can be
-- removed? In 9.0. In a delightful twist of fate, `traverseSubs_`'s kind
-- argument is, indeed, inferred. Better make that explicit though.
--
-- Note: I have to go through all of these 𝜂-expansion, because `coerce` cannot
-- see through the `forall` quantifications: it seems to generate an `e1 ~R e2`
-- constraint to instantiate (pairs of) foralls, but what I need is `e1 ~N e2`,
-- and since there is no backtracking, there is no one best choice here,
-- probably. I can't produce an example, out of the top of my head, why, in some
-- cases, `~R` would be necessary, but it can surely show up (probably by
-- chaining foralls).
mapSubs :: forall a e. (Syntax a) => (forall e'. Context a -> a e' -> a e') -> Context a -> a e -> a e
mapSubs = coerce $ traverseSubs @_ @a @Identity @e

mapSubs_ :: forall a e. (Syntax a) => (forall e'. a e' -> a e') -> a e -> a e
mapSubs_ = coerce $ traverseSubs_ @_ @a @Identity @e

foldSubs :: forall a r e. (Syntax a, Monoid r) => (forall e'. Context a -> a e' -> r) -> Context a -> a e -> r
foldSubs = coerce $ traverseSubs @_ @a @(Const r) @e

foldSubs_ :: forall a r e. (Syntax a, Monoid r) => (forall e'. a e' -> r) -> a e -> r
foldSubs_ = coerce $ traverseSubs_ @_ @a @(Const r) @e

-- TODO: make abstract
--
-- TODO: semantic as an infinite list.
--
-- TODO: provide a mechanism to cut substitution-by-identity off
--
-- TODO: provide a mechanism to read lists as a substitution (probably
-- `IsList`). I'd like it to be compatible with infinite lists, `Seq`'s
-- `fromList` only reads finite lists. Maybe we want to chunk the list in
-- exponentially increasing sized chunks. It should provide access to
-- `Apply`. Do I want another access? I'll see in practice, otherwise `Apply` is
-- always followed by the identity (or another `Apply` for the sake of
-- infinitude). If I don't need an access to `Apply`, then `Seq` is not the best
-- representation: I should choose `Array` instead (I only use length and lookup
-- so far; I initially picked `Seq` because it also has efficient
-- concatenation; Note, though: (efficient) composition uses drop).
--
-- TODO: Generalise away from `Int`?
--
-- TODO: better name to `Apply`/`mkApply`, it clashes with `apply`
--
-- Note: constructors do not exactly correspond to the public interface. That's
-- because this choice of constructors work better in 'comp'.
data Subst a
  = Id
    -- ^ identity substitution @⟦Id⟧ = [var 0 ..]@. Used by 'lifting'.
  | Lift Int (Subst a)
    -- ^ @'Lift' k s@ adds @k@ to each de Bruijn index in s: @⟦'Lift' k s⟧ = map (lift k) ⟦s⟧@. Used by 'lifting' and 'shifting'.
  | Rng Int (Subst a)
    -- ^ @⟦'Rng' p s⟧ = [var 0, …, var (p-1)] ++ s@.
  | Apply (Seq a) (Subst a)
    -- ^ @⟦'Apply' xs s⟧ = xs ++ s@

mkLift :: HasCallStack => Int -> Subst a -> Subst a
mkLift k _ | k < 0 = error "Db.mkLift: can't lift by a negative amount"
mkLift 0 s = s
mkLift k (Lift p s) = Lift (k+p) s
mkLift k s = Lift k s

mkRng :: HasCallStack => Int -> Subst a -> Subst a
mkRng k _ | k < 0 = error "Db.mkRng: can't make a negative-size range"
mkRng k (Lift k' (Rng p s)) | k == k' = Rng (k+p) (mkLift k s)
mkRng k s = Rng k s

mkApply :: Seq a -> Subst a -> Subst a
mkApply [] s = s
mkApply xs s = Apply xs s

instance Substitutable a => IsList (Subst a) where
  type Item (Subst a) = a

  fromList [] = Id
  fromList xs = Apply (fromList segment) (fromList rest)
    where
      (segment, rest) = splitAt 1024 xs

  toList Id = map var [0 ..]
  toList (Lift k s) = map (lift k) $ toList s
  toList (Rng p s) = map var [0 .. p-1] ++ toList s
  toList (Apply xs s) = toList xs ++ toList s

lifting :: HasCallStack => Int -> Subst a
lifting k = mkLift k Id

shifting :: HasCallStack => Int -> Subst a -> Subst a
shifting p s = mkRng p s

class Substitutable a where
  var :: Int -> a
  subst :: Subst a -> a -> a
  lift :: Int -> a -> a
  lift k = subst (Lift k Id)

apply :: Substitutable a => Int -> Subst a -> a
apply = go 0
  where
    go l i Id = var (i+l)
    go l i (Lift k s) = go (l+k) i s
    go l i (Rng p s)
      | i < p = var i
      | otherwise = go l (i-p) s
    go l i (Apply xs s)
      | Just x <- Seq.lookup i xs = lift l x
      | otherwise = go l (i-Seq.length xs) s

-- | 'Prelude.drop' in the list semantics.
drop :: (HasCallStack, Substitutable a) => Int -> Subst a -> Subst a
drop n Id = mkLift n Id
drop n (Lift k s) = Lift k (drop n s)
drop n (Rng p s)
  | n <= p = mkApply (fmap var [n..p]) s
  | otherwise = drop (n-p) s
drop n (Apply xs s)
  | n <= p = mkApply (Seq.drop n xs) s
  | otherwise = drop (n-p) s
  where
    p = Seq.length xs

-- | 'Prelude.take', but since I don't have a dedicated finite substitution
-- type, I use `Subst a -> Subst a` for this role.
take :: (HasCallStack, Substitutable a) => Int -> Subst a -> Subst a -> Subst a
take n Id = mkRng n
take n (Lift k s) = mkLift k . take n s
take n (Rng p s)
  | n <= p = mkRng n
  | otherwise = mkRng p . take (n-p) s
take n (Apply xs s)
  | n <= p = mkApply (Seq.take n xs)
  | otherwise = mkApply xs . take (n-p) s
  where
    p = Seq.length xs

-- QUESTION: can I generalise? In general, I have an `a`, a substitution of `b`
-- and I produce a `c`, so that composition would be `Subst a -> Subst b ->
-- Subst c`. This is not an entirely idle thought either, since if I have
-- substitutions of types and of terms (say in a System-F-like language), then I
-- will want to compose both kind of substitutions in an explicit substitution
-- setting. But it does make inference wonky as I very much do not want `a` to
-- determine `b` or `b` to determine `a` (It's alright, however, for both of
-- them to jointly determine `c`): I want to apply term and type substitutions
-- to terms, and I want to apply type substitutions to both types and terms. It
-- may be because of similar reasons that Coq has a `Lift` type in addition to
-- the `Subst` type (which is essentially identical except for the `Apply` bit).
--
-- REMARK: it may help with the above to split `Substitutable` into a `Liftable`
-- class with `var` and `lift`, and a keep `subst` only in `Substitutable`. It
-- would avoid a lot of ambiguous functions, but, on the other hand, we lose the
-- default implementation of `lift` (which would become ambiguous).
--
-- MMM: I'm realising now that there is something wrong with even `Liftable`: if
-- we have several kinds of variables, we want to lift a particular kind. Maybe
-- we want to add a symbol just like in `Binds`. Probably should be a different
-- type class to avoid complicating the standard case.
comp :: Substitutable a => Subst a -> Subst a -> Subst a
comp Id s2 = s2
comp (Lift k s1) s2 = comp s1 (drop k s2)
comp (Rng p s1) s2 = take p s2 (comp s1 s2)
comp (Apply xs s1) s2 = Apply (fmap (subst s2) xs) (comp s1 s2)
