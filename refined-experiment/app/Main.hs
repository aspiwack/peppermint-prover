{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import qualified CongruenceClosure as CC
import Control.Applicative
import Control.Lens hiding (use)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Control.Tactic (Tactic)
import qualified Control.Tactic as Tactic
import Control.Unification (Unifiable)
import qualified Control.Unification as Unification
import qualified Control.Unification.Ranked.STVar as Unification
import qualified Control.Unification.Types as Unification
import Data.Coerce
import Data.Functor.Compose
import Data.Generics.Labels ()
import Data.Map.Lens
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import qualified Data.Text.Prettyprint.Doc as Pp
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as Pp
import GHC.Generics (Generic)
import GHC.Stack
import GHC.TypeLits
import Language.LBNF.Runtime
import Refined (Ident(..))
import qualified Refined as Concrete

-- Game plan
--
-- + Use refinement types but discharge proof obligation manually
-- + Terms have a unique _intrinsic_ type, which will be a simple type (could be something like a-la-Church F𝜔 in some ideal future)
-- + Terms are assigned a refined type, but the same term may have many such types
-- + Whenever a term is used, proof obligations that it satisfies the refined type has to be proved to talk about the term at all
-- + There is an erasure function from refined types to intrinsic types
-- + Features: subtypes, quotients, uniform universal quantification (existential too?)
-- + Compared to a standard dependent type system
--   * Types are more rigid, since every type erases to a single intrinsic type (for instance we know statically how many arrows a type has).
--   * We don't have to care about proof irrelevance, since proofs are not part of terms, they are really side conditions
--   * Quotients are easy too
--   * We don't have to care about limitation of a conversion function: we only have to discharge equality proofs
--   * Compared to a system like NuPRL, there is a type-checking algorithm, we don't have to prove everything about a type
--   * It's easy to add primitive types (just axiomatise them)
--   * Termination/totality can be proved as a side condition (usual Caveats about absurd hypotheses may apply) (future anyway)
-- + For now, we'll just pretend that every function is total (the intrinsic type is really about partial functions, as usual in programming languages)
-- + The intended language (at the horizon) is inspired by the internal language of Toposes

-- The dependency that you recover is using a forall in the refinements type
-- `∀ n : ℕ. 𝜏` erases `erase 𝜏`.
--
-- You can recover `𝛱n:ℕ.` as `∀ n : ℕ. { p : ℕ | p = n} → ...` (this is the
-- well-established fact that 𝛱 is ∀+singleton types).
--
-- I guess that, what we are losing, compared to CIC, is strong elimination
-- (i.e. the ability to construct a type by matching on a value)

------------------------------------------------------------------------------
-- Abstract syntax

-- REMINDER: Binders are de Bruijn.

-- | An annotation is an accidental part of the syntax, used to give user
-- feedback, but doesn't affect the semantics of the syntax tree it is used
-- on. Therefore, it is considered that all annotations are equal.
newtype Ann a = Ann a

instance Eq (Ann a) where
  _ == _ = True

instance Ord (Ann a) where
  _ `compare` _ = EQ

instance Show a => Show (Ann a) where
  show (Ann a) = show a

data Term
  = Nat Integer
  | Succ
  | NVar Ident
  | Var Int
  | App Term Term
  | PTrue
  | PFalse
  | PEquals Term Term
  | PNot Prop
  | PAnd Prop Prop
  | PImpl Prop Prop
  | PEquiv Prop Prop
  | PForall (Ann Ident) RType Prop
  deriving (Eq, Ord, Show)

type Prop = Term

data IType
  = INat
  | IProp
  | IArrow IType IType
  deriving (Eq)

data RType
  = RNat
  | RProp
  | RSub (Ann Ident) RType Prop
  | RArrow RType RType
  deriving (Eq, Ord, Show)

internTerm' :: Concrete.Term -> Term
internTerm' u = internTerm Map.empty u

internIType' :: Concrete.IType -> IType
internIType' 𝜏 = internIType Map.empty 𝜏

internRType' :: Concrete.RType -> RType
internRType' 𝜏 = internRType Map.empty 𝜏

internProp' :: Concrete.Term -> Prop
internProp' p = internProp Map.empty p

internTerm :: Map Ident Int -> Concrete.Term -> Term
internTerm subst (Concrete.Var x) = case Map.lookup x subst of
  Just i -> Var i
  Nothing -> NVar x
internTerm _ (Concrete.Nat n) = Nat n
internTerm subst (Concrete.App u v) = App (internTerm subst u) (internTerm subst v)
internTerm _ Concrete.Succ = Succ
internTerm _ Concrete.PTrue = PTrue
internTerm _ Concrete.PFalse = PFalse
internTerm subst (Concrete.PEquals u v) = PEquals (internTerm subst u) (internTerm subst v)
internTerm subst (Concrete.PNot p) = PNot (internTerm subst p)
internTerm subst (Concrete.PAnd p q) = PAnd (internTerm subst p) (internTerm subst q)
internTerm subst (Concrete.PImpl p q) = PImpl (internTerm subst p) (internTerm subst q)
internTerm subst (Concrete.PEquiv p q) = PEquiv (internTerm subst p) (internTerm subst q)
internTerm subst (Concrete.PForall x 𝜏 p) =
  PForall (Ann x) (internRType subst 𝜏) (internTerm (addBinder x subst) p)


internIType :: Map Ident Int -> Concrete.IType -> IType
internIType _ Concrete.INat = INat
internIType _ Concrete.IProp = IProp
internIType subst (Concrete.IArrow 𝜏 𝜎) = IArrow (internIType subst 𝜏) (internIType subst 𝜎)

internRType :: Map Ident Int -> Concrete.RType -> RType
internRType _ Concrete.RNat = RNat
internRType _ Concrete.RProp = RProp
internRType subst (Concrete.RArrow 𝜏 𝜎) = RArrow (internRType subst 𝜏) (internRType subst 𝜎)
internRType subst (Concrete.RSub x 𝜏 u) =
  RSub (Ann x) (internRType subst 𝜏) (internProp (addBinder x subst) u)

internProp :: Map Ident Int -> Concrete.Term -> Prop
internProp = internTerm

addBinder :: Ident -> Map Ident Int -> Map Ident Int
addBinder x subst =
  Map.insert x 0 (Map.map (+1) subst)


-- TODO: shadowing in externalisation

externTerm :: Term -> Concrete.Term
externTerm (Var i) = Concrete.Var (Ident ("__DB:"++show i))
externTerm (NVar x) = Concrete.Var x
externTerm (Nat n) = Concrete.Nat n
externTerm Succ = Concrete.Succ
externTerm (App u v) = Concrete.App (externTerm u) (externTerm v)
externTerm PTrue = Concrete.PTrue
externTerm PFalse = Concrete.PFalse
externTerm (PEquals u v) = Concrete.PEquals (externTerm u) (externTerm v)
externTerm (PNot p) = Concrete.PNot (externTerm p)
externTerm (PAnd p q) = Concrete.PAnd (externTerm p) (externTerm q)
externTerm (PImpl p q) = Concrete.PImpl (externTerm p) (externTerm q)
externTerm (PEquiv p q) = Concrete.PEquiv (externTerm p) (externTerm q)
externTerm (PForall (Ann x) 𝜏 p) =
  Concrete.PForall x (externRType 𝜏) (externTerm (substProp [NVar x] p))

externIType :: IType -> Concrete.IType
externIType INat = Concrete.INat
externIType IProp = Concrete.IProp
externIType (IArrow 𝜏 𝜎) = Concrete.IArrow (externIType 𝜏) (externIType 𝜎)

externRType :: RType -> Concrete.RType
externRType RNat = Concrete.RNat
externRType RProp = Concrete.RProp
externRType (RArrow 𝜏 𝜎) = Concrete.RArrow (externRType 𝜏) (externRType 𝜎)
externRType (RSub (Ann x) 𝜏 u) =
  Concrete.RSub x (externRType 𝜏) (externProp (substProp [NVar x] u))

externProp :: Prop -> Concrete.Term
externProp = externTerm

------------------------------------------------------------------------------
-- Proof validation helpers

-- | This is a variant of the @()@ type whose only purpose, pretty much, is to
-- have a strict implementation of the 'Semigroup' type class. This lets us
-- define precondition checking by simply traversing data structures. See the
-- 'Validate' type class.
data Valid = Valid
  deriving (Show, Eq, Ord, Generic)

instance Semigroup Valid where
  Valid <> Valid = Valid

instance Monoid Valid where
  mempty = Valid

-- | This is a variant of the @NFData@ type class from the deepseq package. This
-- variant has two purpose: it's easy to define instances by traversal using
-- 'foldMap', and, more importantly, it is meant to be applied to fewer types,
-- to make sure that have validated our intermediate lemmas properly. See the
-- 'Prove' type class.
class Validate a where
  validate :: a -> Valid

instance Validate Valid where
  validate = id

instance Validate a => Validate [a] where
  validate = foldMap validate

instance {-# OVERLAPPABLE #-} TypeError ('Text "The type " ':<>: 'ShowType a ':<>: 'Text" is not a type which can be validated.") => Validate a where
  validate = error "Can't validate"

------------------------------------------------------------------------------
-- Generic pretty-printing code

-- The rendering code below is copied and adapted from the bnfc code

pp :: Print a => a -> Pp.Doc Pp.AnsiStyle
pp = render . prt 0

render :: Doc -> Pp.Doc Pp.AnsiStyle
render d = rend (map ($ "") $ d [])
  where
    rend :: [String] -> Pp.Doc Pp.AnsiStyle
    rend ss = case ss of
      "ax"     :ts -> Pp.hardline <> declKeyword "ax" Pp.<+> rend ts
      "def"    :ts -> Pp.hardline <> declKeyword "def" Pp.<+> rend ts
      "thm"    :ts -> Pp.hardline <> declKeyword "thm" Pp.<+> rend ts
      "["      :ts -> "[" <> rend ts
      "("      :ts -> "(" <> rend ts
      "{"      :ts -> "{" Pp.<+> rend ts
      t  : "," :ts -> Pp.pretty t <> Pp.comma Pp.<+> rend ts
      t  : "}" :ts -> Pp.pretty t Pp.<+> "}" Pp.<+> rend ts
      t  : ")" :ts -> Pp.pretty t <> ")" Pp.<+> rend ts
      t  : "]" :ts -> Pp.pretty t <> "]" Pp.<+> rend ts
      t        :ts -> Pp.pretty t Pp.<+> rend ts
      _ -> Pp.emptyDoc

    declKeyword = Pp.annotate Pp.bold


------------------------------------------------------------------------------
-- Immediate subterm traversals

-- (sort of in the style of uniplate. See also
-- https://www.twanvl.nl/blog/haskell/traversing-syntax-trees)

termSubs :: Applicative f => (Int -> Term -> f Term) ->  (Int -> RType -> f RType) -> Int -> Term -> f Term
termSubs _ _ _ t@(Var _) = pure t
termSubs _ _ _ t@(NVar _) = pure t
termSubs _ _ _ t@(Nat _) = pure t
termSubs _ _ _ t@Succ = pure t
termSubs on_term _ env (App t u) = App <$> on_term env t <*> on_term env u
termSubs _on_term _on_rtype _env PTrue =
  pure PTrue
termSubs _on_term _on_rtype _env PFalse =
  pure PFalse
termSubs on_term _on_rtype env (PEquals t u) =
  PEquals <$> on_term env t <*> on_term env u
termSubs on_term _on_rtype env (PNot p) =
  PNot <$> on_term env p
termSubs on_term _on_rtype env (PImpl p q) =
  PImpl <$> on_term env p <*> on_term env q
termSubs on_term _on_rtype env (PEquiv p q) =
  PEquiv <$> on_term env p <*> on_term env q
termSubs on_term _on_rtype env (PAnd p q) =
  PAnd <$> on_term env p <*> on_term env q
termSubs on_term on_rtype env (PForall x 𝜏 p) =
  PForall x <$> on_rtype env 𝜏 <*> on_term (1+env) p

rtypeSubs ::
  Applicative f =>
  (Int -> RType -> f RType) ->
  (Int -> Prop -> f Prop) ->
  Int -> RType -> f RType
rtypeSubs _on_rtype _on_prop _env RNat =
  pure RNat
rtypeSubs _on_rtype _on_prop _env RProp =
  pure RProp
rtypeSubs on_rtype _on_prop env (RArrow 𝜏 𝜇) =
  RArrow <$> on_rtype env 𝜏 <*> on_rtype env 𝜇
rtypeSubs on_rtype on_prop env (RSub x 𝜏 p) =
  RSub x <$> on_rtype env 𝜏 <*> on_prop (env+1) p
{-# SPECIALIZE rtypeSubs :: Monoid a => (Int -> RType -> Const a RType) -> (Int -> Prop -> Const a Prop) -> Int -> RType -> Const a RType #-}
-- TODO: More of these ⬆️

propSubs ::
  Applicative f =>
  (Int -> Term -> f Term) ->
  (Int -> RType -> f RType) ->
  (Int -> Prop -> f Prop) ->
  Int -> Prop -> f Prop
propSubs on_term on_rtype _on_prop = termSubs on_term on_rtype

termSubs_ :: Applicative f => (Term -> f Term) -> (RType -> f RType) -> Term -> f Term
termSubs_ on_term on_rtype = termSubs (\_ -> on_term) (\_ -> on_rtype)0

rtypeSubs_ ::
  Applicative f =>
  (RType -> f RType) ->
  (Prop -> f Prop) ->
  RType -> f RType
rtypeSubs_ on_rtype on_prop = rtypeSubs (\_ -> on_rtype) (\_ -> on_prop) 0

propSubs_ ::
  Applicative f =>
  (Term -> f Term) ->
  (RType -> f RType) ->
  (Prop -> f Prop) ->
  Prop -> f Prop
propSubs_ on_term on_rtype on_prop =
  propSubs (\_ -> on_term) (\_ -> on_rtype) (\_ -> on_prop) 0

termFoldSubs :: forall a. Monoid a => (Int -> Term -> a) -> (Int -> RType -> a) -> Int -> Term -> a
termFoldSubs = coerce $ termSubs @(Const a)

termFoldSubs_ :: forall a. Monoid a => (Term -> a) -> (RType -> a) -> Term -> a
termFoldSubs_ = coerce $ termSubs_ @(Const a)

rtypeFoldSubs ::
  forall a. Monoid a =>
  (Int -> RType -> a) ->
  (Int -> Prop -> a) ->
  Int -> RType -> a
rtypeFoldSubs = coerce $ rtypeSubs @(Const a)

rtypeFoldSubs_ ::
  forall a. Monoid a =>
  (RType -> a) ->
  (Prop -> a) ->
  RType -> a
rtypeFoldSubs_ = coerce $ rtypeSubs_ @(Const a)

propFoldSubs ::
  forall a. Monoid a =>
  (Int -> Term -> a) ->
  (Int -> RType -> a) ->
  (Int -> Prop -> a) ->
  Int -> Prop -> a
propFoldSubs = coerce $ propSubs @(Const a)

propFoldSubs_ ::
  forall a. Monoid a =>
  (Term -> a) ->
  (RType -> a) ->
  (Prop -> a) ->
  Prop -> a
propFoldSubs_ = coerce $ propSubs_ @(Const a)

termMapSubs_ :: (Term -> Term) -> (RType -> RType) -> Term -> Term
termMapSubs_ = coerce $ termSubs_ @Identity

rtypeMapSubs_ ::
  (RType -> RType) ->
  (Prop -> Prop) ->
  RType -> RType
rtypeMapSubs_ = coerce $ rtypeSubs_ @Identity

propMapSubs_ ::
  (Term -> Term) ->
  (RType -> RType) ->
  (Prop -> Prop) ->
  Prop -> Prop
propMapSubs_ = coerce $ propSubs_ @Identity

------------------------------------------------------------------------------
-- Smart constructors for props

pand :: Prop -> Prop -> Prop
pand PTrue p = p
pand p PTrue = p
pand p q = p `PAnd` q

pimpl :: Prop -> Prop -> Prop
pimpl PTrue p = p
pimpl _ PTrue = PTrue
pimpl p q = p `PImpl` q

pforall :: Ann Ident -> RType -> Prop -> Prop
pforall _ _ PTrue = PTrue
pforall x 𝜏 p = PForall x 𝜏 p

------------------------------------------------------------------------------
-- Proofs

-- TODO: make into an abstract type, to this effect we also need to make sure
-- not to export the 'Prove' type class. Which may require some unfortunate
-- boilerplate.
newtype Theorem = Proved Goal

class Prove a where
  prove :: Goal -> a

instance Prove Theorem where
  prove = Proved

instance (Validate a, Prove b) => Prove (a -> b) where
  prove g x | Valid <- validate x = prove g

ensuring :: HasCallStack => Bool -> a -> a
ensuring True = id
ensuring False = error "Something went wrong"

validating :: (HasCallStack, Functor f) => (Goal -> f Theorem) -> Goal -> f Valid
validating k g = (\(Proved g') -> ensuring (g == g') Valid) <$> k g

check :: (REnv -> TcM a) -> (a -> Tac) -> Tac
check chk tac = Tactic.Mk $ \k g@Goal{bound_variables} -> Compose $ do
  glbls <- view #globals
  tenv <- view #thms
  let env =
        emptyREnv
        & (\e -> Map.foldrWithKey addGlobal e glbls)
        & (\e -> foldr (uncurry addLocal) e (over (mapped . _2) embedIType bound_variables))
  let (the_prop, potential_proof_obligations) = runTcM tenv glbls (chk env)
  let proof_obligations = toListOf (traverse . filtered ((== Discharged) . snd) . _1) potential_proof_obligations
  getCompose $ prove g <$> traverse (validating k) proof_obligations <*> validating (Tactic.eval (tac the_prop) k) g

thm_assumption :: MonadPlus m => Goal -> m Theorem
thm_assumption g@(Goal {hyps, stoup=Nothing, concl}) = do
  guard (concl `elem` hyps)
  return $ Proved g
thm_assumption (Goal {stoup=Just _}) = mzero

assumption :: MonadPlus m => Tactic Goal Theorem m
assumption = Tactic.Mk $ \_ g -> Compose $ pure <$> thm_assumption g

unify' :: forall m t v. (Unification.BindingMonad t v m) => Unification.UTerm t v -> Unification.UTerm t v -> m Bool
unify' u v =
  runExceptT (Unification.unify u v) >>= \case
    Right _ -> return True
    Left (_ :: Unification.UFailure t v) -> return False

-- TODO: hum… if a forall has a condition inside the type, it is completely
-- ignored, hence subsumes, as currently implemented, lets me prove false
-- things.
subsumes :: Prop -> Prop -> Bool
subsumes h0 c0 = Unification.runSTRBinding $ go [] h0 c0
  where
    go subst (PForall _ _ p) c = do
      v <- Unification.freeVar
      go (v:subst) p c
    go subst (PEquals u v) (PEquals w e) = do
      let
        u' = toUTerm subst u
        v' = toUTerm subst v
        w' = toUTerm [] w
        e' = toUTerm [] e
      l <- unify' u' w'
      r <- unify' v' e'
      return $ l && r
    go _ _ _ =
      return False

    toUTerm :: forall v. [v] -> Term -> Unification.UTerm TermView v
    toUTerm subst (Var i) = case i < length subst of
      True -> Unification.UVar (subst !! i)
      False -> Unification.UTerm (VVar i)
    toUTerm _ (NVar x) =
      Unification.UTerm (VNVar x)
    toUTerm _ (Nat n) =
      Unification.UTerm (VNat n)
    toUTerm _ Succ =
      Unification.UTerm VSucc
    toUTerm subst (App u v) =
      Unification.UTerm (VApp (toUTerm subst u) (toUTerm subst v))
    toUTerm _ PTrue =
      Unification.UTerm VTrue
    toUTerm _ PFalse =
      Unification.UTerm VFalse
    toUTerm subst (PEquals u v) =
      Unification.UTerm (VEquals (toUTerm subst u) (toUTerm subst v))
    toUTerm subst (PNot u) =
      Unification.UTerm (VNot (toUTerm subst u))
    toUTerm subst (PAnd u v) =
      Unification.UTerm (VAnd (toUTerm subst u) (toUTerm subst v))
    toUTerm subst (PImpl u v) =
      Unification.UTerm (VImpl (toUTerm subst u) (toUTerm subst v))
    toUTerm subst (PEquiv u v) =
      Unification.UTerm (VEquiv (toUTerm subst u) (toUTerm subst v))
    toUTerm _ (PForall x 𝜏 p) =
      Unification.UTerm (VForall x 𝜏 p)


thm_subsumption :: MonadPlus m => Goal -> m Theorem
thm_subsumption g@(Goal {hyps, stoup=Nothing, concl}) = do
  guard (any (`subsumes` concl) hyps)
  return $ Proved g
thm_subsumption (Goal {stoup=Just _}) = mzero

subsumption :: MonadPlus m => Tactic Goal Theorem m
subsumption = Tactic.Mk $ \_ g -> Compose $ pure <$> thm_subsumption g

-- Traverses all the terms which are not under a binder
propTerms :: Applicative f => (Term -> f Term) -> Prop -> f Prop
propTerms f (PEquals u v) = PEquals <$> f u <*> f v
propTerms _ p@(PForall _ _ _) = pure p
propTerms f p = propSubs_ f pure (propTerms f) p

goalTerms :: Applicative f => (Term -> f Term) -> Goal -> f Goal
goalTerms f (Goal {bound_variables, hyps, stoup, concl}) =
  Goal bound_variables <$> (traverse . propTerms) f hyps <*> (traverse . propTerms) f stoup <*> propTerms f concl

newtype ConstM m a = ConstM (m ())
  deriving (Functor)
instance Applicative m => Applicative (ConstM m) where
  pure _ = ConstM (pure ())
  ConstM a <*> ConstM b = ConstM ((\() () -> ()) <$> a <*> b)

goalIterTerms :: forall m. Applicative m => (Term -> m ()) -> Goal -> m ()
goalIterTerms = coerce $ goalTerms @(ConstM m)

thm_cc :: Goal -> TacM Theorem
thm_cc g@(Goal {hyps, stoup=Nothing, concl}) =
    let
      slurped = CC.exec CC.empty $ void $ goalIterTerms CC.add g
      learned = CC.exec slurped $ forM_ hyps $ \h ->
          case h of
            PEquals u v -> CC.merge u v
            _ -> return ()
      equiv u v = CC.eval learned $ CC.equivalent u v

      inconsistent_hyp (PNot (PEquals u v)) = equiv u v
      inconsistent_hyp _ = False

      inconsistent = any inconsistent_hyp hyps
      concl_true = case concl of
          PEquals u v -> equiv u v
          _ -> False
    in
    case concl_true || inconsistent of
      True -> return $ Proved g
      False -> doFail g
thm_cc g@(Goal {stoup=Just _}) = doFail g

congruence_closure :: Tac
congruence_closure = Tactic.Mk $ \_ g -> Compose $ pure <$> thm_cc g

doFail :: Goal -> TacM a
doFail g = lift $ Failure [g]

fail :: Tac
fail = Tactic.Mk $ \_ g -> Compose $ doFail g

-- move to tactics
repeat :: MonadPlus m => Tactic goal thm m -> Tactic goal thm m
repeat tac = (tac `Tactic.thn` Main.repeat tac) `Tactic.or` Tactic.id
  -- or id: define and use try

addHyp :: Prop -> [Prop] -> [Prop]
addHyp PTrue = id
addHyp p = (p:)

-- TODO: investigate why calling `prove sub` instead of `prove g` doesn't appear
-- to produce errors.
intro :: Tac
intro = Tactic.Mk $ \(validating -> k) g -> case g of
  Goal {stoup=Nothing, concl=PNot p} ->
    let
      sub = g
        & over #hyps (addHyp p)
        & set #concl PFalse
    in
    prove g <$> k sub
  Goal {stoup=Nothing, concl=p `PImpl` q} ->
    let
      sub = g
        & over #hyps (addHyp p)
        & set #concl q
    in
    prove g <$> k sub
  Goal {stoup=Nothing, concl=PForall (Ann x) 𝜏 p} -> Compose @TacM $ do
    glbls <- view #globals
    if x `Map.notMember` glbls then
        let
          x' = avoid x (freeVarsGoal g ++ Map.keys glbls)
          sub = g
            & over (#bound_variables . traverse . _1) (\y -> if y == x then x' else y)
            & over #bound_variables ((x, underlyingIType 𝜏) :)
            & over (#hyps . traverse) (substProp [NVar x'])
            & over #hyps (addHyp (constraint 𝜏 (NVar x')))
            & set #concl (substProp [NVar x']p)
        in
        getCompose $ prove g <$> k sub
    else
        let
          x' = avoid x (freeVarsGoal g ++ Map.keys glbls)
          sub = g
            & over #bound_variables ((x', underlyingIType 𝜏) :)
            & over #hyps (addHyp (constraint 𝜏 (NVar x')))
            & set #concl (substProp [NVar x'] p)
        in
        getCompose $ prove g <$> k sub
  _ -> Compose $ doFail g

max_intros :: Tac
max_intros = Main.repeat intro

discharge :: Tac
discharge = assumption `Tactic.or` subsumption `Tactic.or` (max_intros `Tactic.thn`congruence_closure)

dischargeWith :: [Ident] -> Tac
dischargeWith lems =
  foldr (\lem tac -> use lem [] `Tactic.thn` tac) discharge lems

use :: Ident -> [Term] -> Tac
use x h = Tactic.Mk $ \(validating -> k) g@(Goal {stoup}) -> Compose $
  case stoup of
    Nothing -> do
      tenv <- view #thms
      x_prop <- case Map.lookup x tenv of { Just p -> return p ; Nothing -> doFail g }
      let
        sub = g
          & over #hyps (addHyp (instantiate x_prop h))
      getCompose $ prove g <$> k sub
    Just _ -> doFail g
 where
   instantiate :: Prop -> [Term] -> Prop
   instantiate (PForall _ _ p) (u:us) = instantiate (substProp [u] p) us
     -- TODO: check the types!
   instantiate p [] = p
   instantiate _ _ = error "Not enough foralls."

have0 :: Prop -> Tac
have0 p = Tactic.Mk $ \(validating -> k) g@(Goal {stoup}) ->
  case stoup of
    Nothing -> Compose $ do
      let
        side = g
          & set #concl p
        sub = g
          & over #hyps (addHyp p)
      getCompose $
        prove g <$> k side <*> k sub
    Just _ -> Compose $ doFail g

have :: Prop -> [Ident] -> Tac
have p lems = have0 p `Tactic.dispatch` [dischargeWith lems, Tactic.id]

-- | Induction on the natural numbers @ℕ@
induction :: Ident -> Tac
induction x = Tactic.Mk $ \ k g@(Goal {stoup, concl}) ->
  case stoup of
    Nothing ->
      let
        sub_0 = g
          & over #concl (substNProp x (Nat 0))
        sub_succ = g
          & over #hyps (addHyp concl)
          & over #concl (substNProp x (App Succ (NVar x)))
      in
     (\(Proved _) (Proved _) -> Proved g)
       <$> k sub_0
       <*> k sub_succ
    Just _ -> Compose $ doFail g

-- TODO: refactor together with have0. Somehow.
focus0 :: Prop -> Tac
focus0 p = Tactic.Mk $ \(validating -> k) g@(Goal {stoup}) -> Compose $
  case stoup of
    Nothing -> do
      let
        side = g
          & set #concl p
        sub = g
          & set #stoup (Just p)
      getCompose $ prove g <$> k side <*> k sub
    Just _ -> doFail g

focus :: Prop -> [Ident] -> Tac
focus p lems = focus0 p `Tactic.dispatch` [dischargeWith lems, Tactic.id]

with :: Term -> Tac
with u = Tactic.Mk $ \(validating -> k) g@(Goal {stoup}) ->
  case stoup of
     -- TODO: check the type!
    Just (PForall _ _𝜎 p) ->
      let
        sub = g
          & set #stoup (Just (substProp [u] p))
      in
      prove g <$> k sub
    _ -> Compose $ doFail g

chain :: Tac
chain = Tactic.Mk $ \(validating -> k) g@(Goal{stoup}) ->
  case stoup of
    Just (PImpl p q) ->
      let
        side = g
          & set #stoup Nothing
          & set #concl p
        sub = g
          & set #stoup (Just q)
      in
      prove g <$> k side <*> k sub
    _ -> Compose $ doFail g

premise :: Tac
premise = Tactic.Mk $ \(validating -> k) g@(Goal {stoup}) ->
  case stoup of
    Just (PImpl p q) ->
      let
        side = g
          & set #stoup Nothing
          & set #concl p
        sub = g
          & set #stoup (Just q)
      in
      prove g <$> k sub <*> k side
    _ -> Compose $ doFail g

deactivate :: Tac
deactivate = Tactic.Mk $ \(validating -> k) g@(Goal {stoup}) ->
  case stoup of
    Just p ->
      let
        sub = g
          & over #hyps (addHyp p)
          & set #stoup Nothing
      in
      prove g <$> k sub
    _ -> Compose $ doFail g


data ResM a
  = Success a
  | Failure [Goal]
  deriving (Functor)

instance Applicative ResM where
  pure = Success

  (Success f) <*> (Success x) = Success (f x)
  (Success _) <*> (Failure gs) = Failure gs
  (Failure gs) <*> (Success _) = Failure gs
  (Failure gs) <*> (Failure gs') = Failure (gs <> gs')

instance Alternative ResM where
  empty = Failure []
  (Success x) <|>  _ = Success x
  (Failure _) <|> act = act

instance Monad ResM where
  (Success a) >>= k = k a
  (Failure gs) >>= _ = Failure gs

instance MonadPlus ResM where

data ProofEnv = ProofEnv
  { thms :: ThmEnv
  , globals :: Map Ident RType
  }
  deriving (Generic)

type TacM = ReaderT ProofEnv ResM

type Tac = Tactic Goal Theorem TacM

------------------------------------------------------------------------------
-- Congruence closure

data TermView a
  = VVar Int
  | VNVar Ident
  | VNat Integer
  | VSucc
  | VApp a a
  | VTrue
  | VFalse
  | VEquals a a
  | VNot a
  | VAnd a a
  | VImpl a a
  | VEquiv a a
  | VForall (Ann Ident) RType Prop
  deriving (Eq, Ord, Functor, Foldable, Traversable, Show)

instance CC.LiftRelation TermView where
  liftRelation _ (VVar x) = \case {VVar y -> pure $ x == y; _ -> pure False}
  liftRelation _ (VNVar x) = \case {VNVar y -> pure $ x == y; _ -> pure False}
  liftRelation _ (VNat n) = \case {VNat p -> pure $ n == p; _ -> pure False}
  liftRelation _ VSucc = \case {VSucc -> pure $ True; _ -> pure False}
  liftRelation r (VApp u v) = \case
    VApp w e -> (&&) <$> r u w <*> r v e
    _ -> pure False
  liftRelation _ VTrue = \case {VTrue -> pure $ True; _ -> pure False}
  liftRelation _ VFalse = \case {VFalse -> pure $ True; _ -> pure False}
  liftRelation r (VEquals u v) = \case
    VEquals w e -> (&&) <$> r u w <*> r v e
    _ -> pure False
  liftRelation r (VNot u) = \case
    VNot v -> r u v
    _ -> pure False
  liftRelation r (VAnd u v) = \case
    VAnd w e -> (&&) <$> r u w <*> r v e
    _ -> pure False
  liftRelation r (VImpl u v) = \case
    VImpl w e -> (&&) <$> r u w <*> r v e
    _ -> pure False
  liftRelation r (VEquiv u v) = \case
    VEquiv w e -> (&&) <$> r u w <*> r v e
    _ -> pure False
  liftRelation _ (VForall x 𝜏 p) = \case
    VForall y 𝜎 q -> pure (y == x && 𝜏 == 𝜎 && p == q)
    _ -> pure False

instance CC.Unfix Term TermView where
  view (Var x) = VVar x
  view (NVar x) = VNVar x
  view (Nat n) = VNat n
  view Succ = VSucc
  view (App u v) = VApp u v
  view PTrue = VTrue
  view PFalse = VFalse
  view (PEquals u v) = VEquals u v
  view (PNot u) = VNot u
  view (PAnd u v) = VAnd u v
  view (PImpl u v) = VImpl u v
  view (PEquiv u v) = VEquiv u v
  view (PForall x 𝜏 p) = VForall x 𝜏 p

------------------------------------------------------------------------------
-- Unification

instance Unifiable TermView where
  zipMatch (VVar x) (VVar y) | x == y = pure $ VVar x
  zipMatch (VNVar x) (VNVar y) | x == y = pure $ VNVar x
  zipMatch (VNat n) (VNat p) | n == p = pure $ VNat n
  zipMatch VSucc VSucc = pure $ VSucc
  zipMatch (VApp u v) (VApp w e) = pure $
    VApp (Right (u, w)) (Right (v, e))
  zipMatch _ _ = Nothing

------------------------------------------------------------------------------
-- The rest

embedIType :: IType -> RType
embedIType INat = RNat
embedIType IProp = RProp
embedIType (IArrow t u) = RArrow (embedIType t) (embedIType u)

underlyingIType :: RType -> IType
underlyingIType RNat = INat
underlyingIType RProp = IProp
underlyingIType (RArrow t u) = IArrow (underlyingIType t) (underlyingIType u)
underlyingIType (RSub _ t _) = underlyingIType t

chooseAVariableNameBasedOn :: RType -> Ident
chooseAVariableNameBasedOn _ = Ident "x"

constraint :: RType -> Term -> Prop
constraint RNat _ = PTrue
constraint RProp _ = PTrue
constraint (RArrow t u) f =
  let x = Ann (chooseAVariableNameBasedOn t) in
  pforall x t (constraint t (Var 0) `pimpl` constraint u (f `App` (Var 0)))
constraint (RSub _ t p) e = (constraint t e) `pand` (substProp [e] p)

-- It's an infinite stream really
varQualifiers :: [String]
varQualifiers = map show ([1..] :: [Integer])

-- TODO: avoid is generally used in a context where there are globals, that we
-- need to avoid too. Let's track this. Maybe make an abstraction of this, with
-- a monadic `avoid` possibly?
--
-- A fresh variable based on the name of the argument. Second argument ought to
-- be a set.
avoid :: Ident -> [Ident] -> Ident
avoid v@(Ident x) forbidden = head $ filter (`notElem` forbidden) candidates
  where
    candidates = v : map qualifyWith varQualifiers
    qualifyWith suffix = Ident $ x ++ suffix

freeVarsTerm :: Term -> [Ident]
freeVarsTerm (NVar x) = [ x ]
freeVarsTerm t = termFoldSubs_ freeVarsTerm freeVarsRType t

freeVarsRType :: RType -> [Ident]
freeVarsRType = rtypeFoldSubs_ freeVarsRType freeVarsProp

freeVarsProp :: Prop -> [Ident]
freeVarsProp = propFoldSubs_ freeVarsTerm freeVarsRType freeVarsProp

substProp :: [Term] -> Prop -> Prop
substProp subst (PForall y 𝜏 p) =
  PForall y 𝜏 (substProp (shift subst) p)
substProp subst p =
  propMapSubs_ (substTerm subst) (substRType subst) (substProp subst) p

substNProp :: Ident -> Term -> Prop -> Prop
substNProp x t = propMapSubs_ (substNTerm x t) (substNRType x t) (substNProp x t)

substRType :: [Term] -> RType -> RType
substRType subst (RSub y 𝜏 p) =
  RSub y 𝜏 (substProp (shift subst) p)
substRType subst 𝜏 =
  rtypeMapSubs_ (substRType subst) (substProp subst) 𝜏

substNRType :: Ident -> Term -> RType -> RType
substNRType x t = rtypeMapSubs_ (substNRType x t) (substNProp x t)

liftTerm :: Term -> Term
liftTerm = substTerm (map Var [1..])

shift :: [Term] -> [Term]
shift subst = Var 0 : map liftTerm subst

substTerm :: [Term] -> Term -> Term
substTerm subst u@(Var i) = Maybe.fromMaybe u $ preview (ix i) subst
substTerm subst (PForall y 𝜏 p) = PForall y 𝜏 (substProp (shift subst) p)
substTerm subst u = termMapSubs_ (substTerm subst) (substRType subst) u

substNTerm :: Ident -> Term -> Term -> Term
substNTerm x t u@(NVar y)
  | x == y = t
  | otherwise = u
substNTerm x t u = termMapSubs_ (substNTerm x t) (substNRType x t) u

data IEnv = MkIEnv
  { named :: Map Ident IType
  , db :: [IType]
  }
  deriving (Generic)

ilookupNamed :: Ident -> IEnv -> Maybe IType
ilookupNamed x env = Map.lookup x (env ^. #named)

ilookupDb :: Int -> IEnv -> Maybe IType
ilookupDb i env = preview (ix i) (env ^. #db)

ipushDb :: IType -> IEnv -> IEnv
ipushDb 𝜏 = over #db (𝜏:)

typeCheckIntrinsicTerm :: IEnv -> Term -> IType -> Bool
typeCheckIntrinsicTerm env e u =
  (typeInferIntrinsicTerm env e) == Just u

typeInferIntrinsicTerm :: IEnv -> Term -> Maybe IType
typeInferIntrinsicTerm env (Var i) = do
  ilookupDb i env
typeInferIntrinsicTerm env (NVar x) = do
  ilookupNamed x env
typeInferIntrinsicTerm _env (Nat _) = do
  return $ internIType' [Concrete.iType|ℕ|]
typeInferIntrinsicTerm _env Succ = do
  return $ internIType' [Concrete.iType|ℕ → ℕ|]
typeInferIntrinsicTerm env (f `App` e) = do
  (u `IArrow` t) <- typeInferIntrinsicTerm env f
  guard (typeCheckIntrinsicTerm env e u)
  return t
typeInferIntrinsicTerm _env PTrue = do
  return IProp
typeInferIntrinsicTerm _env PFalse = do
  return IProp
typeInferIntrinsicTerm env (PEquals u v) = do
  itype_of_u <- typeInferIntrinsicTerm env u
  () <- case typeCheckIntrinsicTerm env v itype_of_u of
        True -> Just ()
        False -> Nothing
  return IProp
typeInferIntrinsicTerm env (PNot p) = do
  () <- case typeCheckIntrinsicTerm env p IProp of
    True -> Just ()
    False -> Nothing
  return IProp
typeInferIntrinsicTerm env (PAnd p q) = do
  () <- case typeCheckIntrinsicTerm env p IProp of
    True -> Just ()
    False -> Nothing
  () <- case typeCheckIntrinsicTerm env q IProp of
    True -> Just ()
    False -> Nothing
  return IProp
typeInferIntrinsicTerm env (PImpl p q) = do
  () <- case typeCheckIntrinsicTerm env p IProp of
    True -> Just ()
    False -> Nothing
  () <- case typeCheckIntrinsicTerm env q IProp of
    True -> Just ()
    False -> Nothing
  return IProp
typeInferIntrinsicTerm env (PEquiv p q) = do
  () <- case typeCheckIntrinsicTerm env p IProp of
    True -> Just ()
    False -> Nothing
  () <- case typeCheckIntrinsicTerm env q IProp of
    True -> Just ()
    False -> Nothing
  return IProp
typeInferIntrinsicTerm env (PForall _ 𝜏 p) = do
  () <- case typeCheckIntrinsicTerm (ipushDb (underlyingIType 𝜏) env) p IProp of
    True -> Just ()
    False -> Nothing
  return IProp

-- | Assumes that @'underlyingIType' t == IArrow _ _@
decompArrow :: HasCallStack => RType -> (RType, RType, Term -> Prop)
decompArrow (u `RArrow` t) = (u, t, const PTrue)
decompArrow (RSub _ u p) =
  let !(v, t, q) = decompArrow u in
  (v, t, \e -> q e `pand` substProp [e] p)
decompArrow _ = error "This has to be an arrow"

data Localised a
  = Local a
  | Global a
  deriving (Generic, Show)

projectLocalised :: Localised a -> a
projectLocalised (Local a) = a
projectLocalised (Global a) = a

data REnv = REnv
  { named :: Map Ident (Localised RType)
  , db :: [RType]}
  deriving (Generic, Show)

emptyREnv :: REnv
emptyREnv = REnv {named=Map.empty, db=[]}

rlookupNamed :: Ident -> REnv -> Maybe (Localised RType)
rlookupNamed x env = Map.lookup x (env ^. #named)

rlookupDb :: Int -> REnv -> Maybe RType
rlookupDb i env = preview (ix i) (env ^. #db)

(!) :: HasCallStack => REnv -> Ident -> RType
(!) env x = case Map.lookup x (env ^. #named) of
  Just 𝜏 -> projectLocalised 𝜏
  Nothing -> error $ "Ident " ++ show x ++ " not in REnv " ++ show env

addLocal :: Ident -> RType -> REnv -> REnv
addLocal x 𝜏 = over #named $ Map.insert x (Local 𝜏)

addGlobal :: Ident -> RType -> REnv -> REnv
addGlobal x 𝜏 = over #named $ Map.insert x (Global 𝜏)

globalsREnv :: IndexedTraversal' Ident REnv RType
globalsREnv = #named .> itraversed <. #_Global

pushDb :: RType -> REnv -> REnv
pushDb 𝜏 = over #db (𝜏:)

underlyingITypes :: REnv -> IEnv
underlyingITypes env = MkIEnv
  { named = Map.map (underlyingIType . projectLocalised) (env ^. #named)
  , db = map underlyingIType (env ^. #db)
  }

data VarClass
  = DefinedLocal
  | DefinedGlobal
  | Undefined

avoidREnv :: Ident -> REnv -> Ident
avoidREnv x env =
  avoid x (Map.keys (env ^. #named))

data Goal = Goal
  { bound_variables :: [(Ident, IType)]
  , hyps :: [Prop]
  , stoup :: Maybe Prop
  , concl :: Prop
  }
  deriving (Eq, Generic)
-- /!\ DANGER MR. ROBINSON: `Eq` instance not compatible with 𝛼-conversion

freeVarsGoal :: Goal -> [Ident]
freeVarsGoal (Goal {bound_variables, hyps, stoup, concl}) =
  concat
    [ map fst bound_variables
    , concatMap freeVarsProp hyps
    , concatMap freeVarsProp stoup
    , freeVarsProp concl
    ]

ppBoundVar :: (Ident, IType) -> Pp.Doc Pp.AnsiStyle
ppBoundVar (a, b) = pp a Pp.<+> ":" Pp.<+> pp (externIType b)

ppGoal :: Goal -> Pp.Doc Pp.AnsiStyle
ppGoal (Goal {bound_variables, hyps, stoup=Nothing, concl}) =
  Pp.enclose "[" "]" (Pp.sep (Pp.punctuate Pp.comma (map ppBoundVar bound_variables)))
  Pp.<+> Pp.sep (Pp.punctuate Pp.comma (map pp (map externProp hyps)))
  Pp.<+> "⊢"
  Pp.<+> pp (externProp concl)
ppGoal (Goal {bound_variables, hyps, stoup=Just stoup, concl}) =
  Pp.enclose "[" "]" (Pp.sep (Pp.punctuate Pp.comma (map ppBoundVar bound_variables)))
  Pp.<+> Pp.sep (Pp.punctuate Pp.comma (map pp (map externProp hyps)))
  Pp.<+> "|"
  Pp.<+> pp (externProp stoup)
  Pp.<+> "⊢"
  Pp.<+> pp (externProp concl)

ppDSGoal :: (Goal, DischargeStatus) -> Pp.Doc Pp.AnsiStyle
ppDSGoal (goal, ds) = ppGoal goal Pp.<+> ppDischargeStatus ds
  where
    ppDischargeStatus Open = Pp.annotate (Pp.color Pp.Red) "✘"
    ppDischargeStatus Discharged = Pp.annotate (Pp.color Pp.Green) "✔"

ppGoals :: [(Goal, DischargeStatus)] -> Pp.Doc Pp.AnsiStyle
ppGoals gs = Pp.indent 2 $
    Pp.concatWith (Pp.surround Pp.hardline) $ map ppOneGoal gs
  where
    ppOneGoal g = lead Pp.<+> Pp.align (ppDSGoal g)
    lead = Pp.annotate Pp.bold "↳"

ppAttemptedGoal :: (Goal, DischargeStatus, DischargeStatus, [Goal]) -> Pp.Doc Pp.AnsiStyle
ppAttemptedGoal (goal, autods, interactiveds, remaining) =
    ppGoal goal Pp.<+> ppAutoDischargeStatus autods Pp.<+> ppInteractiveDischargeStatus interactiveds
    Pp.<+> Pp.hardline Pp.<+> ppGoals (zip remaining (Prelude.repeat Open))
  where
    ppAutoDischargeStatus Open = Pp.annotate (Pp.color Pp.Yellow) "✘"
    ppAutoDischargeStatus Discharged = Pp.annotate (Pp.color Pp.Green) "✔"

    ppInteractiveDischargeStatus Open = Pp.annotate (Pp.color Pp.Red) "✘"
    ppInteractiveDischargeStatus Discharged = Pp.annotate (Pp.color Pp.Green) "✔"

ppAttemptedGoals :: [(Goal, DischargeStatus, DischargeStatus, [Goal])] -> Pp.Doc Pp.AnsiStyle
ppAttemptedGoals gs = Pp.indent 2 $
    Pp.concatWith (Pp.surround Pp.hardline) $ map ppOneGoal gs
  where
    ppOneGoal g = lead Pp.<+> Pp.align (ppAttemptedGoal g)
    lead = Pp.annotate Pp.bold "↳"


type TcM = ReaderT [Prop] (Writer [Goal])

data DischargeStatus = Discharged | Open
  deriving (Eq)

runTcM :: ThmEnv -> Map Ident RType -> TcM a -> (a, [(Goal, DischargeStatus)])
runTcM thms globals act =
    over (_2 . mapped) try_discharge $ runWriter $ runReaderT act []
  where
    try_discharge :: Goal -> (Goal, DischargeStatus)
    try_discharge g =
      case runReaderT (Tactic.proveWith (\_ -> mzero) discharge g) (ProofEnv {thms, globals}) of
        Success (Proved g') | g == g' -> (g, Discharged)
        _ -> (g, Open)

runTcM' :: ThmEnv -> Map Ident RType -> TcM () -> [(Goal, DischargeStatus)]
runTcM' thms globals act = snd $ runTcM thms globals act

emit :: REnv -> Prop -> TcM ()
emit _env PTrue = return ()
emit env concl0 = do
  -- TODO: there is a bug here, in case of shadowing. Where the shadowing
  -- variable, will appear to bind the shadowed variables in some hypotheses,
  -- yielding incorrectly typed goals.
  let local_variables = env & itoListOf (#named .> itraversed <. (#_Local . to underlyingIType))
  -- TODO: generating names for the debruijns should have proper shadowing
  let dbs = env & itoListOf (#db .> itraversed <. to underlyingIType) & over (traverse . _1) (\i -> Ident ("db"++show i))
  let subst = map (NVar . fst) dbs
  let bound_variables = local_variables ++ dbs
  hyps0 <- ask
  let hyps = map (substProp subst) hyps0
  let concl = substProp subst concl0
  tell [Goal {bound_variables, hyps, concl, stoup=Nothing}]

assuming :: Prop -> TcM a -> TcM a
assuming PTrue = id
assuming p = local (p :)

shadowing :: Ident -> Ident -> TcM a -> TcM a
shadowing x x' act =
  local (map (substNProp x (NVar x'))) act

-- | Assumes that @'typeInferIntrinsicTerm' e == Just ('underlyingIType' t)@.
typeCheckRefinementTerm :: HasCallStack => REnv -> Term -> RType -> TcM ()
typeCheckRefinementTerm env e t = do
  type_of_e <- typeInferRefinementTerm env e
  assuming (constraint type_of_e e) $
    emit env $ constraint t e

typeInferRefinementTerm :: HasCallStack => REnv -> Term -> TcM RType
typeInferRefinementTerm env (Var i) = return $ Maybe.fromJust $ rlookupDb i env
typeInferRefinementTerm env (NVar x) = return $ env ! x
typeInferRefinementTerm _env (Nat _) = return $ RNat
typeInferRefinementTerm _env Succ = return $ internRType' [Concrete.rType|ℕ → ℕ|]
typeInferRefinementTerm env (f `App` e) = do
  type_of_f <- typeInferRefinementTerm env f
  let (type_of_arg, type_of_return, given_of_f) = decompArrow type_of_f
  assuming (given_of_f f) $ do
    typeCheckRefinementTerm env e type_of_arg
    return type_of_return
typeInferRefinementTerm _env PTrue = do
  return RProp
typeInferRefinementTerm _env PFalse = do
  return RProp
typeInferRefinementTerm env (PNot p) = do
  typeCheckProposition env p
  return RProp
typeInferRefinementTerm env (PAnd p q) = do
  typeCheckProposition env p
  typeCheckProposition env q
  return RProp
typeInferRefinementTerm env (PImpl p q) = do
  typeCheckProposition env p
  assuming p $
    typeCheckProposition env q
  return RProp
typeInferRefinementTerm env (PEquiv p q) = do
  typeCheckProposition env p
  assuming p $
    typeCheckProposition env q
  return RProp
typeInferRefinementTerm env (PForall _ t p) = do
  typeCheckProposition (pushDb t env) p
  return RProp
typeInferRefinementTerm env (u `PEquals` v) = do
  -- ⬇️Need proper error management
  let ienv = underlyingITypes env
  let (Just itype_of_u) = typeInferIntrinsicTerm ienv u
  let !() = case typeCheckIntrinsicTerm ienv v itype_of_u of
        True -> ()
        False -> error "Proper errors pliz"
  -- ⬇️ Very asymmetric and awful
  type_of_u <- typeInferRefinementTerm env u
  typeCheckRefinementTerm env v type_of_u
  return RProp

typeCheckProposition' :: HasCallStack => REnv -> Concrete.Term -> TcM Prop
typeCheckProposition' env p = do
  let p' = internProp' p
  typeCheckProposition env p'
  return p'

-- This type is a lie: typeCheckProposition should fail gracefully if the
-- intrinsic type is faulty somewhere.
typeCheckProposition :: HasCallStack => REnv -> Prop -> TcM ()
typeCheckProposition env p = typeCheckRefinementTerm env p RProp

type ThmEnv = Map Ident Prop

checkProgram :: REnv -> ThmEnv -> Concrete.Prog -> IO ()
checkProgram env0 tenv0 (Concrete.Prog decls0) = go env0 tenv0 decls0
  where
    go :: REnv -> ThmEnv -> [Concrete.Decl] -> IO ()
    go _env _tenv [] = return ()
    go env tenv (decl@(Concrete.Definition f t) : decls) = do
      Pp.putDoc $ pp decl
      putStrLn ""
      go (addGlobal f (internRType' t) env) tenv decls
    go env tenv (decl@(Concrete.Axiom z p) : decls) = do
      Pp.putDoc $ pp decl
      putStrLn ""
      let (p', goals) = runTcM tenv (toMapOf globalsREnv env) $ typeCheckProposition' env p
      Pp.putDoc $ ppGoals goals
      go env (Map.insert z p' tenv) decls
    go env tenv (Concrete.Theorem z p tacs : decls) = do
      Pp.putDoc $ pp (Concrete.Theorem z p Concrete.NothingTacAlt)
      putStrLn ""
      let
        (p_tc'd, goals) = runTcM tenv (toMapOf globalsREnv env) $ do
          p' <- typeCheckProposition' env p
          emit env p'
          return p'
        interactedGoals = applyMTacs tenv (toMapOf globalsREnv env) tacs goals
      Pp.putDoc $ ppAttemptedGoals interactedGoals
      go env (Map.insert z p_tc'd tenv) decls

    applyOne :: ThmEnv -> Map Ident RType -> Tac -> Goal -> (Goal, DischargeStatus, DischargeStatus, [Goal])
    applyOne tenv globals tac g = (g, Open, status, remaining)
      where
        res = apply tenv globals tac g
        (status, remaining) = case res of { Nothing -> (Discharged, []); Just gs -> (Open, gs) }

    applyTacs :: ThmEnv -> Map Ident RType -> [Tac] -> [(Goal, DischargeStatus)] -> [(Goal, DischargeStatus, DischargeStatus, [Goal])]
    applyTacs _ _ [] goals = map (\(g,status) -> (g, status, status, [])) goals
    applyTacs _ _ tacs [] = error $ "Too many tactics: " ++ show (length tacs) ++ "too many."
    applyTacs tenv globals tacs ((goal, Discharged):goals) = (goal, Discharged, Discharged, []) : applyTacs tenv globals tacs goals
    applyTacs tenv globals (tac:tacs) ((goal, Open):goals) = applyOne tenv globals tac goal : applyTacs tenv globals tacs goals

    applyMTacs :: ThmEnv -> Map Ident RType -> Concrete.MaybeTacAlt -> [(Goal, DischargeStatus)] -> [(Goal, DischargeStatus, DischargeStatus, [Goal])]
    applyMTacs tenv globals Concrete.NothingTacAlt = applyTacs tenv globals []
    applyMTacs tenv globals (Concrete.JustTacAlt (Concrete.TacAlt tacs)) = applyTacs tenv globals (map evalTac tacs)

evalTac :: Concrete.TacExpr -> Tac
evalTac Concrete.TId = Tactic.id
evalTac Concrete.TDone = discharge
evalTac (Concrete.TInd x) = induction x
evalTac Concrete.TIntros = max_intros
evalTac (Concrete.THave p lems) = check (\env -> typeCheckProposition' env p) $ \p' -> have p' lems
evalTac (Concrete.TFocus p lems) = check (\env -> typeCheckProposition' env p) $ \p' -> focus p' lems
evalTac (Concrete.TWith u) = with (internTerm' u)
evalTac (Concrete.TChain) = chain
evalTac (Concrete.TPremise) = premise
evalTac (Concrete.TDeactivate) = deactivate
evalTac (Concrete.TUse tac us) = use tac (map internTerm' us)
evalTac (Concrete.TSUse tac) = use tac []
evalTac (Concrete.TThen tac1 tac2) = Tactic.thn (evalTac tac1) (evalTac tac2)
evalTac (Concrete.TDispatch tac1 (Concrete.TacAlt alt)) = Tactic.dispatch (evalTac tac1) (map evalTac alt)

apply :: ThmEnv -> Map Ident RType -> Tac -> Goal -> Maybe [Goal]
apply thms globals tac goal =
  case runReaderT (Tactic.proveWith (\g -> lift (Failure [g])) tac goal) (ProofEnv{thms, globals}) of
    Success (Proved thm) -> ensuring (thm == goal) Nothing
    Failure gs -> Just gs

main :: IO ()
main = do
  Pp.putDoc $ pp [Concrete.term|f (f 1)|]
  putStrLn ""
  Pp.putDoc $ pp [Concrete.iType|(ℕ → ℕ) → ℕ → ℕ|]
  putStrLn ""
  let t = [Concrete.rType|{ x : ℕ → ℕ | ⊤ }|]
  Pp.putDoc $ pp t
  putStrLn ""
  Pp.putDoc $ pp (externIType (underlyingIType (internRType' t)))
  putStrLn ""
  Pp.putDoc $ pp (externProp (constraint (internRType' t) (internTerm' [Concrete.term|f|])))
  putStrLn ""
  Pp.putDoc $ pp [Concrete.term|∀ x : ℕ. x=y|]
  putStrLn ""
  Pp.putDoc $ pp (externProp (substNProp (Ident "y") (internTerm' [Concrete.term|x|]) (internProp' [Concrete.term|∀ x : ℕ. x=y|])))
  putStrLn ""
  let example = [Concrete.prog|
    def plus : ℕ → ℕ → ℕ
    ax plus_x_0 : ∀ x : ℕ. plus x 0 = x
    ax plus_x_succ : ∀ x : ℕ. ∀ y : ℕ. plus x (succ y) = succ (plus x y)
    thm plus_assoc : ∀ x : ℕ. ∀ y : ℕ. ∀ z : ℕ. plus (plus x y) z = plus x (plus y z)
      [   intros
        ; by induction on z
        ; [   have plus y 0 = y using plus_x_0
            ; have plus (plus x y) 0 = plus x y using plus_x_0
            ; done

          |   have plus (plus x y) (succ z) = succ (plus (plus x y) z) using plus_x_succ
            ; have plus y (succ z) = succ (plus y z) using plus_x_succ
            ; have plus x (succ (plus y z)) = succ (plus x (plus y z)) using plus_x_succ
            ; done
          ]
      ]
    thm plus_0_x : ∀ x : ℕ. plus 0 x = x
      [   intros
        ; by induction on x
        ; [    use plus_x_0
             ; done
          |    have plus 0 (succ x) = succ (plus 0 x) using plus_x_succ
             ; done
          ]
          ]
    thm plus_succ_x : ∀ x : ℕ. ∀ y : ℕ. plus (succ x) y = succ (plus x y)
      [    intros
         ; by induction on y
         ; [    have plus x 0 = x using plus_x_0
              ; have plus (succ x) 0 = succ x using plus_x_0
              ; done
           |    have plus x (succ y) = succ (plus x y) using plus_x_succ
              ; have plus (succ x) (succ y) = succ (plus (succ x) y) using plus_x_succ
              ; done
           ]
      ]
    thm plus_comm : ∀ x : ℕ. ∀ y : ℕ. plus x y = plus y x
      [   intros
        ; by induction on y
        ; [   intros
            ; have plus x 0 = x using plus_x_0
            ; have plus 0 x = x using plus_0_x
            ; done
          |   intros
            ; have plus x (succ y) = succ (plus x y) using plus_x_succ
            ; have plus (succ y) x = succ (plus y x) using plus_succ_x
            ; done
          ]
      ]

    def times : ℕ → ℕ → ℕ
    ax times_x_0 : ∀ x : ℕ. times x 0 = 0
    ax times_x_succ : ∀ x : ℕ. ∀ y : ℕ. times x (succ y) = plus x (times x y)

    thm times_0_x : ∀ x : ℕ. times 0 x = 0
      [   intros
        ; by induction on x
        ; [   use times_x_0
            ; done
          |   have times 0 (succ x) = plus 0 (times 0 x) using times_x_succ
            ; have plus 0 0 = 0 using plus_0_x
            ; done
          ]
      ]
    thm times_succ_x : ∀ x : ℕ. ∀ y : ℕ. times (succ x) y = plus y (times x y)
      [   intros
        ; by induction on y
        ; [   have times (succ x) 0 = 0 using times_x_0
            ; have times x 0 = 0 using times_x_0
            ; have plus 0 0 = 0 using plus_x_0
            ; done
          |   have times (succ x) (succ y) = plus (succ x) (times (succ x) y) using times_x_succ
            ; have plus (succ x) (times (succ x) y) = succ (plus x (times (succ x) y)) using plus_succ_x
            ; have plus (plus x y) (times x y) = plus x (plus y (times x y)) using plus_assoc
            ; have plus x y = plus y x using plus_comm
            ; have plus (plus y x) (times x y) = plus y (plus x (times x y)) using plus_assoc
            ; have times x (succ y) = plus x (times x y) using times_x_succ
            ; have plus (succ y) (times x (succ y)) = succ (plus y (times x (succ y))) using plus_succ_x
            ; done
          ]
      ]

    thm times_comm : ∀ x : ℕ. ∀ y : ℕ. times x y = times y x
      [    intros
        ;  by induction on x
        ;  [    have times 0 y = 0 using times_0_x
              ; have times y 0 = 0 using times_x_0
              ; done
           |    have times (succ x) y = plus y (times x y) using times_succ_x
              ; have times y (succ x) = plus y (times y x) using times_x_succ
              ; done
           ]
      ]

    thm times_x_plus : ∀ x : ℕ. ∀ y : ℕ. ∀ z : ℕ. times x (plus y z) = plus (times x y) (times x z)
      [   intros
        ; by induction on z
        ; [   have plus y 0 = y using plus_x_0
            ; have times x 0 = 0 using times_x_0
            ; have plus (times x y) 0 = times x y using plus_x_0
            ; done
          |   have plus y (succ z) = succ (plus y z) using plus_x_succ
            ; have times x (succ (plus y z)) = plus x (times x (plus y z)) using times_x_succ

            ; have plus (plus x (times x y)) (times x z) = plus x (plus (times x y) (times x z)) using plus_assoc
            ; have plus x (times x y) = plus (times x y) x using plus_comm
            ; have plus (plus (times x y) x) (times x z) = plus (times x y) (plus x (times x z)) using plus_assoc

            ; have times x (succ z) = plus x (times x z) using times_x_succ
            ; done
          ]
      ]
    thm times_plus_x : ∀ x : ℕ. ∀ y : ℕ. ∀ z : ℕ. times (plus x y) z = plus (times x z) (times y z)
      [   intros
        ; have times (plus x y) z = times z (plus x y) using times_comm
        ; have times z (plus x y) = plus (times z x) (times z y) using times_x_plus
        ; have times z x = times x z using times_comm
        ; have times z y = times y z using times_comm
        ; have plus (times x z) (times y z) = plus (times y z) (times x z) using plus_comm
        ; done
      ]

    thm times_assoc : ∀ x : ℕ. ∀ y : ℕ. ∀ z : ℕ. times (times x y) z = times x (times y z)
      [    intros
        ;  by induction on z
        ;  [    have times (times x y) 0 = 0 using times_x_0
              ; have times y 0 = 0 using times_x_0
              ; have times x 0 = 0 using times_x_0
              ; done
           |    have times (times x y) (succ z) = plus (times x y) (times (times x y) z) using times_x_succ
              ; have times y (succ z) = plus y (times y z) using times_x_succ
              ; have times x (plus y (times y z)) = plus (times x y) (times x (times y z)) using times_x_plus
              ; done
           ]
      ]

    def div : ℕ → { n : ℕ | ¬(n=0) } → ℕ
    ax div_by_divisor : ∀ n : ℕ. ∀ m : { x:ℕ | ¬(x = 0)}. ∀ p : ℕ. times n m = p ⇒ n = div p m
    thm div1 : ∀ n : ℕ . ∀ m : { x:ℕ | ¬(x = 0) }. div (times n m) m = n
      [   intros
        ; focus (∀ n : ℕ. ∀ m : { x:ℕ | ¬(x = 0)}. ∀ p : ℕ. times n m = p ⇒ n = div p m) using div_by_divisor
        ; [ done | id ]
        ; with n; with m; with (times n m)
        ; premise; [id | done]
        ; deactivate
        ; done
      ]

    thm nat_ind : ∀ P : ℕ→Prop. P 0 ⇒ (∀ n:ℕ. P n ⇒ P (succ n)) ⇒ ∀ n:ℕ. P n
      [   intros
        ; by induction on n
        ; [   done
          |   focus (∀ n : ℕ . P n ⇒ P (succ n)) using
            ; with n ; chain; [done | id]
            ; deactivate
            ; done
          ]
      ]

    thm galois_connection_fundamental_equiv :
      ∀ leq : ℕ→ℕ→Prop. (∀ n:ℕ. leq n n) ⇒ (∀ n:ℕ. ∀ p:ℕ. ∀ q:ℕ. leq n p ⇒ leq p q ⇒ leq n q) ⇒
        ∀ f : ℕ→ℕ. ∀ g : ℕ→ℕ.
          (∀ n:ℕ. ∀ p:ℕ. leq (f n) p ⇔ leq n (g p))
          ⇔ ((∀ n:ℕ. leq n (g (f n))) ∧ (∀ p:ℕ. leq (f (g p)) p))

    thm oops : ∀ f : { n : ℕ | n = 0} → { n : ℕ | n = 0}. ⊥
     [   intros
       ; have (f 1 = 0) using
     ]
                            |]

        -- We want to express:     ax div_spec : ∀ n : ℕ. ∀ m : { x:ℕ | ¬(x = 0) }. ∀ p : ℕ. ∃ k : ℕ. ∃ k' : ℕ. times n m + k = p ⇔ n + k' = div p m

        -- TODO later: propositions as terms of a particular type (+ some galois connection proofs, maybe?)

        -- TODO: make types more rigid. Here is the idea: instead of a term of
        -- itype ℕ→ℕ being a value of all the refinements of ℕ→ℕ, it will only
        -- be a value of types of the form { n : ℕ→ℕ | p} (and explicit subtypes
        -- of this etc…). In particular it is not necessarily an element of `{ n
        -- : ℕ | n≠0 } → ℕ`. To coerce we must use an explicit coercion `n :> {
        -- n : ℕ | n≠0 } → ℕ` (read "n seen as an element of …"). It solves the
        -- quotient problem: this way an element has only one equality applying
        -- to it. I think that I want `:>` to be equality-preserving (meaning it
        -- can't cast form a quotient type to a less quotiented type), but maybe
        -- we need a variant that can go the other way.
        --
        -- The idea is that `x :> 𝜏` is well-typed when the intrinsic type of x,
        -- is the underlying type of 𝜏. And then, you have the proof obligation,
        -- from splitting 𝜏 into a pair itype+membership predicate.

        -- TODO later: definitions

        -- TODO later: foralls in RTypes (that would give us a modicum of dependency). A possible test is lists of a given length.

        -- TODO: chaining tactics (including a prolog-like proof-search one)

        -- Big challenges:
        --
        -- - Abstracting over types: how do I say, "For any group G, such
        --   that…"? The most basic idea would be to add a universe type. But
        --   right now all types are sets. And it's very easy, to make an
        --   inconsistent theory with this sort of assumptions (a set of all
        --   sets).
        --
        -- - Totality: how do I characterise totality. Totality at `A → B` is
        --   fairly easy: `f` is total at `A→B`, if for every `x` total at `A`,
        --   `f x` total at `B`. But how do I define total at `ℕ`? From a
        --   reducibility point of view, we would like to characterise
        --   internally, the double-orthogonal of ℕ (as the mathematical set).
        --   Another question is: should we make the total elements at `A` a
        --   subset of the partial elements at `A`? Maybe, but I don't want to
        --   need totality proofs everywhere when I only use total functions. So
        --   maybe we want a rigid kind of subtype, were we can only coerce
        --   explicitly? I don't know yet.
        --
        --   In NuPrl, there is a judgement, which you can reason about,
        --   corresponding to reduction. But I'd like to not have to talk about
        --   reduction.
        --
        --   Hypothesis about totality at ℕ: we may be able to define total
        --   natural numbers as natural numbers for which induction holds. The
        --   idea would be something like: a total natural number, is an term u
        --   at ℕ, such that `∀(P:ℕ→Prop). P 0 ⇒ (∀n:ℕ. P n ⇒ P (S n)) ⇒ P u`.


  putStrLn ""
  checkProgram emptyREnv Map.empty example
  putStrLn "" -- Not sure why but Pp.putDoc doesn't actually print without this
  return ()
