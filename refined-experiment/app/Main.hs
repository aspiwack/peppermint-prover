{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
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
{-# LANGUAGE GADTs #-}
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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Capability.Source as Capability hiding (Coerce)
import Capability.Sink as Capability hiding (Coerce)
import Capability.Reader as Capability hiding (Coerce)
import qualified CongruenceClosure as CC
import Control.Applicative
import Control.Lens hiding (use)
import Control.Monad.Except
import Control.Monad.Reader hiding (ask, local)
import qualified Control.Monad.State as State
import Control.Monad.Writer.Strict
import Control.Tactic (Tactic)
import qualified Control.Tactic as Tactic
import Control.Unification (Unifiable)
import qualified Control.Unification as Unification
import qualified Control.Unification.Ranked.STVar as Unification
import qualified Control.Unification.Types as Unification
import Data.Coerce
import qualified Data.Foldable as Foldable
import Data.Functor.Compose
import qualified Data.Generics.DeBruijn as Db
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

data Entries
  = TERM
  | RTYPE

data Expr (g :: Entries) where
  -- Terms/Props
  Nat :: Integer -> Expr 'TERM
  Succ :: Expr 'TERM
  NVar :: Ident -> Expr 'TERM
  Var :: Int -> Expr 'TERM
  App :: Term -> Term -> Expr 'TERM
  Coerce :: Term -> RType -> Expr 'TERM
  StronglyCoerce :: Term -> RType -> Expr 'TERM
  PTrue :: Expr 'TERM
  PFalse :: Expr 'TERM
  PEquals :: Term -> Term -> Expr 'TERM
  PNot :: Term -> Expr 'TERM
  PAnd :: Term -> Term -> Expr 'TERM
  PImpl :: Term -> Term -> Expr 'TERM
  PEquiv :: Term -> Term -> Expr 'TERM
  PForall :: (Ann Ident) -> RType -> Term -> Expr 'TERM

  -- RTypes
  RNat :: Expr 'RTYPE
  RProp :: Expr 'RTYPE
  RSub :: (Ann Ident) -> RType -> Term -> Expr 'RTYPE
  RQuotient :: RType -> Term -> Expr 'RTYPE
  RArrow :: RType -> RType -> Expr 'RTYPE

deriving instance Eq (Expr a)
deriving instance Ord (Expr a)
deriving instance Show (Expr a)

instance Db.Syntax Expr where
  type Context Expr = Int

  -- Terms/Props
  traverseSubs _ _ t@(Var _) = pure t
  traverseSubs _ _ t@(NVar _) = pure t
  traverseSubs _ _ t@(Nat _) = pure t
  traverseSubs _ _ t@Succ = pure t
  traverseSubs on_sub env (App t u) = App <$> on_sub @'TERM env t <*> on_sub @'TERM env u
  traverseSubs on_sub env (Coerce t 𝜏) = Coerce <$> on_sub @'TERM env t <*> on_sub @'RTYPE env 𝜏
  traverseSubs on_sub env (StronglyCoerce t 𝜏) = StronglyCoerce <$> on_sub @'TERM env t <*> on_sub @'RTYPE env 𝜏
  traverseSubs _on_sub _env PTrue =
    pure PTrue
  traverseSubs _on_sub _env PFalse =
    pure PFalse
  traverseSubs on_sub env (PEquals t u) =
    PEquals <$> on_sub @'TERM env t <*> on_sub @'TERM env u
  traverseSubs on_sub env (PNot p) =
    PNot <$> on_sub @'TERM env p
  traverseSubs on_sub env (PImpl p q) =
    PImpl <$> on_sub @'TERM env p <*> on_sub @'TERM env q
  traverseSubs on_sub env (PEquiv p q) =
    PEquiv <$> on_sub @'TERM env p <*> on_sub @'TERM env q
  traverseSubs on_sub env (PAnd p q) =
    PAnd <$> on_sub @'TERM env p <*> on_sub @'TERM env q
  traverseSubs on_sub env (PForall x 𝜏 p) =
    PForall x <$> on_sub @'RTYPE env 𝜏 <*> on_sub @'TERM (1+env) p

  -- RTypes
  traverseSubs _on_sub _env RNat =
    pure RNat
  traverseSubs _on_sub _env RProp =
    pure RProp
  traverseSubs on_sub env (RArrow 𝜏 𝜇) =
    RArrow <$> on_sub @'RTYPE env 𝜏 <*> on_sub @'RTYPE env 𝜇
  traverseSubs on_sub env (RSub x 𝜏 p) =
    RSub x <$> on_sub @'RTYPE env 𝜏 <*> on_sub @'TERM (env+1) p
  traverseSubs on_sub env (RQuotient 𝜏 r) =
    RQuotient <$> on_sub @'RTYPE env 𝜏 <*> on_sub @'TERM env r

type Term = Expr 'TERM

data IType
  = INat
  | IProp
  | IArrow IType IType
  deriving (Eq)

type RType = Expr 'RTYPE

-- | An 'RType' which is not a subtype.
newtype BasalType
  = UnsafeMkBasalType { embedBasalType :: RType }
  deriving (Eq, Show)

internTerm' :: Concrete.Term -> Term
internTerm' u = internTerm Map.empty u

internIType' :: Concrete.IType -> IType
internIType' 𝜏 = internIType Map.empty 𝜏

internRType' :: Concrete.RType -> RType
internRType' 𝜏 = internRType Map.empty 𝜏

internProp' :: Concrete.Term -> Term
internProp' p = internProp Map.empty p

internTerm :: Map Ident Int -> Concrete.Term -> Term
internTerm subst (Concrete.Var x) = case Map.lookup x subst of
  Just i -> Var i
  Nothing -> NVar x
internTerm _ (Concrete.Nat n) = Nat n
internTerm subst (Concrete.App u v) = App (internTerm subst u) (internTerm subst v)
internTerm subst (Concrete.Coerce u 𝜏) = Coerce (internTerm subst u) (internRType subst 𝜏)
internTerm subst (Concrete.StronglyCoerce u 𝜏) = StronglyCoerce (internTerm subst u) (internRType subst 𝜏)
internTerm _ Concrete.Succ = Succ
internTerm _ Concrete.PTrue = PTrue
internTerm _ Concrete.PFalse = PFalse
internTerm subst (Concrete.PEquals u v) = PEquals (internTerm subst u) (internTerm subst v)
internTerm subst (Concrete.PNot p) = PNot (internTerm subst p)
internTerm subst (Concrete.PAnd p q) = PAnd (internTerm subst p) (internTerm subst q)
internTerm subst (Concrete.PImpl p q) = PImpl (internTerm subst p) (internTerm subst q)
internTerm subst (Concrete.PEquiv p q) = PEquiv (internTerm subst p) (internTerm subst q)
internTerm subst (Concrete.PForall binds p) = internForall subst binds p

internForall :: Map Ident Int -> Concrete.Binders -> Concrete.Term -> Term
internForall subst binds p = case binds of
    Concrete.BOne bind ->
      internOne' bind (\s -> internTerm s p) subst
    Concrete.BMany bs ->
      internMany (map (\(Concrete.BParen b) -> b) bs) subst
  where
    internOne :: Concrete.BindIdents -> RType -> (Map Ident Int -> Term) -> Map Ident Int -> Term
    internOne (Concrete.BSingle x) 𝜎 k subst' =
      PForall (Ann x) 𝜎 (k (addBinder x subst'))
    internOne (Concrete.BMore x xs') 𝜎 k subst' =
      PForall (Ann x) 𝜎 (internOne xs' 𝜎 k (addBinder x subst'))

    internOne' :: Concrete.Binder -> (Map Ident Int -> Term) -> Map Ident Int -> Term
    internOne' (Concrete.Bind xs 𝜏) k = internOne xs (internRType subst 𝜏) k

    internMany :: [Concrete.Binder] -> Map Ident Int -> Term
    internMany = foldr internOne' (\s -> internTerm s p)


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
internRType subst (Concrete.RQuotient 𝜏 r) =
  RQuotient (internRType subst 𝜏) (internTerm subst r)

internProp :: Map Ident Int -> Concrete.Term -> Term
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
externTerm (Coerce u 𝜏) = Concrete.Coerce (externTerm u) (externRType 𝜏)
externTerm (StronglyCoerce u 𝜏) = Concrete.StronglyCoerce (externTerm u) (externRType 𝜏)
externTerm PTrue = Concrete.PTrue
externTerm PFalse = Concrete.PFalse
externTerm (PEquals u v) = Concrete.PEquals (externTerm u) (externTerm v)
externTerm (PNot p) = Concrete.PNot (externTerm p)
externTerm (PAnd p q) = Concrete.PAnd (externTerm p) (externTerm q)
externTerm (PImpl p q) = Concrete.PImpl (externTerm p) (externTerm q)
externTerm (PEquiv p q) = Concrete.PEquiv (externTerm p) (externTerm q)
externTerm (PForall (Ann x) 𝜏 p) =
  Concrete.PForall (Concrete.BOne (Concrete.Bind (Concrete.BSingle x) (externRType 𝜏))) (externTerm (substitute [NVar x] p))

externIType :: IType -> Concrete.IType
externIType INat = Concrete.INat
externIType IProp = Concrete.IProp
externIType (IArrow 𝜏 𝜎) = Concrete.IArrow (externIType 𝜏) (externIType 𝜎)

externRType :: RType -> Concrete.RType
externRType RNat = Concrete.RNat
externRType RProp = Concrete.RProp
externRType (RArrow 𝜏 𝜎) = Concrete.RArrow (externRType 𝜏) (externRType 𝜎)
externRType (RSub (Ann x) 𝜏 u) =
  Concrete.RSub x (externRType 𝜏) (externProp (substitute [NVar x] u))
externRType (RQuotient 𝜏 r) =
  Concrete.RQuotient (externRType 𝜏) (externTerm r)

externProp :: Term -> Concrete.Term
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
-- Smart constructors for props

pand :: Term -> Term -> Term
pand PTrue p = p
pand p PTrue = p
pand p q = p `PAnd` q

pimpl :: Term -> Term -> Term
pimpl PTrue p = p
pimpl _ PTrue = PTrue
pimpl p q = p `PImpl` q

pforall :: Ann Ident -> RType -> Term -> Term
pforall _ _ PTrue = PTrue
pforall x 𝜏 p = PForall x 𝜏 p

mkCoerce :: Term -> RType -> Term
mkCoerce u 𝜏 = Coerce (stripCoercions u) 𝜏
  where
    stripCoercions :: Term -> Term
    stripCoercions (Coerce v _) = stripCoercions v
    stripCoercions v = v

stronglyCoerce :: Term -> RType -> Term
stronglyCoerce u 𝜏 = StronglyCoerce (stripCoercions u) 𝜏
  where
    stripCoercions :: Term -> Term
    stripCoercions (Coerce v _) = stripCoercions v
    stripCoercions (StronglyCoerce v _) = stripCoercions v
    stripCoercions v = v

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

check :: TcM a -> (a -> Tac) -> Tac
check chk tac = Tactic.Mk $ \k g@Goal{bound_variables} -> Compose $ do
  glbls <- view #globals
  tenv <- view #thms
  let env =
        emptyREnv
        & (\e -> Map.foldrWithKey addGlobal e glbls)
        & (\e -> foldr (uncurry addLocal) e bound_variables)
  let (the_prop, potential_proof_obligations) = runTcM env tenv chk
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
subsumes :: Term -> Term -> Bool
subsumes h0 c0 = Unification.runSTRBinding $ go [] h0 c0
  where
    go subst (PForall _ _ p) c = do
      v <- Unification.freeVar
      go (v:subst) p c
    go subst u v = do
      let
        u' = toUTerm subst u
        v' = toUTerm [] v
      unify' u' v'

    toUTerm :: forall v. [v] -> Term -> Unification.UTerm TermView v
    toUTerm subst (Var i) = case i < length subst of
      True -> Unification.UVar (subst !! i)
      False -> Unification.UTerm (VVar i)
    toUTerm subst t = Unification.UTerm $ toUTerm subst <$> (CC.view t)

thm_subsumption :: MonadPlus m => Goal -> m Theorem
thm_subsumption g@(Goal {hyps, stoup=Nothing, concl}) = do
  guard (any (`subsumes` concl) hyps)
  return $ Proved g
thm_subsumption (Goal {stoup=Just _}) = mzero

subsumption :: MonadPlus m => Tactic Goal Theorem m
subsumption = Tactic.Mk $ \_ g -> Compose $ pure <$> thm_subsumption g

goalTerms :: Applicative f => (Term -> f Term) -> Goal -> f Goal
goalTerms f (Goal {bound_variables, hyps, stoup, concl}) =
  Goal bound_variables <$> traverse f hyps <*> traverse f stoup <*> f concl

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
      slurped = CC.exec CC.empty $ do
        goalIterTerms CC.add g
        CC.add PTrue
      learned = CC.exec slurped $ forM_ hyps $ \h ->
          case h of
            PEquals u v -> CC.merge u v
            p -> CC.merge p PTrue
      equiv u v = CC.eval learned $ CC.equivalent u v

      inconsistent_hyp (PNot (PEquals u v)) = equiv u v
      inconsistent_hyp _ = False

      inconsistent = any inconsistent_hyp hyps
      concl_true = case concl of
          PEquals u v -> equiv u v
          p -> equiv p PTrue
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

addHyp :: Term -> [Term] -> [Term]
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
            & over #bound_variables ((x, baseType 𝜏) :)
            & over (#hyps . traverse) (substitute [NVar x'])
            & over #hyps (addHyp (topConstraint 𝜏 (NVar x')))
            & set #concl (substitute [NVar x']p)
        in
        getCompose $ prove g <$> k sub
    else
        let
          x' = avoid x (freeVarsGoal g ++ Map.keys glbls)
          sub = g
            & over #bound_variables ((x', baseType 𝜏) :)
            & over #hyps (addHyp (topConstraint 𝜏 (NVar x')))
            & set #concl (substitute [NVar x'] p)
        in
        getCompose $ prove g <$> k sub
  _ -> Compose $ doFail g

decompHyp :: Term -> [Term]
decompHyp (PAnd p q) = decompHyp p ++ decompHyp q
decompHyp p = [p]

decomp :: Tac
decomp = Tactic.Mk $ \(validating -> k) g@Goal{hyps} ->
  let
    sub = g & set #hyps [ h' | h <- hyps, h' <- decompHyp h ]
  in
  prove g <$> k sub

max_intros :: Tac
max_intros = decomp `Tactic.thn` Main.repeat intro

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
   instantiate :: Term -> [Term] -> Term
   instantiate (PForall _ _ p) (u:us) = instantiate (substitute [u] p) us
     -- TODO: check the types!
   instantiate p [] = p
   instantiate _ _ = error "Not enough foralls."

have0 :: Term -> Tac
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

have :: Term -> [Ident] -> Tac
have p lems = have0 p `Tactic.dispatch` [dischargeWith lems, Tactic.id]

-- | Induction on the natural numbers @ℕ@
induction :: Ident -> Tac
induction x = Tactic.Mk $ \ k g@(Goal {stoup, concl}) ->
  case stoup of
    Nothing ->
      let
        sub_0 = g
          & over #concl (substituteN x (Nat 0))
        sub_succ = g
          & over #hyps (addHyp concl)
          & over #concl (substituteN x (App Succ (NVar x)))
      in
     (\(Proved _) (Proved _) -> Proved g)
       <$> k sub_0
       <*> k sub_succ
    Just _ -> Compose $ doFail g

-- TODO: refactor together with have0. Somehow.
focus0 :: Term -> Tac
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

focus :: Term -> [Ident] -> Tac
focus p lems = focus0 p `Tactic.dispatch` [dischargeWith lems, Tactic.id]

with :: Term -> Tac
with u = Tactic.Mk $ \(validating -> k) g@(Goal {stoup}) ->
  case stoup of
     -- TODO: check the type!
    Just (PForall _ _𝜎 p) ->
      let
        sub = g
          & set #stoup (Just (substitute [u] p))
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

split :: Tac
split = Tactic.Mk $ \(validating -> k) g@(Goal{concl}) ->
  case concl of
    PEquiv p q ->
      let
        l2r = g & set #concl (p `PImpl` q)
        r2l = g & set #concl (q `PImpl` p)
      in
      prove g <$> k l2r <*> k r2l
    PAnd p q ->
      let
        l2r = g & set #concl p
        r2l = g & set #concl q
      in
      prove g <$> k l2r <*> k r2l
    _ -> Compose $ doFail g

left :: Tac
left = Tactic.Mk $ \(validating -> k) g@(Goal{stoup}) ->
  case stoup of
    Just (PEquiv p q) ->
      let
        sub = g & set #stoup (Just (p `PImpl` q))
      in
      prove g <$> k sub
    _ -> Compose $ doFail g

right :: Tac
right = Tactic.Mk $ \(validating -> k) g@(Goal{stoup}) ->
  case stoup of
    Just (PEquiv p q) ->
      let
        sub = g & set #stoup (Just (q `PImpl` p))
      in
      prove g <$> k sub
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

-- TODO: can we implement this tactic in a less horrible way?
quotient :: Tac
quotient = Tactic.Mk $ \(validating -> k) g@(Goal {bound_variables, concl}) ->
  case concl of
    PEquals u v -> Compose $ do
      -- TODO: lot of duplicate code with the check tactic above which requires
      -- refactoring.
      glbls <- view #globals
      tenv <- view #thms
      let env =
           emptyREnv
           & (\e -> Map.foldrWithKey addGlobal e glbls)
           & (\e -> foldr (uncurry addLocal) e bound_variables)
      let (type_of_u, _) = runTcM env tenv (typeInferRefinementTerm u)
        -- ignoring the proof obligation, because I assume the goal to be
        -- already well typed.
      case baseType' type_of_u of
        RQuotient _ r ->
          let
            (type_of_r, _) = runTcM env tenv (typeInferRefinementTerm r)
          in
          case baseType' type_of_r of
            RArrow lowered_type _ ->
              let
                sub = g
                  & set #concl (r `App` (stronglyCoerce u lowered_type) `App` (stronglyCoerce v lowered_type))
              in
              getCompose $ prove g <$> k sub
            _ -> error "quotient tactic on ill-typed term"
        _ -> doFail g
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
  | VCoerce a RType
  | VStronglyCoerce a RType
  | VTrue
  | VFalse
  | VEquals a a
  | VNot a
  | VAnd a a
  | VImpl a a
  | VEquiv a a
  | VForall (Ann Ident) RType Term
  deriving (Eq, Ord, Functor, Foldable, Traversable, Show)

-- I took this from Will Fancher's https://elvishjerricco.github.io/2017/03/23/applicative-sorting.html
unsafeReifyList :: (HasCallStack, Traversable t) => t a -> [b] -> t b
unsafeReifyList t = State.evalState (traverse reify t)
  where
    reify _ =
      State.get >>= \case
        [] -> error "The number of argument should be exactly the length of t."
        b:bs -> do
          State.put bs
          return b

appMaybe :: (Eq (t ()), Traversable t) => (a -> b -> c) -> t a -> t b -> Maybe (t c)
appMaybe f t u =
  if void t == void u then
    Just $
      unsafeReifyList t $ zipWith f (Foldable.toList t) (Foldable.toList u)
  else
    Nothing

traverse2 :: (Eq (t ()), Traversable t, Applicative f) => (a -> b -> f c) -> t a -> t b -> Maybe (f (t c))
traverse2 f t u = fmap sequenceA (appMaybe f t u)

-- TODO: right now CC considers that `:>>` respects equality, I'm pretty
-- sure. But it shouldn't. I'm not sure how to permit pattern-matching using
-- unification, while considering `u :>> t` as an opaque term for CC, unless I
-- use two different view types. Which is a bit annoying.
instance CC.LiftRelation TermView where
  liftRelation r t u =
    case traverse2 (\a b -> Compose (Const . All <$> r a b)) t u of
      Just b -> getAll . getConst <$> getCompose b
      Nothing -> pure False

instance CC.Unfix Term TermView where
  view (Var x) = VVar x
  view (NVar x) = VNVar x
  view (Nat n) = VNat n
  view Succ = VSucc
  view (App u v) = VApp u v
  view (Coerce u 𝜏) = VCoerce u 𝜏
  view (StronglyCoerce u 𝜏) = VStronglyCoerce u 𝜏
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
  zipMatch = appMaybe (\t u -> Right (t, u))

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
underlyingIType (RQuotient t _) = underlyingIType t

baseType :: RType -> BasalType
baseType (RSub _ t _) = baseType t
baseType t = UnsafeMkBasalType t

baseType' :: RType -> RType
baseType' = embedBasalType . baseType

chooseAVariableNameBasedOn :: RType -> Ident
chooseAVariableNameBasedOn _ = Ident "x"

constraint :: RType -> Term -> Term
constraint RNat _ = PTrue
constraint RProp _ = PTrue
constraint (RArrow t u) f =
  let x = Ann (chooseAVariableNameBasedOn t) in
  pforall x t (constraint t (Var 0) `pimpl` constraint u (f `App` (Var 0)))
constraint (RSub _ t p) e = (constraint t e) `pand` (substitute [e] p)
constraint (RQuotient t _) e = constraint t e

-- | Constraint over the 'baseType'. That is, @t@ is essentially @{ x : baseType
-- t | topConstraint t x }@.
topConstraint :: RType -> Term -> Term
topConstraint (RSub _ t p) e = (topConstraint t e) `pand` (substitute [e] p)
topConstraint _ _ = PTrue

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

freeVars :: Expr e -> [Ident]
freeVars (NVar x) = [ x ]
freeVars t = Db.foldSubs_ freeVars t

substitute :: [Term] -> Expr e -> Expr e
substitute subst (PForall y 𝜏 p) =
  PForall y 𝜏 (substitute (shift subst) p)
substitute subst (RSub y 𝜏 p) =
  RSub y 𝜏 (substitute (shift subst) p)
substitute subst u@(Var i) = Maybe.fromMaybe u $ preview (ix i) subst
substitute subst t = Db.mapSubs_ (substitute subst) t

substituteN :: Ident -> Term -> Expr e -> Expr e
substituteN x t u@(NVar y)
  | x == y = t
  | otherwise = u
substituteN x t e = Db.mapSubs_ (substituteN x t) e

liftTerm :: Term -> Term
liftTerm = substitute (map Var [1..])

shift :: [Term] -> [Term]
shift subst = Var 0 : map liftTerm subst

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
typeInferIntrinsicTerm env (Coerce u _) = do
  typeInferIntrinsicTerm env u
typeInferIntrinsicTerm env (StronglyCoerce u _) = do
  typeInferIntrinsicTerm env u
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
decompArrow :: HasCallStack => RType -> (RType, RType, Term -> Term)
decompArrow (u `RArrow` t) = (u, t, const PTrue)
decompArrow (RSub _ u p) =
  let !(v, t, q) = decompArrow u in
  (v, t, \e -> q e `pand` substitute [e] p)
decompArrow _ = error "This has to be an arrow"

data LocalisedRType
  = Local BasalType
  | Global RType
  deriving (Generic, Show)

projectLocalised :: LocalisedRType -> RType
projectLocalised (Local a) = embedBasalType a
projectLocalised (Global a) = a

data REnv = REnv
  { named :: Map Ident LocalisedRType
  , db :: [RType]}
  deriving (Generic, Show)

emptyREnv :: REnv
emptyREnv = REnv {named=Map.empty, db=[]}

rlookupNamed :: Ident -> REnv -> Maybe LocalisedRType
rlookupNamed x env = Map.lookup x (env ^. #named)

rlookupDb :: Int -> REnv -> Maybe RType
rlookupDb i env = preview (ix i) (env ^. #db)

(!) :: HasCallStack => REnv -> Ident -> RType
(!) env x = case Map.lookup x (env ^. #named) of
  Just 𝜏 -> projectLocalised 𝜏
  Nothing -> error $ "Ident " ++ show x ++ " not in REnv " ++ show env

addLocal :: Ident -> BasalType -> REnv -> REnv
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
  { bound_variables :: [(Ident, BasalType)]
  , hyps :: [Term]
  , stoup :: Maybe Term
  , concl :: Term
  }
  deriving (Eq, Generic)
-- /!\ DANGER MR. ROBINSON: `Eq` instance not compatible with 𝛼-conversion

freeVarsGoal :: Goal -> [Ident]
freeVarsGoal (Goal {bound_variables, hyps, stoup, concl}) =
  concat
    [ map fst bound_variables
    , concatMap freeVars hyps
    , concatMap freeVars stoup
    , freeVars concl
    ]

ppBoundVar :: (Ident, BasalType) -> Pp.Doc Pp.AnsiStyle
ppBoundVar (a, b) = pp a Pp.<+> ":" Pp.<+> pp (externRType (embedBasalType b))

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

data TcContext = TcContext
  { hyps :: [Term]
  , env :: REnv
  }
  deriving (Generic)

newtype TcM a = MkTcM (ReaderT TcContext (State.State [Goal]) a)
  deriving (Functor, Applicative, Monad)
  deriving (HasSource "hyps" [Term], HasReader "hyps" [Term]) via Field "hyps" "context" (Capability.MonadReader (ReaderT TcContext (State.State [Goal])))
  deriving (HasSource "env" REnv, HasReader "env" REnv) via Field "env" "context" (Capability.MonadReader (ReaderT TcContext (State.State [Goal])))
  deriving (HasSink "constraint" Goal) via (Capability.SinkStack (Capability.MonadState (ReaderT TcContext (State.State [Goal]))))

data DischargeStatus = Discharged | Open
  deriving (Eq)

runTcM :: REnv -> ThmEnv -> TcM a -> (a, [(Goal, DischargeStatus)])
runTcM env thms (MkTcM act) =
    over _2 reverse $ over (_2 . mapped) try_discharge $ flip State.runState [] $ runReaderT act starting_context
  where
    globals = toMapOf globalsREnv env
    starting_context = TcContext
      { hyps = []
      , env
      }
    try_discharge :: Goal -> (Goal, DischargeStatus)
    try_discharge g =
      case runReaderT (Tactic.proveWith (\_ -> mzero) discharge g) (ProofEnv {thms, globals}) of
        Success (Proved g') | g == g' -> (g, Discharged)
        _ -> (g, Open)

runTcM' :: REnv -> ThmEnv -> TcM () -> [(Goal, DischargeStatus)]
runTcM' env thms act = snd $ runTcM env thms act

emit :: Term -> TcM ()
emit PTrue = return ()
emit concl0 = do
  env <- ask @"env"
  -- TODO: there is a bug here, in case of shadowing. Where the shadowing
  -- variable, will appear to bind the shadowed variables in some hypotheses,
  -- yielding incorrectly typed goals.
  let local_variables = env & itoListOf (#named .> itraversed <. #_Local)
  -- TODO: generating names for the debruijns should have proper shadowing
  let dbs = env & itoListOf (#db .> itraversed <. to baseType) & over (traverse . _1) (\i -> Ident ("db"++show i))
  let subst = map (NVar . fst) dbs
  let bound_variables = local_variables ++ dbs
  hyps0 <- ask @"hyps"
  let hyps = map (substitute subst) hyps0
  let concl = substitute subst concl0
  yield @"constraint" $ Goal {bound_variables, hyps, concl, stoup=Nothing}

assuming :: Term -> TcM a -> TcM a
assuming PTrue = id
assuming p = local @"hyps" (p :)

shadowing :: Ident -> Ident -> TcM a -> TcM a
shadowing x x' act =
  local @"hyps" (map (substituteN x (NVar x'))) act

-- | Assumes that @'typeInferIntrinsicTerm' e == Just ('underlyingIType' t)@.
typeCheckRefinementTerm :: HasCallStack => Term -> RType -> TcM ()
typeCheckRefinementTerm e t = do
  type_of_e <- typeInferRefinementTerm e
  assuming (topConstraint type_of_e e) $
    emit $ topConstraint t e

typeInferRefinementTerm :: HasCallStack => Term -> TcM RType
typeInferRefinementTerm (Var i) = do
  env <- ask @"env"
  return $ Maybe.fromJust $ rlookupDb i env
typeInferRefinementTerm (NVar x) = do
  env <- ask @"env"
  return $ env ! x
typeInferRefinementTerm (Nat _) = return $ RNat
typeInferRefinementTerm Succ = return $ internRType' [Concrete.rType|ℕ → ℕ|]
typeInferRefinementTerm (f `App` e) = do
  type_of_f <- typeInferRefinementTerm f
  let (type_of_arg, type_of_return, given_of_f) = decompArrow type_of_f
  assuming (given_of_f f) $ do
    typeCheckRefinementTerm e type_of_arg
    return type_of_return
typeInferRefinementTerm (Coerce u 𝜏) = do
  typeCheckRefinementTerm u (baseType' 𝜏)
  emit (topConstraint 𝜏 u)
  return 𝜏
typeInferRefinementTerm (StronglyCoerce u 𝜏) = do
  env <- ask @"env"
  let ienv = underlyingITypes env
  case typeCheckIntrinsicTerm ienv u (underlyingIType 𝜏) of
    False -> error "Incorrect underlying type"
    True -> do
      emit (constraint 𝜏 u)
      -- Probably we want to add what we know about `u` from its rtype in the
      -- context. Though it does assume that I'm able to infer the type for it,
      -- which I currently can, probably, but it may not be a robust assumption.
      return 𝜏
typeInferRefinementTerm PTrue = do
  return RProp
typeInferRefinementTerm PFalse = do
  return RProp
typeInferRefinementTerm (PNot p) = do
  typeCheckProposition p
  return RProp
typeInferRefinementTerm (PAnd p q) = do
  typeCheckProposition p
  typeCheckProposition q
  return RProp
typeInferRefinementTerm (PImpl p q) = do
  typeCheckProposition p
  assuming p $
    typeCheckProposition q
  return RProp
typeInferRefinementTerm (PEquiv p q) = do
  typeCheckProposition p
  assuming p $
    typeCheckProposition q
  return RProp
typeInferRefinementTerm (PForall _ t p) = do
  local @"env" (pushDb t) $
    typeCheckProposition p
  return RProp
typeInferRefinementTerm (u `PEquals` v) = do
  type_of_u <- typeInferRefinementTerm u
  typeCheckRefinementTerm v (baseType' type_of_u)
  return RProp

typeCheckProposition' :: HasCallStack => Concrete.Term -> TcM Term
typeCheckProposition' p = do
  let p' = internProp' p
  typeCheckProposition p'
  return p'

-- This type is a lie: typeCheckProposition should fail gracefully if the
-- intrinsic type is faulty somewhere.
typeCheckProposition :: HasCallStack => Term -> TcM ()
typeCheckProposition p = typeCheckRefinementTerm p RProp

type ThmEnv = Map Ident Term

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
      let (p', goals) = runTcM env tenv $ typeCheckProposition' p
      Pp.putDoc $ ppGoals goals
      go env (Map.insert z p' tenv) decls
    go env tenv (Concrete.Theorem z p tacs : decls) = do
      Pp.putDoc $ pp (Concrete.Theorem z p Concrete.NothingTacAlt)
      putStrLn ""
      let
        (p_tc'd, goals) = runTcM env tenv $ do
          p' <- typeCheckProposition' p
          emit p'
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
evalTac (Concrete.THave p lems) = check (typeCheckProposition' p) $ \p' -> have p' lems
evalTac (Concrete.TFocus p lems) = check (typeCheckProposition' p) $ \p' -> focus p' lems
evalTac (Concrete.TWith u) = with (internTerm' u)
evalTac (Concrete.TChain) = chain
evalTac (Concrete.TSplit) = split
evalTac (Concrete.TLeft) = left
evalTac (Concrete.TRight) = right
evalTac (Concrete.TDeactivate) = deactivate
evalTac (Concrete.TQuotient) = quotient
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
  Pp.putDoc $ pp (externProp (substituteN (Ident "y") (internTerm' [Concrete.term|x|]) (internProp' [Concrete.term|∀ x : ℕ. x=y|])))
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
        ; chain; [done | id]
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
      ∀ leq : ℕ→ℕ→Prop. (∀ n:ℕ. leq n n) ⇒ (∀ n p q : ℕ. leq n p ⇒ leq p q ⇒ leq n q) ⇒
        ∀ (f : ℕ→ℕ) (g : ℕ→ℕ).
          (∀ n m : ℕ. leq n m ⇒ leq (f n) (f m)) ⇒
          (∀ p q : ℕ. leq p q ⇒ leq (g p) (g q)) ⇒
          ((∀ n p:ℕ. leq (f n) p ⇔ leq n (g p))
          ⇔ ((∀ n:ℕ. leq n (g (f n))) ∧ (∀ p:ℕ. leq (f (g p)) p)))
      [   intros
        ; split
        ; intros
        ; [   split
            ; [   intros
                ; focus ( ∀ n : ℕ . ∀ p : ℕ . leq (f n) p ⇔ leq n (g p) ) using
                ; with n; with (f n); left; chain; [done|id]
                ; deactivate
                ; done
              |   intros
                ; focus ( ∀ n : ℕ . ∀ p : ℕ . leq (f n) p ⇔ leq n (g p) ) using
                ; with (g p); with p; right; chain; [done|id]
                ; deactivate
                ; done
              ]
          |   split
            ; [   intros
                ; focus ( ∀ p : ℕ . ∀ q : ℕ . leq p q ⇒ leq (g p) (g q) ) using
                ; with (f n); with p; chain; [done|id]
                ; deactivate
                ; focus ( ∀ n : ℕ . ∀ p : ℕ . ∀ q : ℕ . leq n p ⇒ leq p q ⇒ leq n q ) using
                ; with n; with (g (f n)); with (g p); chain; [done|id]; chain; [done|id]
                ; deactivate
                ; done
              |   intros
                ; focus ( ∀ n : ℕ . ∀ m : ℕ . leq n m ⇒ leq (f n) (f m) ) using
                ; with n; with (g p); chain; [done|id]
                ; deactivate
                ; focus (  ∀ n : ℕ . ∀ p : ℕ . ∀ q : ℕ . leq n p ⇒ leq p q ⇒ leq n q ) using
                ; with (f n); with (f (g p)); with p; chain; [done|id]; chain; [done|id]
                ; deactivate
                ; done
              ]
          ]
      ]

    def Tot : ℕ → ℕ → Prop
    ax Tot_def : ∀ x y:ℕ. Tot x y

    thm tot_tot : ∀ x y : ℕ/Tot. x = y
     [   intros
       ; quotient
       ; have (Tot (x :>> ℕ) (y :>> ℕ)) using Tot_def
       ; done
     ]

    def Mod2 : ℕ → ℕ → Prop
    ax Mod2_def : ∀ x:ℕ. Mod2 x (succ (succ x))

    ax eq_scoerce : ∀ x:ℕ. (x :>> ℕ) = x

    thm mod2_0_2 : (0 :> ℕ/Mod2) = (succ (succ 0) :> ℕ/Mod2)
     [   quotient
       ; have (0 :>> ℕ) = 0 using eq_scoerce
       ; have (succ (succ 0) :>> ℕ) = succ (succ 0) using eq_scoerce
       ; have Mod2 0 (succ (succ 0)) using Mod2_def
       ; done
     ]

    thm mod2_2_4 : (succ (succ 0) :> ℕ/Mod2) = (succ (succ (succ (succ 0))) :> ℕ/Mod2)

    thm mod2_0_4 : (0 :> ℕ/Mod2) = (succ (succ (succ (succ 0))) :> ℕ/Mod2)
     [   have (0 :> ℕ/Mod2) = (succ (succ 0) :> ℕ/Mod2) using mod2_0_2
       ; have (succ (succ 0) :> ℕ/Mod2) = (succ (succ (succ (succ 0))) :> ℕ/Mod2) using mod2_2_4
       ; done
     ]

    thm mod2_even : ∀ x:ℕ. (plus x x :> ℕ/Mod2) = (0 :> ℕ/Mod2)

    thm ops : ∀ (f : { n : ℕ | ¬(n=0) } → ℕ) (n : { n : ℕ | ¬(n=0)}). f n = 0

    thm oops : ∀ f : { n : ℕ | n = 0} → { n : ℕ | n = 0}. ⊥
     [   intros
       ; have (f 1 = 0) using
     ]
                            |]

        -- We want to express:     ax div_spec : ∀ n : ℕ. ∀ m : { x:ℕ | ¬(x = 0) }. ∀ p : ℕ. ∃ k : ℕ. ∃ k' : ℕ. times n m + k = p ⇔ n + k' = div p m

        -- TODO !!quickly!! have a way to name forall intros

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
        --   Trying to add a full-blown universe would bring to close to
        --   dependent types, and the problems there that we are trying to
        --   avoid. However, Andrew Pitts teaches us in _Polymorphism is Set
        --   Theoretic, constructively_ that we can make a universe U of types
        --   which is stable by U-indexed product (this gives a model of System
        --   F (a la Church, _i.e._ with explicit type abstractions and
        --   applications)). We can surely (proof left as an exercise)
        --   generalise this to quantifying over modules (of a given type),
        --   which will let us quantify over groups and such. Again: explicit
        --   module abstractions and applications. However, we won't just do
        --   functors, like in ML, we want to have functions abstracted over
        --   modules.
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
