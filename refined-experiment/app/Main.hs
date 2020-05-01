{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
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
import qualified Data.Text.Prettyprint.Doc as Pp
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as Pp
import GHC.Generics (Generic)
import GHC.Stack
import Language.LBNF.Runtime
import Refined

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

termSubs :: Applicative f => ([Ident] -> Term -> f Term) -> [Ident] -> Term -> f Term
termSubs _ _ t@(Var _) = pure t
termSubs _ _ t@(Nat _) = pure t
termSubs _ _ t@Succ = pure t
termSubs on_term env (App t u) = App <$> on_term env t <*> on_term env u

rtypeSubs ::
  Applicative f =>
  ([Ident] -> RType -> f RType) ->
  ([Ident] -> Prop -> f Prop) ->
  [Ident] -> RType -> f RType
rtypeSubs _on_rtype _on_prop _env RNat =
  pure RNat
rtypeSubs on_rtype _on_prop env (RArrow 𝜏 𝜇) =
  RArrow <$> on_rtype env 𝜏 <*> on_rtype env 𝜇
rtypeSubs on_rtype on_prop env (RSub x 𝜏 p) =
  RSub x <$> on_rtype env 𝜏 <*> on_prop (x:env) p

propSubs ::
  Applicative f =>
  ([Ident] -> Term -> f Term) ->
  ([Ident] -> RType -> f RType) ->
  ([Ident] -> Prop -> f Prop) ->
  [Ident] -> Prop -> f Prop
propSubs _on_term _on_rtype _on_prop _env PTrue =
  pure PTrue
propSubs _on_term _on_rtype _on_prop _env PFalse =
  pure PFalse
propSubs on_term _on_rtype _on_prop env (PEquals t u) =
  PEquals <$> on_term env t <*> on_term env u
propSubs _on_term _on_rtype on_prop env (PNot p) =
  PNot <$> on_prop env p
propSubs _on_term _on_rtype on_prop env (PImpl p q) =
  PImpl <$> on_prop env p <*> on_prop env q
propSubs _on_term _on_rtype on_prop env (PAnd p q) =
  PAnd <$> on_prop env p <*> on_prop env q
propSubs _on_term on_rtype on_prop env (PForall x 𝜏 p) =
  PForall x <$> on_rtype env 𝜏 <*> on_prop (x:env) p

termSubs_ :: Applicative f => (Term -> f Term) -> Term -> f Term
termSubs_ on_term = termSubs (\_ -> on_term) []

rtypeSubs_ ::
  Applicative f =>
  (RType -> f RType) ->
  (Prop -> f Prop) ->
  RType -> f RType
rtypeSubs_ on_rtype on_prop = rtypeSubs (\_ -> on_rtype) (\_ -> on_prop) []

propSubs_ ::
  Applicative f =>
  (Term -> f Term) ->
  (RType -> f RType) ->
  (Prop -> f Prop) ->
  Prop -> f Prop
propSubs_ on_term on_rtype on_prop =
  propSubs (\_ -> on_term) (\_ -> on_rtype) (\_ -> on_prop) []

termFoldSubs :: forall a. Monoid a => ([Ident] -> Term -> a) -> [Ident] -> Term -> a
termFoldSubs = coerce $ termSubs @(Const a)

rtypeFoldSubs ::
  forall a. Monoid a =>
  ([Ident] -> RType -> a) ->
  ([Ident] -> Prop -> a) ->
  [Ident] -> RType -> a
rtypeFoldSubs = coerce $ rtypeSubs @(Const a)

propFoldSubs ::
  forall a. Monoid a =>
  ([Ident] -> Term -> a) ->
  ([Ident] -> RType -> a) ->
  ([Ident] -> Prop -> a) ->
  [Ident] -> Prop -> a
propFoldSubs = coerce $ propSubs @(Const a)

termMapSubs_ :: (Term -> Term) -> Term -> Term
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

pforall :: Ident -> RType -> Prop -> Prop
pforall _ _ PTrue = PTrue
pforall x 𝜏 p = PForall x 𝜏 p

------------------------------------------------------------------------------
-- Proofs

-- TODO: make into an abstract type
newtype Theorem = Proved Goal

checkProp :: (REnv -> TcM Prop) -> (Prop -> Tac) -> Tac
checkProp chk tac = Tactic.Mk $ \k g@Goal{bound_variables} -> Compose $ do
  glbls <- view #globals
  tenv <- view #thms
  let env =
        emptyREnv
        & (\e -> Map.foldrWithKey addGlobal e glbls)
        & (\e -> foldr (uncurry addLocal) e (over (mapped . _2) embedIType bound_variables))
  let (the_prop, potential_proof_obligations) = runTcM tenv glbls (chk env)
  let proof_obligations = toListOf (traverse . filtered ((== Discharged) . snd) . _1) potential_proof_obligations
  let ensuring' (Proved g') x = ensuring (g == g') x
  getCompose $ (\ps p -> foldr ensuring' (ensuring' p $ Proved g) ps) <$> traverse k proof_obligations <*> Tactic.eval (tac the_prop) k g

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

subsumes :: Prop -> Prop -> Bool
subsumes h0 c0 = Unification.runSTRBinding $ go Map.empty h0 c0
  where
    go subst (PForall x _ p) c = do
      v <- Unification.freeVar
      go (Map.insert x v subst) p c
    go subst (PEquals u v) (PEquals w e) = do
      let
        u' = toUTerm subst u
        v' = toUTerm subst v
        w' = toUTerm Map.empty w
        e' = toUTerm Map.empty e
      l <- unify' u' w'
      r <- unify' v' e'
      return $ l && r
    go _ _ _ =
      return False

    toUTerm :: forall v. Map Ident v -> Term -> Unification.UTerm TermView v
    toUTerm subst (Var x) = case Map.lookup x subst of
      Just v -> Unification.UVar v
      Nothing -> Unification.UTerm (VVar x)
    toUTerm _ (Nat n) =
      Unification.UTerm (VNat n)
    toUTerm _ Succ =
      Unification.UTerm VSucc
    toUTerm subst (App u v) =
      Unification.UTerm (VApp (toUTerm subst u) (toUTerm subst v))

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

ensuring :: HasCallStack => Bool -> a -> a
ensuring True = id
ensuring False = error "Something went wrong"

addHyp :: Prop -> [Prop] -> [Prop]
addHyp PTrue = id
addHyp p = (p:)

intro :: Tac
intro = Tactic.Mk $ \k g -> case g of
  Goal {stoup=Nothing, concl=PNot p} ->
    let
      sub = g
        & over #hyps (addHyp p)
        & set #concl PFalse
    in
    (\(Proved sub') -> ensuring (sub == sub') $ Proved g) <$> (k sub)
  Goal {stoup=Nothing, concl=p `PImpl` q} ->
    let
      sub = g
        & over #hyps (addHyp p)
        & set #concl q
    in
    (\(Proved sub') -> ensuring (sub == sub') $ Proved g) <$> (k sub)
  Goal {stoup=Nothing, concl=PForall x 𝜏 p} -> Compose @TacM $ do
    glbls <- view #globals
    if x `Map.notMember` glbls then
        let
          x' = avoid x (freeVarsGoal g ++ Map.keys glbls)
          sub = g
            & over (#bound_variables . traverse . _1) (\y -> if y == x then x' else y)
            & over #bound_variables ((x, underlyingIType 𝜏) :)
            & over (#hyps . traverse) (substProp x (Var x'))
            & over #hyps (addHyp (constraint 𝜏 (Var x)))
            & set #concl p
        in
        getCompose $ (\(Proved sub') -> ensuring (sub == sub') $ Proved g) <$> (k sub)
    else
        let
          x' = avoid x (freeVarsGoal g ++ Map.keys glbls)
          sub = g
            & over #bound_variables ((x', underlyingIType 𝜏) :)
            & over #hyps (addHyp (constraint 𝜏 (Var x')))
            & set #concl (substProp x (Var x') p)
        in
        getCompose $ (\(Proved sub') -> ensuring (sub == sub') $ Proved g) <$> (k sub)
  _ -> Compose $ doFail g

max_intros :: Tac
max_intros = Main.repeat intro

discharge :: Tac
discharge = assumption `Tactic.or` subsumption `Tactic.or` (max_intros `Tactic.thn`congruence_closure)

dischargeWith :: [Ident] -> Tac
dischargeWith lems =
  foldr (\lem tac -> use lem [] `Tactic.thn` tac) discharge lems

use :: Ident -> [Term] -> Tac
use x h = Tactic.Mk $ \ k g@(Goal {stoup}) -> Compose $
  case stoup of
    Nothing -> do
      tenv <- view #thms
      x_prop <- case Map.lookup x tenv of { Just p -> return p ; Nothing -> doFail g }
      let
        sub = g
          & over #hyps (addHyp (instantiate x_prop h))
      getCompose $ (\(Proved sub') -> ensuring (sub == sub') $ Proved g) <$> (k sub)
    Just _ -> doFail g
 where
   instantiate :: Prop -> [Term] -> Prop
   instantiate (PForall y _ p) (u:us) = instantiate (substProp y u p) us
   instantiate p [] = p
   instantiate _ _ = error "Not enough foralls."

have0 :: Prop -> Tac
have0 p = Tactic.Mk $ \k g@(Goal {stoup}) ->
  case stoup of
    Nothing -> Compose $ do
      let
        side = g
          & set #concl p
        sub = g
          & over #hyps (addHyp p)
      getCompose $
        (\(Proved side') (Proved sub') -> ensuring (side == side') $ ensuring (sub == sub') $ Proved g)
        <$> k side <*> k sub
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
          & over #concl (substProp x (Nat 0))
        sub_succ = g
          & over #hyps (addHyp concl)
          & over #concl (substProp x (App Succ (Var x)))
      in
     (\(Proved _) (Proved _) -> Proved g)
       <$> k sub_0
       <*> k sub_succ
    Just _ -> Compose $ doFail g

-- TODO: refactor together with have0. Somehow.
focus0 :: Prop -> Tac
focus0 p = Tactic.Mk $ \k g@(Goal {stoup}) -> Compose $
  case stoup of
    Nothing -> do
      let
        side = g
          & set #concl p
        sub = g
          & set #stoup (Just p)
      getCompose $
        (\(Proved side') (Proved sub') -> ensuring (side == side') $ ensuring (sub == sub') $ Proved g)
        <$> k side <*> k sub
    Just _ -> doFail g

focus :: Prop -> [Ident] -> Tac
focus p lems = focus0 p `Tactic.dispatch` [dischargeWith lems, Tactic.id]

with :: Term -> Tac
with u = Tactic.Mk $ \k g@(Goal {stoup}) ->
  case stoup of
     -- TODO: check the type!
    Just (PForall y _ p) ->
      let
        sub = g
          & set #stoup (Just (substProp y u p))
      in
      (\(Proved sub') -> ensuring (sub == sub') $ Proved g) <$> (k sub)
    _ -> Compose $ doFail g

premise :: Tac
premise = Tactic.Mk $  \k g@(Goal {stoup}) ->
  case stoup of
    Just (PImpl p q) ->
      let
        side = g
          & set #stoup Nothing
          & set #concl p
        sub = g
          & set #stoup (Just q)
      in
      (\(Proved side') (Proved sub') -> ensuring (side == side') $ ensuring (sub == sub') $ Proved g)
        <$> k sub <*> k side
    _ -> Compose $ doFail g

deactivate :: Tac
deactivate = Tactic.Mk $ \k g@(Goal {stoup}) ->
  case stoup of
    Just p ->
      let
        sub = g
          & over #hyps (addHyp p)
          & set #stoup Nothing
      in
      (\(Proved sub') -> ensuring (sub == sub') $ Proved g) <$> (k sub)
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
  = VVar Ident
  | VNat Integer
  | VSucc
  | VApp a a
  deriving (Eq, Ord, Functor, Foldable, Traversable, Show)

instance CC.LiftRelation TermView where
  liftRelation _ (VVar x) (VVar y) = pure $ x == y
  liftRelation _ (VNat n) (VNat p) = pure $ n == p
  liftRelation _ VSucc VSucc = pure $ True
  liftRelation r (VApp u v) (VApp w e) =
    (&&) <$> r u w <*> r v e
  liftRelation _ _ _ = pure False

instance CC.Unfix Term TermView where
  view (Var x) = VVar x
  view (Nat n) = VNat n
  view Succ = VSucc
  view (App u v) = VApp u v

------------------------------------------------------------------------------
-- Unification

instance Unifiable TermView where
  zipMatch (VVar x) (VVar y) | x == y = pure $ VVar x
  zipMatch (VNat n) (VNat p) | n == p = pure $ VNat n
  zipMatch VSucc VSucc = pure $ VSucc
  zipMatch (VApp u v) (VApp w e) = pure $
    VApp (Right (u, w)) (Right (v, e))
  zipMatch _ _ = Nothing

------------------------------------------------------------------------------
-- The rest

embedIType :: IType -> RType
embedIType INat = RNat
embedIType (IArrow t u) = RArrow (embedIType t) (embedIType u)

underlyingIType :: RType -> IType
underlyingIType RNat = INat
underlyingIType (RArrow t u) = IArrow (underlyingIType t) (underlyingIType u)
underlyingIType (RSub _ t _) = underlyingIType t

chooseAVariableNameBasedOn :: RType -> Ident
chooseAVariableNameBasedOn _ = Ident "x"

constraint :: RType -> Term -> Prop
constraint RNat _ = PTrue
constraint (RArrow t u) f =
  let x = avoid (chooseAVariableNameBasedOn t) (freeVarsTerm [] f) in
  pforall x t (constraint t (Var x) `pimpl` constraint u (f `App` (Var x)))
constraint (RSub x t p) e = (constraint t e) `pand` (substProp x e p)

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

freeVarsTerm :: [Ident] -> Term -> [Ident]
freeVarsTerm env (Var x) = [ x | x `notElem` env ]
freeVarsTerm env t = termFoldSubs freeVarsTerm env t

freeVarsRType :: [Ident] -> RType -> [Ident]
freeVarsRType = rtypeFoldSubs freeVarsRType freeVarsProp

freeVarsProp :: [Ident] -> Prop -> [Ident]
freeVarsProp = propFoldSubs freeVarsTerm freeVarsRType freeVarsProp

substProp :: Ident -> Term -> Prop -> Prop
substProp x t fp@(PForall y 𝜏 p) =
  let
    y' = avoid y (freeVarsProp [] fp <> freeVarsTerm [] t)
    p' = substProp y (Var y') p
  in
  PForall y' 𝜏 (substProp x t p')
substProp x t p =
  propMapSubs_ (substTerm x t) (substRType x t) (substProp x t) p

substRType :: Ident -> Term -> RType -> RType
substRType x t s𝜏@(RSub y 𝜏 p) =
  let
    y' = avoid y (freeVarsRType [] s𝜏 <> freeVarsTerm [] t)
    p' = substProp y (Var y') p
  in
  RSub y' 𝜏 (substProp x t p')
substRType x t 𝜏 =
  rtypeMapSubs_ (substRType x t) (substProp x t) 𝜏

substTerm :: Ident -> Term -> Term -> Term
substTerm x t u@(Var y)
  | y == x = t
  | otherwise = u
substTerm x t u = termMapSubs_ (substTerm x t) u

type IEnv = Map Ident IType

typeCheckIntrinsicTerm :: IEnv -> Term -> IType -> Bool
typeCheckIntrinsicTerm env e u =
  (typeInferIntrinsicTerm env e) == Just u

typeInferIntrinsicTerm :: IEnv -> Term -> Maybe IType
typeInferIntrinsicTerm env (Var x) = do
  Map.lookup x env
typeInferIntrinsicTerm _env (Nat _) = do
  return [iType|ℕ|]
typeInferIntrinsicTerm _env Succ = do
  return [iType|ℕ → ℕ|]
typeInferIntrinsicTerm env (f `App` e) = do
  (u `IArrow` t) <- typeInferIntrinsicTerm env f
  guard (typeCheckIntrinsicTerm env e u)
  return t

-- | Assumes that @'underlyingIType' t == IArrow _ _@
decompArrow :: HasCallStack => RType -> (RType, RType, Term -> Prop)
decompArrow (u `RArrow` t) = (u, t, const PTrue)
decompArrow (RSub x u p) =
  let !(v, t, q) = decompArrow u in
  (v, t, \e -> q e `pand` substProp x e p)
decompArrow _ = error "This has to be an arrow"

data Localised a
  = Local a
  | Global a
  deriving (Generic)

projectLocalised :: Localised a -> a
projectLocalised (Local a) = a
projectLocalised (Global a) = a

newtype REnv = REnv { renv :: Map Ident (Localised RType) }
  deriving (Generic)

emptyREnv :: REnv
emptyREnv = REnv Map.empty

lookupREnv :: Ident -> REnv -> Maybe (Localised RType)
lookupREnv x (REnv env) = Map.lookup x env

(!) :: REnv -> Ident -> RType
(!) env x = projectLocalised ((renv env) Map.! x)

addLocal :: Ident -> RType -> REnv -> REnv
addLocal x 𝜏 (REnv env) = REnv $ Map.insert x (Local 𝜏) env

addGlobal :: Ident -> RType -> REnv -> REnv
addGlobal x 𝜏 (REnv env) = REnv $ Map.insert x (Global 𝜏) env

globalsREnv :: IndexedTraversal' Ident REnv RType
globalsREnv = #renv .> itraversed <. #_Global

underlyingITypes :: REnv -> IEnv
underlyingITypes (REnv env) = Map.map (underlyingIType . projectLocalised) env

data VarClass
  = DefinedLocal
  | DefinedGlobal
  | Undefined

avoidREnv :: Ident -> REnv -> Ident
avoidREnv x (REnv env) =
  avoid x (Map.keys env)

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
    , concatMap (freeVarsProp []) hyps
    , concatMap (freeVarsProp []) stoup
    , freeVarsProp [] concl
    ]

ppBoundVar :: (Ident, IType) -> Pp.Doc Pp.AnsiStyle
ppBoundVar (a, b) = pp a Pp.<+> ":" Pp.<+> pp b

ppGoal :: Goal -> Pp.Doc Pp.AnsiStyle
ppGoal (Goal {bound_variables, hyps, stoup=Nothing, concl}) =
  Pp.enclose "[" "]" (Pp.sep (Pp.punctuate Pp.comma (map ppBoundVar bound_variables)))
  Pp.<+> Pp.sep (Pp.punctuate Pp.comma (map pp hyps))
  Pp.<+> "⊢"
  Pp.<+> pp concl
ppGoal (Goal {bound_variables, hyps, stoup=Just stoup, concl}) =
  Pp.enclose "[" "]" (Pp.sep (Pp.punctuate Pp.comma (map ppBoundVar bound_variables)))
  Pp.<+> Pp.sep (Pp.punctuate Pp.comma (map pp hyps))
  Pp.<+> "|"
  Pp.<+> pp stoup
  Pp.<+> "⊢"
  Pp.<+> pp concl

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
emit env concl = do
  -- TODO: there is a bug here, in case of shadowing. Where the shadowing
  -- variable, will appear to bind the shadowed variables in some hypotheses,
  -- yielding incorrectly typed goals.
  let bound_variables = env & itoListOf (#renv .> itraversed <. (#_Local . to underlyingIType))
  hyps <- ask
  tell [Goal {bound_variables, hyps, concl, stoup=Nothing}]

assuming :: Prop -> TcM a -> TcM a
assuming PTrue = id
assuming p = local (p :)

shadowing :: Ident -> Ident -> TcM a -> TcM a
shadowing x x' act =
  local (map (substProp x (Var x'))) act

-- | Assumes that @'typeInferIntrinsicTerm' e == Just ('underlyingIType' t)@.
typeCheckRefinementTerm :: HasCallStack => REnv -> Term -> RType -> TcM ()
typeCheckRefinementTerm env e t = do
  type_of_e <- typeInferRefinementTerm env e
  assuming (constraint type_of_e e) $
    emit env $ constraint t e

typeInferRefinementTerm :: HasCallStack => REnv -> Term -> TcM RType
typeInferRefinementTerm env (Var x) = return $ env ! x
typeInferRefinementTerm _env (Nat _) = return $ RNat
typeInferRefinementTerm _env Succ = return $ [rType|ℕ → ℕ|]
typeInferRefinementTerm env (f `App` e) = do
  type_of_f <- typeInferRefinementTerm env f
  let (type_of_arg, type_of_return, given_of_f) = decompArrow type_of_f
  assuming (given_of_f f) $ do
    typeCheckRefinementTerm env e type_of_arg
    return type_of_return

-- This type is a lie: typeCheckProposition should fail gracefully if the
-- intrinsic type is faulty somewhere.
typeCheckProposition :: REnv -> Prop -> TcM ()
typeCheckProposition _env PTrue = return ()
typeCheckProposition _env PFalse = return ()
typeCheckProposition env (PNot p) = do
  typeCheckProposition env p
typeCheckProposition env (PAnd p q) = do
  typeCheckProposition env p
  typeCheckProposition env q
typeCheckProposition env (PImpl p q) = do
  typeCheckProposition env p
  assuming p $
    typeCheckProposition env q
typeCheckProposition env (PForall x t p) = do
  case lookupREnv x env of
    Nothing -> typeCheckProposition (addLocal x t env) p
    Just (Local 𝜏) ->
      let
        x' = avoid x (freeVarsProp [] p)
        t' = substRType x (Var x') t
      in
      shadowing x x' $ typeCheckProposition (addLocal x' 𝜏 (addLocal x t' env)) p
    Just (Global _) ->
      let x' = avoidREnv x env in
      typeCheckProposition (addLocal x' t env) (substProp x (Var x') p)
typeCheckProposition env (u `PEquals` v) = do
  -- ⬇️Need proper error management
  let ienv = underlyingITypes env
  let (Just itype_of_u) = typeInferIntrinsicTerm ienv u
  let !() = case typeCheckIntrinsicTerm ienv v itype_of_u of
        True -> ()
        False -> error "Proper errors pliz"
  -- ⬇️ Very asymmetric and awful
  type_of_u <- typeInferRefinementTerm env u
  typeCheckRefinementTerm env v type_of_u

type ThmEnv = Map Ident Prop

checkProgram :: REnv -> ThmEnv -> Prog -> IO ()
checkProgram env0 tenv0 (Prog decls0) = go env0 tenv0 decls0
  where
    go :: REnv -> ThmEnv -> [Decl] -> IO ()
    go _env _tenv [] = return ()
    go env tenv (decl@(Definition f t) : decls) = do
      Pp.putDoc $ pp decl
      putStrLn ""
      go (addGlobal f t env) tenv decls
    go env tenv (decl@(Axiom z p) : decls) = do
      Pp.putDoc $ pp decl
      putStrLn ""
      let goals = runTcM' tenv (toMapOf globalsREnv env) $ typeCheckProposition env p
      Pp.putDoc $ ppGoals goals
      go env (Map.insert z p tenv) decls
    go env tenv (Theorem z p tacs : decls) = do
      Pp.putDoc $ pp (Theorem z p NothingTacAlt)
      putStrLn ""
      let
        goals = runTcM' tenv (toMapOf globalsREnv env) $ do
          typeCheckProposition env p
          emit env p
        interactedGoals = applyMTacs tenv (toMapOf globalsREnv env) tacs goals
      Pp.putDoc $ ppAttemptedGoals interactedGoals
      go env (Map.insert z p tenv) decls

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

    applyMTacs :: ThmEnv -> Map Ident RType -> MaybeTacAlt -> [(Goal, DischargeStatus)] -> [(Goal, DischargeStatus, DischargeStatus, [Goal])]
    applyMTacs tenv globals NothingTacAlt = applyTacs tenv globals []
    applyMTacs tenv globals (JustTacAlt (TacAlt tacs)) = applyTacs tenv globals (map evalTac tacs)

evalTac :: TacExpr -> Tac
evalTac TId = Tactic.id
evalTac TDone = discharge
evalTac (TInd x) = induction x
evalTac TIntros = max_intros
evalTac (THave p lems) = checkProp (\env -> typeCheckProposition env p >> return p) $ \p' -> have p' lems
evalTac (TFocus p lems) = checkProp (\env -> typeCheckProposition env p >> return p) $ \p' -> focus p' lems
evalTac (TWith u) = with u
evalTac (TPremise) = premise
evalTac (TDeactivate) = deactivate
evalTac (TUse tac us) = use tac us
evalTac (TSUse tac) = use tac []
evalTac (TThen tac1 tac2) = Tactic.thn (evalTac tac1) (evalTac tac2)
evalTac (TDispatch tac1 (TacAlt alt)) = Tactic.dispatch (evalTac tac1) (map evalTac alt)

apply :: ThmEnv -> Map Ident RType -> Tac -> Goal -> Maybe [Goal]
apply thms globals tac goal =
  case runReaderT (Tactic.proveWith (\g -> lift (Failure [g])) tac goal) (ProofEnv{thms, globals}) of
    Success _thm -> Nothing -- should check the theorem really
    Failure gs -> Just gs

main :: IO ()
main = do
  Pp.putDoc $ pp [term|f (f 1)|]
  putStrLn ""
  Pp.putDoc $ pp [iType|(ℕ → ℕ) → ℕ → ℕ|]
  putStrLn ""
  let t = [rType|{ x : ℕ → ℕ | ⊤ }|]
  Pp.putDoc $ pp t
  putStrLn ""
  Pp.putDoc $ pp (underlyingIType t)
  putStrLn ""
  Pp.putDoc $ pp (constraint t [term|f|])
  putStrLn ""
  Pp.putDoc $ pp [prop|∀ x : ℕ. x=y|]
  putStrLn ""
  Pp.putDoc $ pp (substProp (Ident "y") [term|x|] [prop|∀ x : ℕ. x=y|])
  putStrLn ""
  let example = [prog|
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
        ; with n; with m; with (times n m)
        ; premise; [id | done]
        ; deactivate
        ; done
      ]

    thm oops : ∀ f : { n : ℕ | n = 0} → { n : ℕ | n = 0}. ⊥
     [   intros
       ; have (f 1 = 0) using
     ]
                            |]

        -- TODO Next time: have a proper shadowing semantics in the typechecker
        -- (shadowing must trigger renaming in the hypotheses when shadowing a
        -- local, shadowing a global needs to rename the conclusion instead),
        -- and intro (shadowing a local renames hypotheses, renaming a global is
        -- an error)

        -- TODO Next time too: typechecking tactics

        -- TODO Separate concrete syntax from abstract syntax

        -- We want to express:     ax div_spec : ∀ n : ℕ. ∀ m : { x:ℕ | ¬(x = 0) }. ∀ p : ℕ. ∃ k : ℕ. ∃ k' : ℕ. times n m + k = p ⇔ n + k' = div p m

        -- TODO later: propositions as terms of a particular type (+ some galois connection proofs, maybe?)

        -- TODO later: definitions

        -- TODO later: foralls in RTypes (that would give us a modicum of dependency). A possible test is lists of a given length.


  putStrLn ""
  checkProgram emptyREnv Map.empty example
  putStrLn "" -- Not sure why but Pp.putDoc doesn't actually print without this
  return ()
