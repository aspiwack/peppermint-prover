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
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Compile where

import Control.Applicative
import Control.Lens
import qualified Control.Monad.State as State
import Data.Coerce
import Data.Generics.Labels ()
import Data.List
import qualified Data.Maybe as Maybe
import Data.Monoid
import GHC.Generics
import Data.Text.Prettyprint.Doc ((<+>))
import qualified Data.Text.Prettyprint.Doc as Pp

-- - Q: How do I lower this language?
--
--   A: this is not harder than using CPS as an intermediate form. Actually,
--   it's much of the same thing, with a more dedicated syntax. So we have the
--   same problems in compiling with continuations, that call/cc is trivially
--   representable. Both in compiling with continuations and sequent core, we
--   have the same solution: having a linearity constraint on the stack-thing
--   (or continuation thing). When the stack is linear, then you have to use it
--   syntactically, as a tail object (in sequent core they even only need a
--   single stack variable). You can exploit this property to lower sequent code.
--
-- - Q: What does sequent core use let-on-commands for?
--
--   A: First, they are not really lets of commands, they are lets of
--   computations. With a small twist: they are variadic in the stack argument,
--   and are eliminated with a form of multi-cut. It's used to represent
--   join-points.
--
-- - Q: Should the lets that we use for the supercompilation be lets of values,
--   of commands, or of computations?
--
--   A: Computations! Because we want these lets to represent fixed points, and
--   in a polarised sequent calculus, we only have fixed point on computations.
--
-- Refs:
-- [super compilation by evaluation]: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/07/supercomp-by-eval.pdf
-- [sequent core]: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/04/sequent-calculus-icfp16.pdf
-- [compiling with continuations]

data Computation
  = Cc Command -- Binds 1
  | CaseTuple Int Command -- Binds n
  | CaseI Command Command -- Binds 1, in both
  | CaseVoid
  | Return Value
  | Call String
  deriving (Eq)

data Value
  = Var Int
  | Symb String
  | Tuple [Value]
  | I1 Value
  | I2 Value
  | CaseReturn Command -- Binds 1 (basically: this is a thunk)
  deriving (Eq)

data Command
  = Interact Computation Value
  | Let [(String, Computation)] Command -- Could also be called Def
  deriving (Eq)
-- Herbelin & Curien: Command
-- Krivine: Thread
-- Bolinbroke & Peyton Jones: StateValue
--
-- Whatever you call it, it's kind of the same thing.

mu :: [Pp.Doc ann] -> Pp.Doc ann -> Pp.Doc ann
mu binds c = Pp.group $ Pp.hang 2 $ "𝜇" <> Pp.tupled binds <> "." <> Pp.line <> c
instance Algebra ([String] -> Pp.Doc ann) ([String] -> Pp.Doc ann) ([String] -> Pp.Doc ann) where
  tCc c supply =
    let x = Pp.pretty $ head supply in
    mu [x] $ c (const x) (tail supply)
  tCaseTuple n c supply =
    let xs = map Pp.pretty (take n supply) in
    mu xs $ c (map const xs) (drop n supply)
  tCaseI c1 c2 supply =
    let x = Pp.pretty $ head supply in
    Pp.encloseSep "{ " " }" ", "
      [ mu ["1." <> x] $ c1 (const x) (tail supply)
      , mu ["2." <> x] $ c2 (const x) (tail supply)
      ]
  tCaseVoid _supply = "{}"
  tRet v supply = "⇓" <+> v supply
  tCall s _supply = Pp.pretty s

  tSymb s _supply = ":" <> Pp.pretty s
  tTuple us supply = Pp.tupled (map ($ supply) us)
  tI1 u supply = "1." <> u supply
  tI2 u supply = "2." <> u supply
  tCaseRet c supply =
    let x = Pp.pretty $ head supply in
    mu ["⇓" <> x] $ c (const x) (tail supply)

  tInteract e v supply = Pp.group $ Pp.vsep
    [ Pp.nest 2 $ Pp.vsep
      ["⟨"
      , e supply
      ]
    , Pp.nest 2 $ Pp.vsep
      [ "|"
      , v supply
      ]
    , "⟩"
    ]
  tLet es c supply = Pp.vsep
    [ "let"
    , Pp.indent 2 $ Pp.encloseSep "{ " " }" "; " (map (\(n,d) -> Pp.pretty n <+> " = " <+> d supply) es)
    , "in"
    , c supply
    ]

varNameSupply :: [String]
varNameSupply = map (\x -> [x]) $ ['x'..'z'] ++ ['a'..'w']

unboundVars :: [[String] -> Pp.Doc ann]
unboundVars = map (\(i::Int) _ -> "UNBOUND_" <> Pp.pretty i) [0..]

instance Show Computation where
  show e = show $ (runComputation @([String]->Pp.Doc _) e unboundVars varNameSupply)

instance Show Value where
  show u = show $ (runValue @([String]->Pp.Doc _) u unboundVars varNameSupply)

instance Show Command where
  show c = show $ (runCommand @([String]->Pp.Doc _) c unboundVars varNameSupply)

computationSubs :: Applicative f => (Int -> Computation -> f Computation) -> (Int -> Value -> f Value) -> (Int -> Command -> f Command) -> Int -> Computation -> f Computation
computationSubs _onComputation _onValue onCommand lvl (Cc c) = Cc <$> onCommand (lvl+1) c
computationSubs _onComputation _onValue onCommand lvl (CaseTuple n c) = CaseTuple n <$> onCommand (lvl+n) c
computationSubs _onComputation _onValue onCommand lvl (CaseI c1 c2) = CaseI <$> onCommand (lvl+1) c1 <*> onCommand (lvl+1) c2
computationSubs _onComputation _onValue _onCommand _lvl e@CaseVoid = pure e
computationSubs _onComputation onValue _onCommand lvl (Return v) = Return <$> onValue lvl v
computationSubs _onComputation _onValue _onCommand _lvl e@(Call _) = pure e

valueSubs :: Applicative f => (Int -> Computation -> f Computation) -> (Int -> Value -> f Value) -> (Int -> Command -> f Command) -> Int -> Value -> f Value
valueSubs _onComputation _onValue _onCommand _lvl v@(Var _) = pure v
valueSubs _onComputation _onValue _onCommand _lvl v@(Symb _) = pure v
valueSubs _onComputation onValue _onCommand lvl (Tuple us) = Tuple <$> traverse (onValue lvl) us
valueSubs _onComputation onValue _onCommand lvl (I1 u) = I1 <$> onValue lvl u
valueSubs _onComputation onValue _onCommand lvl (I2 u) = I2 <$> onValue lvl u
valueSubs _onComputation _onValue onCommand lvl (CaseReturn c) = CaseReturn <$> onCommand (lvl+1) c

commandSubs :: Applicative f => (Int -> Computation -> f Computation) -> (Int -> Value -> f Value) -> (Int -> Command -> f Command) -> Int -> Command -> f Command
commandSubs onComputation onValue _onCommand lvl (Interact e v)= Interact <$> onComputation lvl e <*> onValue lvl v
commandSubs onComputation _onValue onCommand lvl (Let es c) =
  Let <$> traverseOf (traverse . _2) (onComputation lvl) es <*> onCommand lvl c

computationSubs_ :: Applicative f => (Computation -> f Computation) -> (Value -> f Value) -> (Command -> f Command) -> Computation -> f Computation
computationSubs_ onComputation onValue onCommand = computationSubs (const onComputation) (const onValue) (const onCommand) 0

valueSubs_ :: Applicative f => (Computation -> f Computation) -> (Value -> f Value) -> (Command -> f Command) -> Value -> f Value
valueSubs_ onComputation onValue onCommand = valueSubs (const onComputation) (const onValue) (const onCommand) 0

commandSubs_ :: Applicative f => (Computation -> f Computation) -> (Value -> f Value) -> (Command -> f Command) -> Command -> f Command
commandSubs_ onComputation onValue onCommand = commandSubs (const onComputation) (const onValue) (const onCommand) 0

computationMapSubs_ :: (Computation -> Computation) -> (Value -> Value) -> (Command -> Command) -> Computation -> Computation
computationMapSubs_ = coerce $ computationSubs_ @Identity

valueMapSubs_ :: (Computation -> Computation) -> (Value -> Value) -> (Command -> Command) -> Value -> Value
valueMapSubs_ = coerce $ valueSubs_ @Identity

commandMapSubs_ :: (Computation -> Computation) -> (Value -> Value) -> (Command -> Command) -> Command -> Command
commandMapSubs_ = coerce $ commandSubs_ @Identity

computationFoldSubs :: forall a. Monoid a => (Int -> Computation -> a) -> (Int -> Value -> a) -> (Int -> Command -> a) -> Int -> Computation -> a
computationFoldSubs = coerce $ computationSubs @(Const a)

valueFoldSubs :: forall a. Monoid a => (Int -> Computation -> a) -> (Int -> Value -> a) -> (Int -> Command -> a) -> Int -> Value -> a
valueFoldSubs = coerce $ valueSubs @(Const a)

commandFoldSubs :: forall a. Monoid a => (Int -> Computation -> a) -> (Int -> Value -> a) -> (Int -> Command -> a) -> Int -> Command -> a
commandFoldSubs = coerce $ commandSubs @(Const a)

computationFoldSubs_ :: forall a. Monoid a => (Computation -> a) -> (Value -> a) -> (Command -> a) -> Computation -> a
computationFoldSubs_ = coerce $ computationSubs_ @(Const a)

valueFoldSubs_ :: forall a. Monoid a => (Computation -> a) -> (Value -> a) -> (Command -> a) -> Value -> a
valueFoldSubs_ = coerce $ valueSubs_ @(Const a)

commandFoldSubs_ :: forall a. Monoid a => (Computation -> a) -> (Value -> a) -> (Command -> a) -> Command -> a
commandFoldSubs_ = coerce $ commandSubs_ @(Const a)

------
-- Substitution

substComputation :: [Value] -> Computation -> Computation
substComputation subst (Cc c) = Cc (substCommand (shift subst) c)
substComputation subst (CaseTuple n c) = CaseTuple n (substCommand ((iterate shift subst)!!n) c)
substComputation subst (CaseI c1 c2) = CaseI (substCommand (shift subst) c1) (substCommand (shift subst) c2)
substComputation subst e = computationMapSubs_ (substComputation subst) (substValue subst) (substCommand subst) e

substValue :: [Value] -> Value -> Value
substValue subst u@(Var i) = Maybe.fromMaybe u $ preview (ix i) subst
substValue subst (CaseReturn c) = CaseReturn (substCommand (shift subst) c)
substValue subst u = valueMapSubs_ (substComputation subst) (substValue subst) (substCommand subst) u

substCommand :: [Value] -> Command -> Command
substCommand subst = commandMapSubs_ (substComputation subst) (substValue subst) (substCommand subst)

shift :: [Value] -> [Value]
shift subst = Var 0 : map liftValue subst

liftComputation :: Computation -> Computation
liftComputation = substComputation (map Var [1..])

liftValue :: Value -> Value
liftValue = substValue (map Var [1..])

liftCommand :: Command -> Command
liftCommand = substCommand (map Var [1..])

------
-- Tagless representation

class Algebra c v t | c -> v, c -> t, v -> c, t -> c where
  tCc :: (v -> t) -> c
  tCaseTuple :: Int -> ([v] -> t) -> c
  tCaseI :: (v -> t) -> (v -> t) -> c
  tCaseVoid :: c
  tRet :: v -> c
  tCall :: String -> c

  tSymb :: String -> v
  tTuple :: [v] -> v
  tI1 :: v -> v
  tI2 :: v -> v
  tCaseRet :: (v -> t) -> v

  tInteract :: c -> v -> t
  tLet :: [(String, c)] -> t -> t

runComputation :: Algebra c v t => Computation -> [v] -> c
runComputation (Cc c) subst = tCc (\v -> runCommand c (v:subst))
runComputation (CaseTuple n c) subst = tCaseTuple n (\vs -> runCommand c (vs ++ subst))
runComputation (CaseI c1 c2) subst = tCaseI (\v -> runCommand c1 (v:subst)) (\v -> runCommand c2 (v:subst))
runComputation (CaseVoid) _subst = tCaseVoid
runComputation (Return u) subst = tRet (runValue u subst)
runComputation (Call d) _subst = tCall d

runValue :: Algebra c v t => Value -> [v] -> v
runValue (Var i) subst = subst !! i
runValue (Symb s) _subst = tSymb s
runValue (Tuple us) subst = tTuple $ map (\u -> runValue u subst) us
runValue (I1 u) subst = tI1 (runValue u subst)
runValue (I2 u) subst = tI2 (runValue u subst)
runValue (CaseReturn c) subst = tCaseRet (\v -> runCommand c (v:subst))

runCommand :: Algebra c v t => Command -> [v] -> t
runCommand (Interact e u) subst = tInteract (runComputation e subst) (runValue u subst)
runCommand (Let decls c) subst =
  tLet
    (over (traverse . _2) (\e -> runComputation e subst) decls)
    (runCommand c subst)

tVar :: Int -> ([Value] -> Value)
tVar i = \subst -> (reverse subst) !! i

-- XXX: needs an actual substitution to lift unbound variables. It's ok on closed terms.
instance Algebra ([Value]->Computation) ([Value]->Value) ([Value]->Command) where
  tCc c subst = Cc (c (tVar (length subst)) (shift subst))
  tCaseTuple n c subst =
    let xs = reverse $ map (\i -> tVar ((length subst)+i)) [0..(n-1)] in
    CaseTuple n (c xs ((iterate shift subst)!!n))
  tCaseI c1 c2 subst = CaseI (c1 (tVar (length subst)) (shift subst)) (c2 (tVar (length subst)) (shift subst))
  tCaseVoid _subst = CaseVoid
  tRet v subst = Return (v subst)
  tCall d _subst = Call d

  tSymb s _subst = Symb s
  tTuple us subst = Tuple (map ($ subst) us)
  tI1 u subst = I1 (u subst)
  tI2 u subst = I2 (u subst)
  tCaseRet c subst = CaseReturn (c (tVar (length subst)) (shift subst))

  tInteract e u subst = Interact (e subst) (u subst)
  tLet decls c subst =
    Let
      (over (traverse . _2) ($ subst) decls)
      (c subst)

interpretComputation :: (forall c v t. Algebra c v t => c) -> Computation
interpretComputation e = e @([Value] -> Computation) []

interpretValue :: (forall c v t. Algebra c v t => v) -> Value
interpretValue u = u @([Value] -> Computation) []

interpretCommand :: (forall c v t. Algebra c v t => t) -> Command
interpretCommand c = c @([Value] -> Computation) []

------
-- Smart constructors

mkLet :: [(String, Computation)] -> Command -> Command
mkLet defs c = simplify $ foldl' (flip $ uncurry inlineCommand) (abstract to_abstract c) to_inline
  where
    abstract [] d = d
    abstract defs' d = Let defs' d

    (to_inline, to_abstract) = partition can_inline defs

    can_inline (x, e) = trivial e || not_duplicated x

    trivial (CaseTuple 0 (Interact (Return _) _)) = True
    trivial _ = False

    -- This is very crude, and not always correct for performance, but it'll
    -- help debugging (why is not always correct? it lets me inline under a
    -- lambda, this is only correct in a full call-by-name calculus)
    not_duplicated x =
      (getSum $ foldMapOf (traverse . _2) (callCountComputationSum x) defs) == 0
      && callCountCommand x c <= 1

simplify :: Command -> Command
simplify (Interact (Cc c) v) = simplify $ substCommand [v] c
simplify (Interact (Return v) (CaseReturn c)) = simplify $ substCommand [v] c
simplify (Interact (CaseTuple n c) (Tuple us)) | n == length us = simplify $ substCommand us c
simplify (Interact e u) = Interact (simplifyComputation e) (simplifyValue u)
simplify (Let defs c) = Let defs (simplify c)

simplifyComputation :: Computation -> Computation
simplifyComputation = computationMapSubs_ simplifyComputation simplifyValue simplify

simplifyValue :: Value -> Value
simplifyValue = valueMapSubs_ simplifyComputation simplifyValue simplify

inlineComputation :: String -> Computation -> Computation -> Computation
inlineComputation x e (Call y) | y == x = e
inlineComputation x e f = computationMapSubs_ (inlineComputation x e) (inlineValue x e) (inlineCommand x e) f

inlineValue :: String -> Computation -> Value -> Value
inlineValue x e = valueMapSubs_ (inlineComputation x e) (inlineValue x e) (inlineCommand x e)

inlineCommand :: String -> Computation -> Command -> Command
inlineCommand x e = commandMapSubs_ (inlineComputation x e) (inlineValue x e) (inlineCommand x e)

callCountComputation :: String -> Computation -> Int
callCountComputation = coerce callCountComputationSum

callCountCommand :: String -> Command -> Int
callCountCommand = coerce callCountCommandSum

callCountComputationSum :: String -> Computation -> Sum Int
callCountComputationSum x (Call y) | y == x = Sum 1
callCountComputationSum x e = computationFoldSubs_ (callCountComputationSum x) (callCountValueSum x) (callCountCommandSum x) e

callCountValueSum :: String -> Value -> Sum Int
callCountValueSum x = valueFoldSubs_ (callCountComputationSum x) (callCountValueSum x) (callCountCommandSum x)

callCountCommandSum :: String -> Command -> Sum Int
callCountCommandSum x = commandFoldSubs_ (callCountComputationSum x) (callCountValueSum x) (callCountCommandSum x)

------
-- λ-calculus: cbn

-- Binds 1
--
-- u (with x potentially free) ~~> 𝜇(x,k). ⟨e|k⟩
lam :: Algebra c v t => (c -> c) -> c
lam e =
  tCaseTuple 2 $ \[x, k] ->
    tInteract (e (var x)) k
  -- CasePair $ Interact (liftComputation e) (Var 0)

-- x ~> 𝜇k. ⟨⇑k|x⟩
var :: Algebra c v t => v -> c
var x = tCc $ \k ->
  tInteract (tRet k) x

-- e, u ~> 𝜇k. ⟨e|(𝜇(⇑k').⟨u|k'⟩,k)⟩
app :: Algebra c v t => c -> c -> c
app e u = tCc $ \k ->
  tInteract
    e
    (tTuple [tCaseRet (\k' -> tInteract u k'), k])


-- u, e1, e2 ~> 𝜇k. ⟨u|𝜇(⇑r). ⟨{𝜇(1.x). ⟨e1|k⟩, 𝜇(2.x). ⟨e2|k⟩}|r⟩⟩
casei :: Algebra c v t => c -> (c -> c) -> (c -> c) -> c
casei u e1 e2 = tCc $ \k ->
  tInteract
    u
    (tCaseRet $ \r ->
        tInteract
          (tCaseI (\x -> tInteract (e1 (var x)) k) (\x -> tInteract (e2 (var x)) k))
          r)

symb :: Algebra c v t => String -> c
symb s = tRet $ tSymb s

tUnit :: Algebra c v t => v
tUnit = tTuple []

unit :: Algebra c v t => c
unit = tRet tUnit

pair :: Algebra c v t => c -> c -> c
pair el er = tCc $ \k ->
  tInteract
    el
    (tCaseRet $ \ul ->
        tInteract er (tCaseRet $ \ur ->
          tInteract (tRet (tTuple [ul, ur])) k))

casep :: Algebra c v t => c -> (c -> c -> c) -> c
casep u e = tCc $ \k ->
  tInteract
    u
    (tCaseRet $ \u' ->
        tInteract (tCaseTuple 2 $ \[x, y] -> tInteract (e (var x) (var y)) k) u')

call :: Algebra c v t => String -> c
call = tCall

------
-- λ-calculus: cbv

-- TODO

------
-- Actual supercompiler

type History = [State]
data ShallI
  = Stop
  | Continue History

terminate :: History -> State -> ShallI
terminate h c =
  if length h >= 100 then
    Stop
  else
    Continue (c:h)

data State = State [(String, Computation)] Command
  deriving (Show, Eq)

-- Nothing if the evaluation is stuck (value, or neutral term)
stepCommand :: Command -> Maybe Command
stepCommand (Interact (Cc c) v) = Just $ substCommand [v] c
stepCommand (Interact (Return v) (CaseReturn c)) = Just $ substCommand [v] c
stepCommand (Interact (CaseTuple n c) (Tuple us)) | n == length us = Just $ substCommand us c
stepCommand _c = Nothing

step :: State -> Maybe State
step (State defs c) = (State defs <$> stepCommand c) <|> go defs c
  where
    go ds (Interact (Call x) v) = (\e -> State ds (Interact e v)) <$> lookup x ds
    go ds (Let new_defs c') = Just $ State (new_defs ++ ds) c'
    go _ds _c = Nothing

-- Aka Traversal' Command Command
split :: forall f. Applicative f => (State -> f Command) -> State -> f Command
-- split opt (Interact e v) = Interact <$> computationSubs_ pure pure opt e <*> pure v
split opt (State defs (Interact e v)) =
    mkLet <$> defs' <*> (Interact <$> splitComputation e <*> splitValue v)
  where
    defs' = traverseOf (traverse . _2 ) splitComputation defs
    optCommand :: Command -> f Command
    optCommand c = opt (State [] c)
    splitComputation :: Computation -> f Computation
    splitComputation = computationSubs_ pure splitValue optCommand
    splitValue :: Value -> f Value
    splitValue = valueSubs_ pure splitValue optCommand
split _opt (State defs c) = pure $ mkLet defs c

reduce :: State -> State
reduce = go []
  where
    go h c = case step c of
      Nothing -> c
      Just c' ->
        -- TODO add the intermediate or normalise optimisation
        case terminate h c' of
          Stop -> c'
          Continue h' -> go h' c'

newtype M a = Mk (State.State MemoState a)
  deriving (Functor, Applicative, Monad)

data Promise = Promise
  { promise_name :: String
  , fvs :: Int
  , meaning :: State
  }
  deriving (Generic)
data MemoState = MemoState
  { promises :: [Promise]
  , bindings :: [(String, Computation)]
  , name_supply :: [String]
  }
  deriving (Generic)

startMemoState :: MemoState
startMemoState = MemoState
  { promises = []
  , bindings = []
  , name_supply = zipWith (++) (repeat "$d") (map (show @Int) [1..])
  }

run :: M Command -> Command
run (Mk x) = State.evalState x' startMemoState
  where
    x' = do
      c <- x
      bs <- use #bindings
      return $ mkLet bs c

freshName :: M String
freshName = Mk $ do
  supply <- use #name_supply
  assign #name_supply (tail supply)
  return $ head supply

exists :: State -> M (Maybe Computation)
exists st = Mk $ do
  ps <- use #promises
  return $ Call <$> view #promise_name <$> find (\p -> view #meaning p == st) ps

promise :: State -> M (String, [Value], State)
promise st = do
  x <- freshName
  let (st', vars) = abstractVarsState st
  promise0 x (length vars) st
  return $ (x, vars, st')
  where
    promise0 promise_name fvs meaning = Mk $
      modifying #promises (Promise{promise_name,fvs,meaning} :)

bind :: String -> Int -> Command -> M ()
bind name fvs c = Mk $
  modifying #bindings ((name, CaseTuple fvs c) :)

abstractVarsState :: State -> (State, [Value])
abstractVarsState st =
  State.runState (go st) []
  where
    go (State decls c) =
      State
        <$> traverseOf (traverse . _2) (abstractVarsComputation 0) decls
        <*> abstractVarsCommand 0 c

-- The State Int is the number of already generated binders.
abstractVarsComputation :: Int -> Computation -> State.State [Value] Computation
abstractVarsComputation = computationSubs abstractVarsComputation abstractVarsValue abstractVarsCommand

abstractVarsValue :: Int -> Value -> State.State [Value] Value
abstractVarsValue lvl (Var i) | i >= lvl = do
  n <- State.gets length
  State.modify (++ [Var i])
  return $ Var (lvl+n) -- note at level 0, `Var 0` is a free variable
abstractVarsValue lvl u = valueSubs abstractVarsComputation abstractVarsValue abstractVarsCommand lvl u

abstractVarsCommand :: Int -> Command -> State.State [Value] Command
abstractVarsCommand = commandSubs abstractVarsComputation abstractVarsValue abstractVarsCommand

memoise :: (State -> M Command) -> State -> M Command
memoise opt st =
  exists st >>= \case
    Just res -> return $ Interact res (Tuple [])
    Nothing -> do
      (x, vars, st') <- promise st
      e <- opt st'
      bind x (length vars) e
      return $ Interact (Call x) (Tuple vars)

supercompile0 :: History -> State -> M Command
supercompile0 h c = case terminate h c of
  Continue h' -> split (supercompile h') (reduce c)
  Stop -> split (supercompile h) c

supercompile :: History -> State -> M Command
supercompile h = memoise (supercompile0 h)

optimise :: Command -> Command
optimise c = run $
  supercompile [] (State [] c)

optimise' :: (forall c v t. Algebra c v t => t) -> Command
optimise' c = optimise $ interpretCommand c

-- $> optimise' $ tInteract ((lam $ \x -> lam $ \_ -> x) `app` symb "a" `app` symb "b") tUnit

-- $> optimise' $ tInteract (casei (symb "x") (\_ -> symb "a") (\_ -> symb "b")) tUnit

-- $> optimise' $ tInteract (lam $ \ _ -> (lam $ \x -> lam $ \_ -> x) `app` symb "a" `app` symb "b") tUnit

-- $> optimise' $ tInteract (lam $ \y -> (casei y (\_ -> (lam $ \x -> lam $ \_ -> x) `app` symb "a" `app` symb "b") (\_ -> lam $ \_ -> (lam $ \x -> lam $ \_ -> x) `app` symb "c" `app` symb "d"))) tUnit

-- $> optimise' $ tInteract ((casei (symb "x") (\_ -> lam $ \x -> x) (\_ -> lam (\_ -> symb "b"))) `app` symb "a") tUnit


-- foo :: Command
-- foo = Let [("map", lam (lam (casei (var 0) (unit) (casep (var 0) (pair (var 5 `app` (var 1)) (call "map" `app` var 5 `app` (var 0)))))))] (Interact (call "map" `app` (lam (symb "a"))) Unit)
--
-- -- $> optimise foo

-- TODO: fix the definition of map to use `i1` and `i2` in the returned values.
-- TODO: debug, for the map example looks very fishy
-- TODO: hunt for missing commutation which may make the optimised code more readable (I'm not sure there are any).
--
-- GOAL: observe map/map fusion.
