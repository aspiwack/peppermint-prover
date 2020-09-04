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

module Compile where

import Control.Lens
import Data.Coerce
import qualified Data.Maybe as Maybe

data Computation
  = Cc Command -- Binds 1
  | CasePair Command -- Binds 2
  | CaseUnit Command -- Binds 0
  | Return Value

data Value
  = Var Int
  | Pair Value Value
  | Unit
  | CaseReturn Command -- Binds 1 (basically: this is a thunk)

data Command = Interact Computation Value
-- Herbelin & Curien: Command
-- Krivine: Thread
-- Bolinbroke & Peyton Jones: StateValue
--
-- Whatever you call it, it's kind of the same thing.

instance Show Computation where
  show (Cc c) = "𝜇(⋅). " ++ show c
  show (CasePair c) = "𝜇(⋅, ⋅). " ++ show c
  show (CaseUnit c) = "𝜇(). " ++ show c
  show (Return v) = "⇓" ++ show v

instance Show Value where
  show (Var i) = show i
  show (Pair u v) = "(" ++ show u ++ ", " ++ show v ++ ")"
  show Unit = "()"
  show (CaseReturn c) = "𝜇(⇓⋅). " ++ show c
instance Show Command where
  show (Interact e v) = "⟨ " ++ show e ++ " | " ++ show v ++ " ⟩"

computationSubs :: Applicative f => (Int -> Computation -> f Computation) -> (Int -> Value -> f Value) -> (Int -> Command -> f Command) -> Int -> Computation -> f Computation
computationSubs _onComputation _onValue onCommand lvl (Cc c) = Cc <$> onCommand (lvl+1) c
computationSubs _onComputation _onValue onCommand lvl (CasePair c) = CasePair <$> onCommand (lvl+2) c
computationSubs _onComputation _onValue onCommand lvl (CaseUnit c) = CaseUnit <$> onCommand lvl c
computationSubs _onComputation onValue _onCommand lvl (Return v) = Return <$> onValue lvl v

valueSubs :: Applicative f => (Int -> Computation -> f Computation) -> (Int -> Value -> f Value) -> (Int -> Command -> f Command) -> Int -> Value -> f Value
valueSubs _onComputation _onValue _onCommand _lvl v@(Var _) = pure v
valueSubs _onComputation onValue _onCommand lvl (Pair u v) = Pair <$> onValue lvl u <*> onValue lvl v
valueSubs _onComputation _onValue _onCommand _lvl v@Unit = pure v
valueSubs _onComputation _onValue onCommand lvl (CaseReturn c) = CaseReturn <$> onCommand (lvl+1) c

commandSubs :: Applicative f => (Int -> Computation -> f Computation) -> (Int -> Value -> f Value) -> (Int -> Command -> f Command) -> Int -> Command -> f Command
commandSubs onComputation onValue _onCommand lvl (Interact e v)= Interact <$> onComputation lvl e <*> onValue lvl v

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

------
-- Substitution

substComputation :: [Value] -> Computation -> Computation
substComputation subst (Cc c) = Cc (substCommand (shift subst) c)
substComputation subst (CasePair c) = CasePair (substCommand (shift (shift subst)) c)
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
-- Actual supercompiler

-- Binds 1
--
-- u (with x potentially free) ~~> 𝜇(x,k). ⟨e|k⟩
lam :: Computation -> Computation
lam e =
  CasePair $ Interact (liftComputation e) (Var 0)

-- e, v ~> 𝜇k. ⟨e|(v,k)⟩
app :: Computation -> Value -> Computation
app e v =
  Cc $ Interact e (Pair v (Var 0))

type History = [Command]
data ShallI
  = Stop
  | Continue History

terminate :: History -> Command -> ShallI
terminate h c =
  if length h >= 100 then
    Stop
  else
    Continue (c:h)

-- Nothing if the evaluation is stuck (value, or neutral term)
step :: Command -> Maybe Command
step (Interact (Cc c) v) = Just $ substCommand [v] c
step (Interact (Return v) (CaseReturn c)) = Just $ substCommand [v] c
step (Interact (CasePair c) (Pair u v)) = Just $ substCommand [u, v] c
step (Interact (CaseUnit c) Unit) = Just $ c
step _c = Nothing

-- Aka Traversal' Command Command
split :: Applicative f => (Command -> f Command) -> Command -> f Command
split _f c = pure c

reduce :: Command -> Command
reduce = go []
  where
    go h c = case step c of
      Nothing -> c
      Just c' ->
        -- TODO add the intermediate or normalise optimisation
        case terminate h c' of
          Stop -> c'
          Continue h' -> go h' c'

newtype M a = Mk (Identity a)
  deriving (Functor, Applicative, Monad)

run :: M a -> a
run (Mk x) = runIdentity x

supercompile0 :: History -> Command -> M Command
supercompile0 h c = case terminate h c of
  Continue h' -> split (supercompile h') (reduce c)
  Stop -> split (supercompile h) c

supercompile :: History -> Command -> M Command
supercompile = supercompile0

optimise :: Command -> Command
optimise c = run $
  supercompile [] c

-- $> optimise $ Interact ((lam (lam (Return (Compile.Var 1)))) `app` Pair Unit Unit `app` Unit) Unit
