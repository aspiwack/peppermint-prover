module Main where

import Data.Maybe
import Control.Tactic (Tactic)
import qualified Control.Tactic as Tactic
import Test.Hspec
import Control.Applicative

-- A convoluted definition of the true proposition
data Prop
  = T
  | Prop `And` Prop
  deriving (Eq, Show)

newtype Thm = Proved Prop
  deriving (Show)

check :: Prop -> Maybe Thm -> Bool
check goal (Just (Proved proved)) = goal == proved
check _goal Nothing = False

prove_top :: Thm
prove_top = Proved T

prove_and :: Thm -> Thm -> Thm
prove_and (Proved l) (Proved r) = Proved (l `And` r)

trivial :: Tactic Prop Thm Maybe
trivial = Tactic.Mk go
  where
    go _k T = pure prove_top
    go _ _ = empty

destruct_and :: Tactic Prop Thm Maybe
destruct_and = Tactic.Mk go
  where
    go k (l `And` r) = prove_and <$> k l <*> k r
    go _ _ = empty

prop1 :: Prop
prop1 = T `And` (T `And` T)

proof1 :: Tactic Prop Thm Maybe
proof1 =
  destruct_and `Tactic.dispatch` [trivial, destruct_and `Tactic.thn` trivial]

prop2 :: Prop
prop2 = T `And` prop1

proof2 :: Tactic Prop Thm Maybe
proof2 =
  destruct_and `Tactic.dispatch` [trivial, proof1]

decide :: Tactic Prop Thm Maybe
decide =
  (trivial `Tactic.or` destruct_and) `Tactic.thn` decide

main :: IO ()
main = hspec $ do
  describe "Direct proofs" $ do
    it "proof1 solves prop1" $ do
      Tactic.proveWith (\_ -> Nothing) proof1 prop1 `shouldSatisfy` check prop1
    it "proof1 doesn't solve prop2" $ do
      Tactic.proveWith (\_ -> Nothing) proof1 prop2 `shouldSatisfy` isNothing
    it "proof2 solves prop2" $ do
      Tactic.proveWith (\_ -> Nothing) proof2 prop2 `shouldSatisfy` check prop2
  describe "Decision procedure" $ do
    it "solves prop1" $ do
      Tactic.proveWith (\_ -> Nothing) decide prop1 `shouldSatisfy` check prop1
    it "solves prop2" $ do
      Tactic.proveWith (\_ -> Nothing) decide prop2 `shouldSatisfy` check prop2
