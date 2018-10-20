{-# OPTIONS --without-K --postfix-projections #-}

module Tactics.Admit where

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Utils
open import Tac
open import Tactics.Exact

admit' : Tac A
admit' = do
  hole , holeType ← getGoal
  x ← freshName "ADMIT"
  declarePostulate (arg (arg-info visible relevant) x) holeType
  exact' (def x [])

macro
  admit : Tactic
  admit = toMacro admit'
