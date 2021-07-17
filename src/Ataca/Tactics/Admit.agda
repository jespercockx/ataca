{-# OPTIONS --postfix-projections #-}

module Ataca.Tactics.Admit where

open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics.BasicTactics
open import Ataca.Tactics.Exact

admit' : Tac A
admit' = do
  lift (hole , holeType) ← liftF getHoleWithType
  lift x ← liftF $ freshName "ADMIT"
  liftF $ declarePostulate (vArg x) holeType
  exact' (def x [])

macro
  admit : Tactic
  admit = runTac admit'
