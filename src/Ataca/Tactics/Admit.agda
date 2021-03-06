{-# OPTIONS --postfix-projections #-}

module Ataca.Tactics.Admit where

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)

open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics.BasicTactics
open import Ataca.Tactics.Exact

admit' : Tac A
admit' = do
  hole , holeType ← getHoleWithType
  x ← freshName "ADMIT"
  declarePostulate (arg (arg-info visible relevant) x) holeType
  exact' (def x [])

macro
  admit : TC.Tactic
  admit = runTac admit'
