{-# OPTIONS --without-K --postfix-projections #-}

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Utils
open import Tac
open import Exact

admit' : Tac A
admit' = do
  hole , holeType ← getGoal
  x ← freshName "ADMIT"
  declarePostulate (arg (arg-info visible relevant) x) holeType
  exact' (def x [])

macro
  admit : Tactic
  admit = toMacro admit'
