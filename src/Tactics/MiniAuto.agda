{-# OPTIONS --without-K --postfix-projections #-}

module Tactics.MiniAuto where

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Utils

open import Tac
open import Tactics.Assumption
open import Tactics.Intro
open import Tactics.Constructor
open import Tactics.Refine

Hints = List Term

mini-auto-with' : Hints → Tac ⊤
mini-auto-with' hints = repeat 10 $ assumption' <|> do
  goal , goalType ← getGoal
  liftTC (piView goalType) >>= λ where
    (just _) → intro'
    nothing  → choice1 (introConstructor' ∷ map refine' hints)

mini-auto' : Tac ⊤
mini-auto' = mini-auto-with' []

macro
  mini-auto-with : Hints → Tactic
  mini-auto-with hints = toMacro $ mini-auto-with' hints

  mini-auto : Tactic
  mini-auto = toMacro mini-auto'
