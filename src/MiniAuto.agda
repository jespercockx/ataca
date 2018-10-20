{-# OPTIONS --without-K --postfix-projections #-}

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Utils

open import Tac
open import Assumption
open import Intro
open import Constructor
open import Refine

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
