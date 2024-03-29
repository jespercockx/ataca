{-# OPTIONS --postfix-projections #-}

module Ataca.Tactics.MiniAuto where

open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics.BasicTactics
open import Ataca.Tactics.Assumption
open import Ataca.Tactics.Intro
open import Ataca.Tactics.Constructor
open import Ataca.Tactics.Refine

Hints = List Term

mini-auto-with' : Hints → Tac ⊤
mini-auto-with' hints = repeat 10 $ choice1 $
  assumption' ∷ intro' ∷ introAbsurd' ∷ introConstructor' ∷ map refine' hints

mini-auto' : Tac ⊤
mini-auto' = mini-auto-with' []

macro
  mini-auto-with : Hints → Tactic
  mini-auto-with hints = runTac $ mini-auto-with' hints

  mini-auto : Tactic
  mini-auto = runTac mini-auto'
