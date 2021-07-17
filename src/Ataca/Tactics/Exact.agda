{-# OPTIONS --postfix-projections #-}

module Ataca.Tactics.Exact where

open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics.BasicTactics

exact' : Term → Tac A
exact' solution = unlessSolved $ do
  lift hole ← liftF getHole
  liftF $ debug "exact" 10 $ strErr "Solving goal" ∷ termErr hole ∷ strErr "with solution" ∷ termErr solution ∷ []
  liftF $ unify hole solution
  qed

macro
  exact : A → Tactic
  exact u = runTac $ (quoteTac u) >>= exact'
