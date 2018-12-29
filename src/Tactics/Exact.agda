{-# OPTIONS --without-K --postfix-projections #-}

module Tactics.Exact where

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Reflection
open import Utils
open import Core
open import Tactics.BasicTactics

exact' : Term → Tac A
exact' solution = unlessSolved $ do
  hole ← getHole
  debug "exact" 10 $ strErr "Solving goal" ∷ termErr hole ∷ strErr "with solution" ∷ termErr solution ∷ []
  unify hole solution
  skip

macro
  exact : A → TC.Tactic
  exact u = runTac $ (quoteTac u) >>= exact'
