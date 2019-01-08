{-# OPTIONS --without-K --postfix-projections #-}

module Ataca.Tactics.Assumption where

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)

open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics.BasicTactics
open import Ataca.Tactics.Exact

tryVar : Nat → Tac A
tryVar i = do
  debug "assumption" 10 $ strErr "Trying variable" ∷ strErr (show i) ∷ []
  exact' $ var i []

assumption' : Tac A
assumption' = unlessSolved $ do
    ctx ← getContext
    debug "assumption" 20 $ strErr "Current context:" ∷ map (termErr ∘ unArg) ctx
    let vars = from 0 for (length ctx)
    choice $ map tryVar vars

macro
  assumption : TC.Tactic
  assumption = runTac assumption'
