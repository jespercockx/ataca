{-# OPTIONS --postfix-projections #-}

module Ataca.Tactics.Assumption where

open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics.BasicTactics
open import Ataca.Tactics.Exact

tryVar : ℕ → Tac A
tryVar i = do
  liftF $ debug "assumption" 10 $ strErr "Trying variable" ∷ strErr (ℕ.show i) ∷ []
  exact' $ var i []

assumption' : Tac A
assumption' = unlessSolved $ do
    lift ctx ← liftF $ map snd <$> getContext
    liftF $ debug "assumption" 20 $ strErr "Current context:" ∷ map (termErr ∘ unArg) ctx
    let vars = List.upTo (length ctx)
    choice1 $ map tryVar vars

macro
  assumption : Tactic
  assumption = runTac assumption'
