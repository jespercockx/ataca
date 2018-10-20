{-# OPTIONS --without-K --postfix-projections #-}

module Tactics.Assumption where

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Utils
open import Tac
open import Tactics.Exact

tryVar : Nat → Tac A
tryVar i = do
  debug "assumption" 10 $ strErr "Trying variable" ∷ strErr (show i) ∷ []
  exact' $ var i []

assumption' : Tac A
assumption' = unlessSolved $ do
    ctx ← getContext
    debug "assumption" 20 $ strErr "Current context:" ∷ map (termErr ∘ unArg) ctx
    let vars = (if null ctx then [] else from 0 to (length ctx - 1))
    choice $ map tryVar vars

macro
  assumption : Tactic
  assumption = toMacro assumption'
