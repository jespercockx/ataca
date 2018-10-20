{-# OPTIONS --without-K --postfix-projections #-}

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Utils
open import Tac

exact' : Term → Tac A
exact' solution = unlessSolved $ do
  hole ← getHole
  debug "exact" 10 $ strErr "Solving goal" ∷ termErr hole ∷ strErr "with solution" ∷ termErr solution ∷ []
  unify hole solution
  skip

macro
  exact : A → Tactic
  exact u = toMacro $ (quoteTac u) >>= exact'
