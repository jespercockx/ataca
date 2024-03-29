{-# OPTIONS --postfix-projections #-}

module Ataca.Tactics.Refine where

open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics.BasicTactics

refineN' : List ArgInfo → (List (Arg Term) → Term) → Tac ⊤
refineN' is hd = do
  debug "refine" 10 $ strErr "Trying to refine goal with" ∷ termErr (hd []) ∷ strErr "applied to" ∷ strErr (ℕ.show (length is)) ∷ strErr "arguments" ∷ []
  loop is hd []

  where
    loop : List ArgInfo → (List (Arg Term) → Term) → List Term → Tac ⊤
    loop [] hd subgoals       = do
      hole ← getHole
      debug "refine" 15 $ strErr "Solving goal" ∷ termErr hole ∷ strErr "with solution" ∷ termErr (hd []) ∷ []
      unify hole (hd [])
      debug "refine" 15 $ strErr "Instantiation successful, new subgoals" ∷ map termErr subgoals
      forEach subgoals setHole
    loop (i ∷ is) hd subgoals = do
      x ← newMeta!
      loop is (hd ∘ (arg i x ∷_)) (x ∷ subgoals)

refine' : Term → Tac ⊤
refine' u = do
  hd , t ← case u of λ where
    (var x us)    → ⦇ return (λ vs → var x (us ++ vs)) , inferType (var x us) ⦈
    (con c [])    → ⦇ return (con c) , getType c ⦈
    (con c us)    → ⦇ return (λ vs → con c (us ++ vs)) , inferType (con c us) ⦈
    (def f [])    → ⦇ return (def f) , getType f ⦈
    (def f us)    → ⦇ return (λ vs → def f (us ++ vs)) , inferType (def f us) ⦈
    (pi a b)      → ⦇ return (const $ pi a b) , (inferType (pi a b)) ⦈
    (sort s)      → ⦇ return (const $ sort s) , (inferType (sort s)) ⦈
    (lit l)       → ⦇ return (const $ lit l) , (inferType (lit l)) ⦈
    (meta x us)   → ⦇ return (λ vs → meta x (us ++ vs)) , inferType (meta x us) ⦈
    _ → error $ strErr "Not supported by refine: " ∷ termErr u ∷ []
  is ← liftTC $ piArgInfos t
  choice1 $ for (List.upTo (length is)) λ #args →
    refineN' (take #args is) hd

macro
  refine : Term → Tactic
  refine u = runTac $ refine' u
