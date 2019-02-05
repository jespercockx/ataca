{-# OPTIONS --without-K --postfix-projections #-}

module Ataca.Tactics.Destruct where

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Container.Traversable

open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics.BasicTactics
open import Ataca.Tactics.Exact
open import Ataca.Tactics.Constructor

data Is {A : Set ℓ} : A → Set ℓ where
  ⌊_⌋ : (x : A) → Is x

split : (x : A) → (Is x → B) → B
split x f = f ⌊ x ⌋

{-# NOINLINE split #-}

destruct' : Term → Tac ⊤
destruct' u = do
  t ← inferType u
  us , cons , #pars ← isDataOrRecord t
  cls ← flip traverse cons λ c → do
    ct   ← getType c
    tel , ctarget ← liftTC $ telePi ct
    let ais = teleArgInfos tel
    debug "destruct" 40 $ strErr "Constructor" ∷ termErr (con c []) ∷ strErr "with type" ∷ termErr ct ∷ []
    let pat : Pattern
        pat = con (quote ⌊_⌋) (TC.vArg (con c $ map (λ i → arg i (var "_")) ais) ∷ [])
    return $ clause (TC.vArg pat ∷ []) unknown

  let
    solution : Term
    solution = def (quote split) (
      TC.vArg u ∷
      TC.vArg (pat-lam cls []) ∷ [])

  debug "destruct" 10 (strErr "Destruct solution: " ∷ termErr solution ∷ [])

  hole ← getHole
  unify hole solution
  pat-lam cls' _ ← reduce hole
    where _ → liftTC $ TC.typeError (strErr "IMPOSSIBLE" ∷ [])
  forEach cls' λ where
    (clause ps ?rhs) → do
      rhsType ← inferType ?rhs
      debug "destruct" 20 (strErr "Destruct subgoal: " ∷ termErr ?rhs ∷ strErr ":" ∷ termErr rhsType ∷ [])
      -- TODO: Set the right context
      setHole ?rhs
    (absurd-clause _) → liftTC $ TC.typeError (strErr "IMPOSSIBLE" ∷ [])



macro
  destruct : Term → Term → TC ⊤
  destruct u = runTac $ destruct' u
