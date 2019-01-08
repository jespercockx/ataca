{-# OPTIONS --without-K --postfix-projections #-}

module Tactics.Destruct where

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Container.Traversable
open import Utils
open import Reflection
open import Core
open import Tactics.BasicTactics
open import Tactics.Exact
open import Tactics.Constructor

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
    ?rhs ← newMeta!
    let pat : Pattern
        pat = con (quote ⌊_⌋) (TC.vArg (con c $ map (λ i → arg i (var "_")) ais) ∷ [])
    return $ (?rhs , tel) ,  clause (TC.vArg pat ∷ []) ?rhs

  let
    solution : Term
    solution = def (quote split) (
      TC.vArg u ∷
      TC.vArg (pat-lam (map snd cls) []) ∷ [])

  debug "destruct" 10 (strErr "Destruct solution: " ∷ termErr solution ∷ [])

  hole ← getHole
  unify hole solution
  forEach cls λ where
    ((?rhs , tel) , _) → do
      traverse addCtx tel
      rhsType ← inferType ?rhs
      debug "destruct" 20 (strErr "Destruct subgoal: " ∷ termErr ?rhs ∷ strErr ":" ∷ termErr rhsType ∷ [])
      debug "destruct" 20 (strErr "Destruct subgoal context: " ∷ map (termErr ∘ unArg) tel)
      setHole ?rhs



macro
  destruct : Term → Term → TC ⊤
  destruct u = runTac $ destruct' u
