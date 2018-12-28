--{-# OPTIONS -v tac:49 #-}

open import Prelude
open import Container.List

open import Tactics

open import Tac
open import Utils

test₀ : Nat
test₀ = run doIt
  where
    doIt : Tac ⊤
    doIt = choice1 $
      (do
        x    ← newMeta!
        hole ← getHole
        Tac.unify hole (con (quote Nat.suc) (arg (arg-info visible relevant) x ∷ []))
        backtrack)
      ∷ (do
        hole ← getHole
        unify hole (con (quote Nat.zero) []))
      ∷ []

test₁ : Nat
test₁ = exact 42

test₂ : Nat → Bool → Nat
test₂ x y = mini-auto

test₃ : Nat → Bool → Bool
test₃ x y = mini-auto

test₄ : Nat → Bool → Nat
test₄ = mini-auto

test₅ : Bool
test₅ = mini-auto

test₆ : Nat
test₆ = mini-auto

test₇ : _≡_ {A = Bool} true true
test₇ = mini-auto

test₈ : Vec Nat 0
test₈ = mini-auto

test₉ : Vec Bool 3
test₉ = mini-auto

test₁₀ : {A : Set} → A → Vec A 5
test₁₀ = mini-auto

data DecrVec (n : Nat) : Nat → Set where
  []   : DecrVec n zero
  cons : ∀ {k} → (m : Nat) → m < n → DecrVec m k → DecrVec n (suc k)

test₁₁ : DecrVec 4 3
test₁₁ = mini-auto

data NatList : Set where
  []  : NatList
  _∷_ : (x : Nat) (xs : NatList) → NatList

data Is1 : Nat → Set where
  instance is1 : Is1 1

data Any1 : NatList → Set where
  instance
    zero : ∀ {x xs} (p : Is1 x) → Any1 (x ∷ xs)
    suc  : ∀ {x xs} (i : Any1 xs) → Any1 (x ∷ xs)

test₁₂ : Any1 (zero ∷ (suc zero) ∷ [])
test₁₂ = mini-auto

postulate
  Atype Btype : Set
  fun : Atype → Btype

test₁₃ : Atype → Btype
test₁₃ = mini-auto-with hints
  where hints = def (quote fun) [] ∷ []

postulate
  P=NP : Set

proof : P=NP
proof = run do
  try mini-auto'
  admit'

test₁₄ : {A : Set} → ⊥ → A
test₁₄ = mini-auto
