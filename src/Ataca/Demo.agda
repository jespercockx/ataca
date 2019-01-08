
open import Prelude
open import Container.List

open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics

module Ataca.Demo where

test₁ : Nat
test₁ = {! exact 42 !}

test₂ : Nat → Bool → Nat
test₂ x y = {! assumption !}

test₃ : Nat → Bool → Bool
test₃ x y = {! assumption !}

test₄ : Nat → Bool → Nat
test₄ = {! intros !}

test₅ : Bool
test₅ = {! introConstructor !}

test₆ : Nat
test₆ = {! introConstructor !}

test₇ : _≡_ {A = Bool} true true
test₇ = {! introConstructor !}

test₈ : Vec Nat 0
test₈ = {! introConstructor!}

test₉ : Vec Bool 3
test₉ = {! introConstructors !}

test₁₀ : {A : Set} → A → Vec A 5
test₁₀ = {! mini-auto !}

data DecrVec (n : Nat) : Nat → Set where
  []   : DecrVec n zero
  cons : ∀ {k} → (m : Nat) → m < n → DecrVec m k → DecrVec n (suc k)

test₁₁ : DecrVec 4 3
test₁₁ = {! mini-auto !}

test₁₂ : Any {A = Nat} (_≡ 1) (zero ∷ (suc zero) ∷ [])
test₁₂ = {! mini-auto !}

postulate
  X Y : Set
  fun : X → Y

test₁₃ : X → Y
test₁₃ = {! mini-auto-with hints !}
  where
    hints : Hints
    hints = def (quote fun) [] ∷ []

test₁₄ : {A : Set} → ⊥ → A
test₁₄ = {! mini-auto !}

test₁₅ : (x : Nat) → Either (x ≡ 0) (Σ Nat λ y → x ≡ suc y)
test₁₅ x = {! destruct x !}


postulate
  P=NP : Set

proof : P=NP
proof = run do
  try mini-auto'
  admit'
