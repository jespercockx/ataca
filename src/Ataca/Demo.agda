
open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics

open import Agda.Builtin.Nat
open import Data.List.Relation.Unary.Any

module Ataca.Demo where

test₁ : ℕ
test₁ = {! exact 42 !}

test₂ : ℕ → Bool → ℕ
test₂ x y = {! assumption !}

test₃ : ℕ → Bool → Bool
test₃ x y = {! assumption !}

test₄ : ℕ → Bool → ℕ
test₄ = {! intros !}

test₅ : Bool
test₅ = {! introConstructor !}

test₆ : ℕ
test₆ = {! introConstructor !}

test₇ : _≡_ {A = Bool} true true
test₇ = {! introConstructor !}

test₈ : Vec ℕ 0
test₈ = {! introConstructor!}

test₉ : Vec Bool 3
test₉ = {! introConstructors !}

test₁₀ : {A : Set} → A → Vec A 5
test₁₀ = {! mini-auto !}

data DecrVec (n : ℕ) : ℕ → Set where
  []   : DecrVec n zero
  cons : ∀ {k} → (m : ℕ) → m ℕ.< n → DecrVec m k → DecrVec n (suc k)

test₁₁ : DecrVec 4 3
test₁₁ = {! mini-auto !}

test₁₂ : Any {A = ℕ} (_≡ 1) (zero ∷ (suc zero) ∷ [])
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
test₁₄ = {! mini-auto!}

-- Doesn't work yet
-- test₁₅ : (x : ℕ) → (x ≡ 0) ⊎ (Σ ℕ λ y → x ≡ suc y)
-- test₁₅ x =  {! destruct x !}

postulate
  P=NP : Set

proof : P=NP
proof = run do
  try mini-auto'
  admit'
