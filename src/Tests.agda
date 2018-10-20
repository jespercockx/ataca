
open import Prelude
open import Container.List
open import Tactic.Reflection

open import Tactics

test₀ : Nat
test₀ = exact 42

test₁ : Nat → Bool → Nat
test₁ x y = mini-auto

test₂ : Nat → Bool → Bool
test₂ x y = mini-auto

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

test₁₂ : 5 ∈ from 2 to 7
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
