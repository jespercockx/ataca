
open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics

module Ataca.Tests where

test₀ : ℕ
test₀ = run doIt
  where
    doIt : Tac ⊤
    doIt = choice1 $
      (do
        x    ← newMeta!
        hole ← getHole
        unify hole (con (quote ℕ.suc) (vArg x ∷ []))
        backtrack)
      ∷ (do
        hole ← getHole
        unify hole (con (quote ℕ.zero) []))
      ∷ []

test₁ : ℕ
test₁ = exact 42

test₂ : ℕ → Bool → ℕ
test₂ x y = x

test₃ : ℕ → Bool → Bool
test₃ x y = mini-auto

test₄ : ℕ → Bool → ℕ
test₄ = mini-auto

test₅ : Bool
test₅ = mini-auto

test₆ : ℕ
test₆ = mini-auto

test₇ : true ≡ true
test₇ = mini-auto

test₈ : Vec ℕ 0
test₈ = mini-auto

test₉ : Vec Bool 3
test₉ = mini-auto

test₁₀ : {A : Set} → A → Vec A 5
test₁₀ = mini-auto

data DecrVec (n : ℕ) : ℕ → Set where
  []   : DecrVec n zero
  cons : ∀ {k} → (m : ℕ) → m ℕ.< n → DecrVec m k → DecrVec n (suc k)

test₁₁ : DecrVec 4 3
test₁₁ = mini-auto

data ℕList : Set where
  []  : ℕList
  _∷_ : (x : ℕ) (xs : ℕList) → ℕList

data Is1 : ℕ → Set where
  instance is1 : Is1 1

data Any1 : ℕList → Set where
  instance
    zero : ∀ {x xs} {{p : Is1 x}} → Any1 (x ∷ xs)
    suc  : ∀ {x xs} {{i : Any1 xs}} → Any1 (x ∷ xs)

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
