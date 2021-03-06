open import Prelude
open import Tactic.Reflection

module Ataca.Utils where

-- Generalized names

variable
  k l m n : Nat
  ℓ ℓ′ : Level
  A B C : Set ℓ
  F M : Set ℓ → Set ℓ′

-- Some utility functions

void : {{_ : Functor F}} → F A → F ⊤
void m = const _ <$> m

choice1 : {{_ : Alternative F}} → List (F A) → F A
choice1 []       = empty
choice1 [ f ]    = f
choice1 (f ∷ fs) = f <|> choice1 fs

-- Reflection stuff

makeImplicit : Arg A → Arg A
makeImplicit (arg (arg-info v r) x) = arg (arg-info hidden r) x

extendCtxTel : Telescope → TC A → TC A
extendCtxTel []        = id
extendCtxTel (a ∷ tel) = extendContext a ∘ extendCtxTel tel

goalErr : Term → TC (List ErrorPart)
goalErr goal = do
  goalType ← inferType goal
  return $ termErr goal ∷ strErr ":" ∷ termErr goalType ∷ []

piView : Type → TC (Maybe (Arg Type × Abs Type))
piView = λ where
    -- HACK: first try without reducing the type to avoid creating
    -- spurious constraints, then try again if that doesn't work.
    (pi a b) → return $ just (a , b)
    t → reduce t >>= λ where
      (pi a b) → return $ just (a , b)
      _        → return nothing

{-# TERMINATING #-}
telePi : Type → TC (Telescope × Type)
telePi t = piView t >>= λ where
  (just (a , (abs _ b))) → first (a ∷_) <$> extendContext a (telePi b)
  nothing → return ([] , t)

teleArgInfos : Telescope → List ArgInfo
teleArgInfos = map getArgInfo

piArgInfos : Type → TC (List ArgInfo)
piArgInfos t = teleArgInfos ∘ fst <$> telePi t
