open import Prelude
open import Tactic.Reflection

-- Generalized names

variable
  k l m n : Nat
  ℓ ℓ′ : Level
  A B C : Set ℓ
  F M : Set ℓ → Set ℓ′

-- Some utility functions

void : {{_ : Monad M}} → M A → M ⊤
void m = m >> return _

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

{-# TERMINATING #-}
piArgInfos : Type → TC (List ArgInfo)
piArgInfos = λ where
    -- HACK: first try without reducing the type to avoid creating
    -- spurious constraints, then try again if that doesn't work.
    (pi a (abs _ b)) → recurse a b
    t → reduce t >>= λ where
      (pi a (abs _ b)) → recurse a b
      _                → return []

  where recurse = λ a b → (getArgInfo a ∷_) <$> extendContext a (piArgInfos b)
