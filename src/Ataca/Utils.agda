{-# OPTIONS --no-qualified-instances #-}

module Ataca.Utils where

open import Data.Bool.Base public using (Bool; true; false) hiding (module Bool)
module Bool = Data.Bool.Base
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Fin.Base public using (Fin; zero; suc) hiding (module Fin)
module Fin = Data.Fin.Base
open import Data.List.Base public using (List; []; _∷_; [_]; map; foldl; foldr; length; _++_; take; drop; zipWith) hiding (module List)
module List = Data.List.Base
open import Data.Maybe.Base public using (Maybe; nothing; just)
open import Data.Nat.Base public using (ℕ; zero; suc) hiding (module ℕ)
module ℕ where
  open import Data.Nat.Base public
  open import Data.Nat.Show public
open import Data.Product public using (Σ; _×_; _,_; _,′_; curry; uncurry) renaming (proj₁ to fst; proj₂ to snd; map₁ to first; map₂ to second)
open import Data.String.Base public using (String)
module String = Data.String.Base
open import Data.Sum.Base public using (_⊎_) renaming (inj₁ to left; inj₂ to right)
open import Data.Unit public using (⊤; tt)
open import Data.Vec.Base public using (Vec; []; _∷_) hiding (module Vec)
module Vec = Data.Vec.Base

open import Function.Base public using (const; id; flip; _∘_; _$_; it; case_of_)

open import Level public using (Level; Setω; 0ℓ; _⊔_; Lift; lift; lower) renaming (suc to sucℓ)

open import Relation.Binary.PropositionalEquality using (_≡_; refl) public

open import Reflection.AST.Term public
open import Reflection.AST.Name public using (Name)
open import Reflection.AST.Definition public hiding (_≟_)
open import Reflection.AST.Abstraction public using (Abs; abs; unAbs)
open import Reflection.AST.Argument public using (Arg; arg; vArg; hArg; unArg)
open import Reflection.AST.Argument.Modality using (Modality) public
open import Reflection.AST.Argument.Visibility using (Visibility; visible; instance′; hidden) public
open import Reflection.AST.Argument.Relevance using (Relevance; relevant; irrelevant) public
open import Reflection.AST.Argument.Information public using (ArgInfo; arg-info; visibility; modality)

open import Data.List.Instances public -- hiding (listMonadT)
open import Data.Maybe.Instances public -- hiding (maybeMonadT)
open import Reflection.TCM.Instances public

open import Reflection.TCM public using (ErrorPart; strErr; termErr)

open import Effect.Empty public using () renaming (RawEmpty to Empty)
open import Effect.Choice public using () renaming (RawChoice to Choice)
open import Effect.Functor public using () renaming (RawFunctor to Functor)
open import Effect.Applicative public using ()
  renaming ( RawApplicative to Applicative
           ; RawApplicativeZero to ApplicativeZero
           ; RawAlternative to Alternative
           )
open import Effect.Monad public using () renaming ( RawMonad to Monad ; mkRawMonad to mkMonad)
open Functor         {{...}} public using (_<$>_; _<$_)
open Applicative     {{...}} public using (pure) renaming (_⊛_ to _<*>_)
open ApplicativeZero {{...}} public using () renaming (∅ to empty)
open Alternative     {{...}} public using () renaming (_∣_ to _<|>_)
open Monad           {{...}} public using (return; _>>=_; _>>_)

-- Generalized names

variable
  k l m n : ℕ
  ℓ ℓ′ ℓ″ : Level
  A B C : Set ℓ
  F M : Set ℓ → Set ℓ′

-- Some utility functions

for : List A → (A → B) → List B
for = flip map

fmap = _<$>_

void : {{Functor F}} → F A → F ⊤
void m = const _ <$> m

choice1 : {{Alternative F}} → List (F A) → F A
choice1 []       = empty
  where instance applicativeZeroF = Alternative.rawApplicativeZero it
choice1 (f ∷ []) = f
choice1 (f ∷ fs) = f <|> choice1 fs

monadAp : {{Monad M}} → M (A → B) → M A → M B
monadAp {{monadM}} mf mx = do
  f ← mf
  x ← mx
  return (f x)

traverse : {{Monad M}} → (A → M B) → List A → M (List B)
traverse f [] = return []
traverse f (mx ∷ mxs) = do
  x  ← f mx
  xs ← traverse f mxs
  return (x ∷ xs)

mapLift′ : (f : A → B) → Lift ℓ A → Lift ℓ′ B
mapLift′ f (lift x) = lift (f x)

mapLift : (f : A → B) → Lift ℓ A → Lift ℓ B
mapLift = mapLift′

record FunctorLift {a} (F : ∀ {ℓ′} → Set ℓ′ → Set ℓ′) ℓ (A : Set a) : Set (sucℓ ℓ ⊔ a) where
  field
    liftF   : F A → F (Lift ℓ A)
    lowerF  : F (Lift ℓ A) → F A

open FunctorLift {{...}} public

-- Reflection stuff

module TC where
  open import Reflection.TCM public
  newMeta! = newMeta unknown

TC = TC.TC

Tactic = Term → TC ⊤

makeImplicit : Arg A → Arg A
makeImplicit (arg (arg-info v r) x) = arg (arg-info hidden r) x

extendCtxTel : Telescope → TC A → TC A
extendCtxTel []              = id
extendCtxTel ((x , a) ∷ tel) = TC.extendContext x a ∘ extendCtxTel tel

goalErr : Term → TC (List TC.ErrorPart)
goalErr goal = do
  goalType ← TC.inferType goal
  return $ TC.termErr goal ∷ TC.strErr ":" ∷ TC.termErr goalType ∷ []

piView : Type → TC (Maybe (Arg Type × Abs Type))
piView = λ where
    -- HACK: first try without reducing the type to avoid creating
    -- spurious constraints, then try again if that doesn't work.
    (pi a b) → return $ just (a , b)
    t → TC.reduce t >>= λ where
      (pi a b) → return $ just (a , b)
      _        → return nothing

{-# TERMINATING #-}
telePi : Type → TC (Telescope × Type)
telePi t = piView t >>= λ where
  (just (a , (abs x b))) → first ((x , a) ∷_) <$> TC.extendContext x a (telePi b)
  nothing → return ([] , t)

getArgInfo : Arg A → ArgInfo
getArgInfo (arg i _) = i

teleArgInfos : Telescope → List ArgInfo
teleArgInfos = map (getArgInfo ∘ snd)

piArgInfos : Type → TC (List ArgInfo)
piArgInfos t = teleArgInfos ∘ fst <$> telePi t

instance
  functorLiftTC : FunctorLift TC ℓ A
  functorLiftTC .liftF   = λ mx → TC.bindTC mx (λ x → TC.pure (lift x))
  functorLiftTC .lowerF  = λ mx → TC.bindTC mx (λ x → TC.pure (lower x))
