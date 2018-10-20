{-# OPTIONS --without-K --postfix-projections #-}

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Utils
open import Tac

intro' : Tac ⊤
intro' = unlessSolved $ do
  hole , holeType ← getGoal
  debug "intro" 10 $ strErr "Trying intro on" ∷ termErr holeType ∷ []
  pi a b ← reduce holeType
    where t → fail $ strErr "Not a function type: " ∷ termErr t ∷ []
  body ← newMetaCtx (a ∷ []) $ unAbs b
  let v = getVisibility a
  unify hole (lam v (body <$ b))
  addCtx a
  defer body

macro
  intro : Tactic
  intro = toMacro intro'

  intros : Tactic
  intros = toMacro $ repeat 10 intro'
