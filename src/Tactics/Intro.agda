{-# OPTIONS --without-K --postfix-projections #-}

module Tactics.Intro where

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Utils
open import Core
open import Tactics.BasicTactics

intro' : Tac ⊤
intro' = unlessSolved $ do
  hole , holeType ← getHoleWithType
  debug "intro" 10 $ strErr "Trying intro on" ∷ termErr holeType ∷ []
  pi a b ← reduce holeType
    where t → do
                debug "intro" 8 $ strErr "Not a function type: " ∷ termErr t ∷ []
                backtrack
  body ← newMetaCtx (a ∷ []) $ unAbs b
  let v = getVisibility a
  unify hole (lam v (body <$ b))
  addCtx a
  setHole body

macro
  intro : TC.Tactic
  intro = runTac intro'

  intros : TC.Tactic
  intros = runTac $ repeat 10 (intro' <|> return _)

introAbsurd' : Tac ⊤
introAbsurd' = unlessSolved $ do
  hole , holeType ← getHoleWithType
  debug "intro" 10 $ strErr "Trying introAbsurd on" ∷ termErr holeType ∷ []
  pi a b ← reduce holeType
    where t → do
                debug "intro" 8 $ strErr "Not a function type: " ∷ termErr t ∷ []
                backtrack
  unify hole (pat-lam [ absurd-clause [ absurd <$ a ] ] [])
  qed

macro
  introAbsurd = runTac introAbsurd'
