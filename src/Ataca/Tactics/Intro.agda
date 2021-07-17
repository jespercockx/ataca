{-# OPTIONS --postfix-projections #-}

module Ataca.Tactics.Intro where

open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics.BasicTactics

intro' : Tac ⊤
intro' = unlessSolved $ do
  hole , holeType ← getHoleWithType
  debug "intro" 10 $ strErr "Trying intro on" ∷ termErr holeType ∷ []
  pi a@(arg i _) b@(abs x _) ← reduce holeType
    where t → do
                debug "intro" 8 $ strErr "Not a function type: " ∷ termErr t ∷ []
                backtrack
  body ← newMetaCtx ((x , a) ∷ []) $ unAbs b
  let v = visibility i
  unify hole (lam v (abs x body))
  addCtx a
  setHole body

macro
  intro : Tactic
  intro = runTac intro'

  intros : Tactic
  intros = runTac $ repeat 10 (intro' <|> return _)

introAbsurd' : Tac ⊤
introAbsurd' = unlessSolved $ do
  hole , holeType ← getHoleWithType
  debug "intro" 10 $ strErr "Trying introAbsurd on" ∷ termErr holeType ∷ []
  pi a@(arg i _) b ← reduce holeType
    where t → do
                debug "intro" 8 $ strErr "Not a function type: " ∷ termErr t ∷ []
                backtrack
  unify hole (pat-lam [ absurd-clause [] [ arg i (absurd 0) ] ] [])
  qed

macro
  introAbsurd = runTac introAbsurd'
