{-# OPTIONS --postfix-projections #-}

module Ataca.Tactics.Constructor where

open import Ataca.Utils
open import Ataca.Core
open import Ataca.Tactics.BasicTactics
open import Ataca.Tactics.Refine

isDataOrRecord : Type → Tac (List (Arg Term) × List Name × ℕ)
isDataOrRecord t = do
  def d us ← reduce t
    where _ → do
                debug "introConstructor" 9 $ strErr "Not a data/record type: " ∷ termErr t ∷ []
                backtrack
  debug "constr" 30 $ strErr "Found a def" ∷ termErr (def d []) ∷ strErr "applied to arguments" ∷ map (termErr ∘ unArg) us
  getDefinition d >>= λ where
    (data-type #pars cons) → do
      debug "constr" 20 $ strErr "It's a datatype applied to" ∷ strErr (ℕ.show #pars) ∷ strErr "parameters" ∷ []
      return $ us , cons ,′ #pars
    (record′ c fields) → do
      debug "constr" 20 $ strErr "It's a record type" ∷ []
      return $ us , [ c ] , length us
    _                      → do
      debug "introConstructor" 9 $ strErr "Not a data/record type: " ∷ termErr t ∷ []
      backtrack

getConstructor : Type → Tac ((List (Arg Term) → Term) × List ArgInfo)
getConstructor t = do
  us , cons , #pars ← isDataOrRecord t
  let pars = take #pars us
      ipars = map makeImplicit pars
  choice1 $ for cons $ λ c → do
    t ← getType c
    debug "constr" 10 $ strErr "Constructor" ∷ termErr (con c []) ∷ strErr "has type" ∷ termErr t ∷ []
    ais ← liftTC $ piArgInfos t
    debug "constr" 10 $ strErr "Now trying constructor" ∷ termErr (con c []) ∷ []
    return $ (λ args → con c (ipars ++ args)) , drop #pars ais

introConstructor' : Tac ⊤
introConstructor' = do
  _ , holeType ← getHoleWithType
  debug "constr" 20 $ strErr "Trying introConstructor on " ∷ termErr holeType ∷ []
  c , is ← getConstructor holeType
  refineN' is c

macro
  introConstructor : Tactic
  introConstructor = runTac introConstructor'

  introConstructors : Tactic
  introConstructors = runTac $ repeat 10 (introConstructor' <|> return _)
