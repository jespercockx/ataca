{-# OPTIONS --without-K --postfix-projections #-}

module Tactics.Constructor where

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Utils
open import Reflection
open import Core
open import Tactics.BasicTactics
open import Tactics.Refine

isDataOrRecord : Type → Tac (List (Arg Term) × List Name × Nat)
isDataOrRecord t = do
  def d us ← reduce t
    where _ → do
                debug "introConstructor" 9 $ strErr "Not a data/record type: " ∷ termErr t ∷ []
                backtrack
  debug "constr" 30 $ strErr "Found a def" ∷ termErr (def d []) ∷ strErr "applied to arguments" ∷ map (termErr ∘ unArg) us
  getDefinition d >>= λ where
    (data-type #pars cons) → do
      debug "constr" 20 $ strErr "It's a datatype applied to" ∷ strErr (show #pars) ∷ strErr "parameters" ∷ []
      return $ us , cons ,′ #pars
    (record-type c fields) → do
      debug "constr" 20 $ strErr "It's a record type" ∷ []
      return $ us , singleton c , length us
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
  introConstructor : TC.Tactic
  introConstructor = runTac introConstructor'

  introConstructors : TC.Tactic
  introConstructors = runTac $ repeat 10 (introConstructor' <|> return _)
