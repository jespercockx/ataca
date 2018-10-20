{-# OPTIONS --without-K --postfix-projections #-}

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Utils
open import Tac
open import Refine

getConstructor : Type → Tac ((List (Arg Term) → Term) × List ArgInfo)
getConstructor t = do
  debug "constr" 30 $ strErr "Now reducing" ∷ termErr t ∷ []
  def d us ← reduce t
    where _ → fail $ strErr "Not a data/record type: " ∷ termErr t ∷ []
  debug "constr" 30 $ strErr "Found a def" ∷ termErr (def d []) ∷ strErr "applied to arguments" ∷ map (termErr ∘ unArg) us
  cons , #pars ← getDefinition d >>= λ where
    (data-type #pars cons) → do
      debug "constr" 20 $ strErr "It's a datatype applied to" ∷ strErr (show #pars) ∷ strErr "parameters" ∷ []
      return $ cons ,′ #pars
    (record-type c fields) → do
      debug "constr" 20 $ strErr "It's a record type" ∷ []
      return $ singleton c , length us
    _                      → fail $ strErr "Not a data/record type: " ∷ termErr t ∷ []
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
  _ , holeType ← getGoal
  debug "constr" 20 $ strErr "Hole type: " ∷ termErr holeType ∷ []
  c , is ← getConstructor holeType
  refineN' is c

macro
  introConstructor : Tactic
  introConstructor = toMacro introConstructor'

  introConstructors : Tactic
  introConstructors = toMacro $ repeat 10 introConstructor'
