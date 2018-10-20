{-# OPTIONS --without-K -v tac:10 #-}

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Container.List
open import Container.Traversable
open import Tactic.Reflection
open import Tactic.Deriving.Eq

void : ∀ {ℓ} {A : Set ℓ} → TC A → TC ⊤
void m = m >> return _

record Goal : Set where
  field
    theGoal : Term
    goalCtx : List (Arg Type)
open Goal

Tac = Term → TC (List Goal)

runTac : Tac → Tactic
runTac tac = void ∘ tac

macro
  run : Tac → Tactic
  run tac = runTac tac

applyTac : Tac → Goal → TC (List Goal)
applyTac tac goal = inContext (goal .goalCtx) $ do
  `tac ← quoteTC tac
  goalType ← inferType $ goal .theGoal
  debugPrint "tac.apply" 10 (strErr "Running tactic: " ∷ termErr `tac ∷ [])
  debugPrint "tac.apply" 10 (strErr "Goal:           " ∷ termErr (goal .theGoal) ∷ strErr ":" ∷ termErr goalType ∷ [])
  debugPrint "tac.apply" 10 (strErr "Context:        " ∷ map (termErr ∘ unArg) (goal .goalCtx))
  tac (goal .theGoal)

goalErr : Goal → TC (List ErrorPart)
goalErr goal = inContext (goal .goalCtx) $ do
  goalType ← inferType $ goal .theGoal
  return (termErr (goal .theGoal) ∷ strErr ":" ∷ termErr goalType ∷ [])

infixl 10 _and-then_
_and-then_ : Tac → Tac → Tac
(tac₁ and-then tac₂) goal = do
  subgoals ← tac₁ goal
  concat <$> traverse (applyTac tac₂) subgoals

infixl 10 _or-else_
_or-else_ : Tac → Tac → Tac
(tac₁ or-else tac₂) goal = tac₁ goal <|> tac₂ goal

pass : Tac
pass goal = getContext >>= λ ctx → return $ singleton λ where
  .theGoal → goal
  .goalCtx → ctx

try : Tac → Tac
try tac = tac or-else pass

now : Tac → Tac
now tac goal = do
  [] ← tac goal
    where subgoals → do
            unsolveds ← traverse goalErr subgoals
            typeError $ strErr "Unsolved subgoals: " ∷ concat unsolveds
  return []

repeat : Nat → Tac → Tac
repeat zero    tac = pass
repeat (suc k) tac = tac and-then repeat k tac

alreadySolved : Tac
alreadySolved goal = reduce goal >>= λ where
  goal@(meta _ _) → do
    goalType ← inferType goal
    typeError $ strErr "Unsolved subgoal: " ∷ termErr goal ∷ strErr ":" ∷ termErr goalType ∷ []
  _ → return []

unlessSolved : Tac → Tac
unlessSolved tac = alreadySolved or-else tac

{-
{-# TERMINATING #-}
allMetas : Term → TC (List Goal)
allMetas (var x args) = concat <$> traverse (allMetas ∘ unArg) args
allMetas (con c args) = concat <$> traverse (allMetas ∘ unArg) args
allMetas (def f args) = concat <$> traverse (allMetas ∘ unArg) args
allMetas (lam v (abs _ t)) = extendContext (arg (arg-info v relevant) unknown) (allMetas t)
allMetas (pat-lam cs args) = {!!}
allMetas (pi a b) = ⦇ allMetas (unArg a) ++ {!extendContext!} ⦈
allMetas (agda-sort s) = {!s!}
allMetas (lit l) = return []
allMetas (meta x args) = {!!}
allMetas unknown = return []

give' : Term → Tac
give' u goal = do
  unify u goal
  {!!}
-}

assumption' : Tac
assumption' = unlessSolved λ goal → do
    k ← length <$> getContext
    let tryVar : Nat → TC ⊤
        tryVar i = unify (var i []) goal
    choice $ map tryVar (from 0 to (k - 1))
    return []

macro
  assumption : Tactic
  assumption = runTac assumption'


intro' : Tac
intro' = unlessSolved λ goal → do
  pi a b ← reduce =<< inferType goal
    where t → typeError $ strErr "Not a function type: " ∷ termErr t ∷ []
  body ← extendContext a $ newMeta (unAbs b)
  let v = getVisibility a
  unify (lam v (body <$ b)) goal
  extendContext a $ pass body

macro
  intro : Tactic
  intro = runTac intro'

intros' : Nat → Tac
intros' k = repeat k intro'

macro
  intros : Tactic
  intros = runTac $ intros' 10


choice' : ∀ {a b} {F : Set a → Set b} {A : Set a} {{_ : Alternative F}}
        → List (F A) → F A
choice' [] = empty
choice' [ f ] = f
choice' (f ∷ fs) = f <|> choice' fs

{-# TERMINATING #-}
constr' : Tac
constr' goal = do
  def d us ← reduce =<< inferType goal
    where t → errorNotData t
  debugPrint "tac.constr" 10 (strErr "Searching constructor for" ∷ termErr (def d []) ∷ [])
  cons , #pars ← getDefinition d >>= λ where
    (data-type #pars cons) → return $ cons ,′ #pars
    (record-type c fields) → return $ singleton c , length us
    _                      → errorNotData (def d us)
  debugPrint "tac.constr" 10 (strErr "Constructors:         " ∷ map (λ c → termErr (con c [])) cons)
  debugPrint "tac.constr" 20 (strErr "Number of parameters: " ∷ strErr (show #pars) ∷ [])
  let pars = take #pars us
  choice' (map (λ c → tryConstr pars c goal) cons)

  where
    loop : Type → (List (Arg Term) → Term) → List Goal → Tac
    loop t hd subgoals goal = case t of λ where
      (pi a b) → do
        x    ← newMeta (unArg a)
        t'   ← reduce (lam visible b `$ x)
        newgoal ← pass x
        loop t' (hd ∘ ((x <$ a) ∷_)) (newgoal ++ subgoals) goal
      (def _ _) → do
        debugPrint "tac.constr" 10 (strErr "Trying solution: " ∷ termErr (hd []) ∷ [])
        `hd ← quoteTC (hd [])
        debugPrint "tac.constr" 30 (strErr "Trying solution: " ∷ termErr `hd ∷ [])
        debugPrint "tac.constr" 10 (strErr "Subgoals: " ∷ map (λ goal → termErr (goal .theGoal)) subgoals)
        unify (hd []) goal
        return subgoals
      t → typeError $ strErr "IMPOSSIBLE! Should be pi or def: " ∷ termErr t ∷ []

    applyToPars : List (Arg Term) → Type → TC Type
    applyToPars [] t = return t
    applyToPars (u ∷ us) t@(pi a b) = do
      debugPrint "tac.constr.pars" 30 (strErr "Applying to parameters: " ∷ termErr t ∷ [])
      just safe-u ← return $ maybeSafe (unArg u)
        where nothing → typeError $ strErr "Cannot substitute unsafe parameter: " ∷ termErr (unArg u) ∷ []
      let t' = substTerm (safe-u ∷ []) (unAbs b)
      applyToPars us t'
    applyToPars _ t = typeError $ strErr "IMPOSSIBLE! Should be pi: " ∷ termErr t ∷ []

    setHidden : {A : Set} → Arg A → Arg A
    setHidden (arg (arg-info _ r) x) = arg (arg-info hidden r) x

    tryConstr : List (Arg Term) → Name → Tac
    tryConstr pars c goal = do
      t ← getType c
      debugPrint "tac.constr" 10 (strErr "Type of constructor" ∷ termErr (con c []) ∷ strErr ":" ∷ termErr t ∷ [])
      t ← applyToPars pars t
      debugPrint "tac.constr" 10 (strErr " => applied to parameters:" ∷ termErr t ∷ [])
      let implicitPars = map setHidden pars
      loop t (λ args → con c (implicitPars ++ args)) [] goal

    errorNotData : {A : Set} → Term → TC A
    errorNotData t = typeError $ strErr "Not a data/record type: " ∷ termErr t ∷ []


macro
  constr : Tactic
  constr = runTac constr'

  constrs : Tactic
  constrs = runTac (repeat 10 constr')

mini-auto' : Tac
mini-auto' = repeat 10 (assumption' or-else intro' or-else constr')

macro
  mini-auto : Tactic
  mini-auto = runTac mini-auto'


test₁ : Nat → Bool → Nat
test₁ x y = assumption

test₂ : Nat → Bool → Bool
test₂ x y = assumption

test₄ : Nat → Bool → Nat
test₄ = mini-auto

test₅ : Bool
test₅ = constr

test₆ : Nat
test₆ = constr

test₇ : _≡_ {A = Bool} true true
test₇ = constr

test₈ : Vec Nat 0
test₈ = constrs

test₉ : Vec Bool 3
test₉ = constrs

test₁₀ : {A : Set} → A → Vec A 5
test₁₀ = mini-auto

data DecVec (n : Nat) : Nat → Set where
  []  : DecVec n zero
  cons : ∀ {k} → (m : Nat) → m < n → DecVec m k → DecVec n (suc k)

test₁₁ : DecVec 4 3
test₁₁ = mini-auto

test₁₂ : 5 ∈ from 2 to 7
test₁₂ = {!mini-auto!}
