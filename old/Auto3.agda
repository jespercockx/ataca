{-# OPTIONS --without-K -v tac.refine:50 #-}

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Container.List
open import Container.Traversable
open import Tactic.Reflection
open import Tactic.Deriving.Eq

void : ∀ {ℓ} {A : Set ℓ} → TC A → TC ⊤
void m = m >> return _

choice' : ∀ {a b} {F : Set a → Set b} {A : Set a} {{_ : Alternative F}}
        → List (F A) → F A
choice' [] = empty
choice' [ f ] = f
choice' (f ∷ fs) = f <|> choice' fs


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

MultiTac = Term → TC (List (Bool × Tac))

toMulti : Bool → Tac → MultiTac
toMulti b tac _ = return $ singleton (b , tac)

fromMulti : MultiTac → Tac
fromMulti mtac goal = tryTacs =<< mtac goal
  where
    tryTacs : List (Bool × Tac) → TC (List Goal)
    tryTacs tacs = choice' (for tacs (λ { (_ , tac) → tac goal }))

runMultiTac : MultiTac → Tactic
runMultiTac = runTac ∘ fromMulti

repeatMulti : Nat → MultiTac → Tac
repeatMulti 0 mtac goal = pass goal
repeatMulti (suc k) mtac goal = do
    tacs ← mtac goal
    `tacs ← traverse (quoteTC ∘ snd) tacs
    debugPrint "tac.repeat" 10 (strErr "Tactic menu: " ∷ map termErr `tacs)
    tryTacs tacs goal
  where
    tryTacs : List (Bool × Tac) → Tac
    tryTacs [] goal = typeError $ strErr "Give at least one tactic to repeat" ∷ []
    --tryTacs ((_     , tac) ∷ []  ) goal = tac goal
    tryTacs ((true  , tac) ∷ tacs) goal = do
      `tac ← quoteTC tac
      debugPrint "tac.repeat" 10 (strErr "Trying tactic" ∷ termErr `tac ∷ [])
      just subgoals ← maybeA $ tac goal
        where nothing → tryTacs tacs goal
      debugPrint "tac.repeat" 10 (strErr "Tactic" ∷ termErr `tac ∷ strErr "was succesful!" ∷ [])
      `subgoals ← concat <$> traverse goalErr subgoals
      -- TODO: this throws errors while printing!
      --debugPrint "tac.repeat" 10 (strErr "Subgoals:" ∷ `subgoals)
      concat <$> traverse (applyTac (repeatMulti k mtac)) subgoals
    tryTacs ((false , tac) ∷ tacs) =
      ((tac and-then repeatMulti k mtac) or-else tryTacs tacs)

_or-else-multi_ : MultiTac → MultiTac → MultiTac
(mtac₁ or-else-multi mtac₂) goal = ⦇ mtac₁ goal ++ mtac₂ goal ⦈

exact' : Term → Tac
exact' u goal = unify u goal >> return []

macro
  exact : Term → Tactic
  exact u = runTac $ exact' u


assumption' : Tac
assumption' = unlessSolved λ goal → do
    goalType ← inferType goal
    debugPrint "tac.constr" 10 (strErr "Trying assumption on" ∷ termErr goalType ∷ [])
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
  goalType ← inferType goal
  debugPrint "tac.constr" 10 (strErr "Trying intro on" ∷ termErr goalType ∷ [])
  pi a b ← reduce goalType
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

{-# TERMINATING #-}
constr' : MultiTac
constr' goal = do
  goalType ← inferType goal
  debugPrint "tac.constr" 10 (strErr "Searching constructor for" ∷ termErr goalType ∷ [])
  def d us ← reduce goalType
    where t → do
            debugPrint "tac.constr" 10 $ strErr "Not a data/record type: " ∷ termErr t ∷ []
            return []
  cons , #pars ← getDefinition d >>= λ where
    (data-type #pars cons) → return $ cons ,′ #pars
    (record-type c fields) → return $ singleton c , length us
    _                      → do
      debugPrint "tac.constr" 10 $ strErr "Not a data/record type: " ∷ termErr (def d us) ∷ []
      return $ [] , 0
  debugPrint "tac.constr" 10 (strErr "Constructors:         " ∷ map (λ c → termErr (con c [])) cons)
  debugPrint "tac.constr" 20 (strErr "Number of parameters: " ∷ strErr (show #pars) ∷ [])
  let pars = take #pars us
  return $ map (λ c → false , tryConstr pars c) cons

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



macro
  constr : Tactic
  constr = runMultiTac constr'

  constrs : Tactic
  constrs = runTac (repeatMulti 10 constr')

refineAux' : Nat → Type → (List (Arg Term) → Term) → List Goal → Tac
refineAux' zero    t hd subgoals goal = do
  debugPrint "tac.refine" 10 $ strErr "Trying solution: " ∷ termErr (hd []) ∷ []
  debugPrint "tac.refine" 30 $ strErr "  type of head" ∷ termErr t ∷ []
  unify (hd []) goal
  return subgoals
refineAux' (suc n) t hd subgoals goal = do
  debugPrint "tac.refine" 30 $ strErr "  applying" ∷ termErr (hd []) ∷ strErr "to" ∷ strErr (show {A = Nat} (suc n)) ∷ strErr "more arguments..." ∷ []
  debugPrint "tac.refine" 30 $ strErr "  type of head" ∷ termErr t ∷ []
  `t ← normalise =<< quoteTC t
  debugPrint "tac.refine" 50 $ strErr "  raw type" ∷ termErr `t ∷ []
  pi (arg ai a) b ← reduce t
    where t → do
            debugPrint "tac.refine" 10 $ strErr "Not a pi type: " ∷ termErr t ∷ []
            typeError $ strErr "Should be a pi type: " ∷ termErr t ∷ []
  debugPrint "tac.refine" 30 $ strErr "Creating new meta of type " ∷ termErr a ∷ []
  ctx ← getContext
  debugPrint "tac.refine" 30 $ strErr "Current context " ∷ map (termErr ∘ unArg) ctx
  x ← newMeta a
  debugPrint "tac.refine" 30 $ strErr "Created new meta: " ∷ termErr x ∷ []
  x ← reduce x
  debugPrint "tac.refine" 30 $ strErr "Reduced meta:     " ∷ termErr x ∷ []
  newgoal ← pass x
  debugPrint "tac.refine" 30 $ strErr "Created new subgoal." ∷ []
  just safe-x ← return $ maybeSafe x
    where nothing → do
            debugPrint "tac.refine" 10 $ strErr "Unsafe argument: " ∷ termErr x ∷ []
            typeError $ strErr "Cannot substitute unsafe argument: " ∷ termErr x ∷ []
  debugPrint "tac.refine" 30 $ strErr "Codomain (before substituting):" ∷ termErr (unAbs b) ∷ []
  let t' = substTerm (safe-x ∷ []) (unAbs b)
  debugPrint "tac.refine" 30 $ strErr "Codomain (after substituting):" ∷ termErr t' ∷ []
  refineAux' n t' (hd ∘ (arg ai x ∷_)) (newgoal ++ subgoals) goal

refineN' : Nat → Name → Tac
refineN' n f goal = do
  debugPrint "tac.refine" 10 $ strErr "Trying to refine goal with" ∷ termErr (def f []) ∷ strErr "applied to" ∷ strErr (show n) ∷ strErr "arguments" ∷ []
  t ← getType f
  debugPrint "tac.refine" 10 $ strErr "  type of head" ∷ termErr t ∷ []
  refineAux' n t (def f) [] goal

macro
  refineN : Nat → Name → Tactic
  refineN n f = runTac $ refineN' n f

refine' : Name → MultiTac
refine' f goal = do
  debugPrint "tac.refine" 10 $ strErr "Trying to refine goal with" ∷ termErr (def f []) ∷ []
  return (map (λ n → true , refineN' n f) (from 0 to 10))

macro
  refine : Name → Tactic
  refine f = runMultiTac $ refine' f

mini-auto' : Tac
mini-auto' = repeatMulti 10 ((toMulti true assumption') or-else-multi ((toMulti true intro') or-else-multi constr'))

macro
  mini-auto : Tactic
  mini-auto = runTac mini-auto'

test₁ : Nat → Bool → Nat
test₁ x y = x

test₂ : Nat → Bool → Bool
test₂ x y = y

test₄ : Nat → Bool → Nat
test₄ = λ n b → n

test₅ : Bool
test₅ = false

test₆ : Nat
test₆ = zero

test₇ : _≡_ {A = Bool} true true
test₇ = refl

test₈ : Vec Nat 0
test₈ = []

test₉ : Vec Bool 3
test₉ = false ∷ false ∷ false ∷ []

test₁₀ : {A : Set} → A → Vec A 5
test₁₀ = λ z → z ∷ z ∷ z ∷ z ∷ z ∷ []

data DecrVec (n : Nat) : Nat → Set where
  []  : DecrVec n zero
  cons : ∀ {k} → (m : Nat) → m < n → DecrVec m k → DecrVec n (suc k)

test₁₁ : DecrVec 4 3
test₁₁ = cons 2 (diff! 1) (cons 1 (diff! zero) (cons zero (diff! zero) []))

test₁₂ : 5 ∈ from 2 to 7
test₁₂ = suc (suc (suc zero!))

data Nat' : Set where
  suc : Nat' → Nat'
  zero : Nat'

testNat' : Nat'
testNat' = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ?)))))))))


{-
postulate
  emptyList : (A : Set) → List A
--emptyList A = []

postulate
  MyList : (A : Set) → Set
  my-map : (A : Set) → Char → MyList String → MyList A
--my-map A f xs = map f xs

test₁₃ : (Nat → Bool) → MyList Bool
test₁₃ f = {!refineN 3 my-map!}
-}
