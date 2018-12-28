{-# OPTIONS --without-K --postfix-projections #-}

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Utils
open import Container.List
open import Container.Traversable
open import Tactic.Reflection as TC hiding
  ( unify; typeError; inferType; checkType
  ; normalise; reduce
  ; getContext; extendContext; inContext
  ; freshName; declareDef; declarePostulate; defineFun
  ; getType; getDefinition
  ; blockOnMeta; isMacro
  ; withNormalisation; debugPrint
  ; newMeta; newMeta! ) public

private
  record Goal : Set where
    constructor mkGoal
    field
      theHole : Term
      goalCtx : Telescope
  open Goal

{-# NO_POSITIVITY_CHECK #-}
data Tac {ℓ} (A : Set ℓ) : Set ℓ where
  done      : A → Tac A
  chooseTac : Tac A → Tac A → Tac A
  step      : (Goal → TC (Maybe (List (Tac A × Goal)))) → Tac A

private

  {-# TERMINATING #-}
  runTac' : Tac A → Goal
          → TC (Maybe (List (A × Goal)))
          → TC (Maybe (List (A × Goal)))
  runTac' (done x) goal cont = fmap ((x , goal) ∷_) <$> cont
  runTac' (chooseTac tac₁ tac₂) goal cont = do
      x ← runSpeculative $ do
        just subgoals ← runTac' tac₁ goal cont
          where nothing → return $ nothing , false
        return $ just subgoals , true
      case x of λ where
        nothing         → runTac' tac₂ goal cont
        (just subgoals) → return $ just subgoals
  runTac' (step f) goal cont = do
      --`f ← quoteTC f
      --`goalType ← TC.inferType $ goal .theHole
      --TC.debugPrint "tac" 30 $
      --  strErr "Running tactic step" ∷ termErr `f ∷
      --  strErr "on goal"             ∷ termErr (goal .theHole) ∷
      --  strErr ":"                   ∷ termErr `goalType ∷ []
      just subgoals ← f goal
        where nothing → return nothing
      solveSubgoals subgoals cont
    where
      solveSubgoals : List (Tac A × Goal)
                    → TC (Maybe (List (A × Goal)))
                    → TC (Maybe (List (A × Goal)))
      solveSubgoals [] cont = cont
      solveSubgoals ((tac₁ , goal₁) ∷ goals) cont = do
        runTac' tac₁ goal₁ (solveSubgoals goals cont)

runTac : Tac A → Goal → TC (Maybe (List (A × Goal)))
runTac tac goal = runTac' tac goal (return $ just [])

toMacro : Tac ⊤ → Tactic
toMacro tac hole = do
  `tac ← quoteTC tac
  holeType ← TC.inferType hole
  ctx ← TC.getContext
  TC.debugPrint "tac" 5 $
    strErr "Running tactic" ∷ termErr `tac     ∷
    strErr "on hole"        ∷ termErr hole     ∷
    strErr ":"              ∷ termErr holeType ∷ []
  just _ ← runTac tac $ mkGoal hole ctx
    where nothing → TC.typeError (strErr "Tactic" ∷ termErr `tac ∷ strErr "failed!" ∷ [])
  return _

macro
  run : Tac ⊤ → Tactic
  run tac = toMacro tac

backtrack : Tac A
backtrack = step λ _ → return $ nothing

getHole : Tac Term
getHole = step λ goal → return $ just $ [ done (goal .theHole) , goal ]

setHole : Term → Tac ⊤
setHole hole = step λ goal → return $ just $ [ done _ , mkGoal hole (goal .goalCtx) ]

addCtx : Arg Type → Tac ⊤
addCtx b = step λ goal → return $ just $ [ done _ , mkGoal (goal .theHole) (b ∷ goal .goalCtx) ]

pass : A → Tac A
pass x = step λ goal → return $ just $ [ done x , goal ]

skip : Tac A
skip = step λ goal → return $ just []

duplicateGoal : Tac Bool
duplicateGoal = step λ goal → return $ just $ (done false , goal) ∷ (done true , goal) ∷ []

liftTC' : TC (Maybe (List (Tac A × Goal))) → TC A → Tac A
liftTC' err m = step λ goal → catchTC
  (do
     x ← foldl (flip TC.extendContext) m (goal .goalCtx)
     return $ just $ [ done x , goal ])
  err

-- Run TC action, backtracking on failure
liftTC : TC A → Tac A
liftTC = liftTC' (return nothing)

-- Run TC action, raising IMPOSSIBLE on failure
liftTC! : TC A → Tac A
liftTC! m = liftTC' fail m
  where
    fail : TC _
    fail = do
      `m ← TC.quoteTC m
      TC.typeError $ strErr "Primitive TC action" ∷ termErr `m ∷ strErr "failed!" ∷ []

private
  {-# TERMINATING #-}
  fmapTac : (A → B) → Tac A → Tac B
  fmapTac f (done x  ) = done $ f x
  fmapTac f (chooseTac tac₁ tac₂) = chooseTac (fmapTac f tac₁) (fmapTac f tac₂)
  fmapTac f (step tac) = step λ goal →
    fmap′ (fmap′ $ first $ fmapTac f) <$>′ tac goal

  {-# TERMINATING #-}
  bindTac : Tac A → (A → Tac B) → Tac B
  bindTac (done x) f = f x
  bindTac (chooseTac tac₁ tac₂) f = chooseTac (bindTac tac₁ f) (bindTac tac₂ f)
  bindTac (step tac) f = step λ goal →
    fmap′ (fmap′ $ first $ flip bindTac f) <$>′ tac goal

instance
  Functor′Tac : Functor′ {ℓ} {ℓ′} Tac
  Functor′Tac .fmap′ = fmapTac

  FunctorTac : Functor {ℓ} Tac
  FunctorTac .fmap = fmapTac

  Applicative′Tac : Applicative′ {ℓ} {ℓ′} Tac
  Applicative′Tac ._<*>′_ = monadAp′ bindTac

  ApplicativeTac : Applicative (Tac {ℓ})
  ApplicativeTac .pure  = pass
  ApplicativeTac ._<*>_ = monadAp bindTac

  Monad′Tac : Monad′ {ℓ} {ℓ′} Tac
  Monad′Tac ._>>=_ = bindTac

  MonadTac : Monad (Tac {ℓ})
  MonadTac .Monad._>>=_ = bindTac

  ZeroTac : FunctorZero (Tac {ℓ})
  ZeroTac .empty = backtrack

  AlternativeTac : Alternative (Tac {ℓ})
  AlternativeTac ._<|>_ = chooseTac


module _ where
  unify : Term → Term → Tac ⊤
  unify u v = liftTC $ TC.unify u v

  inferType : Term → Tac Type
  inferType u = liftTC! $ TC.inferType u

  checkType : Term → Type → Tac Term
  checkType u a = liftTC! $ TC.checkType u a

  newMeta : Type → Tac Term
  newMeta a = liftTC! $ TC.newMeta a

  newMeta! : Tac Term
  newMeta! = liftTC! TC.newMeta!

  newMetaCtx : Telescope → Type → Tac Term
  newMetaCtx tel a = liftTC! $ extendCtxTel tel $ TC.newMeta a

  newMetaCtx! : Telescope → Tac Term
  newMetaCtx! tel = liftTC! $ extendCtxTel tel TC.newMeta!

  normalise : Term → Tac Term
  normalise u = liftTC! $ TC.normalise u

  reduce : Term → Tac Term
  reduce u = liftTC! $ TC.reduce u

  quoteTac : A → Tac Term
  quoteTac x = liftTC! $ quoteTC x

  unquoteTac : Term → Tac A
  unquoteTac u = liftTC! $ unquoteTC u

  getContext : Tac Telescope
  getContext = liftTC! TC.getContext

  freshName : String → Tac Name
  freshName n = liftTC! $ TC.freshName n

  declareDef : Arg Name → Type → Tac ⊤
  declareDef n a = liftTC! $ TC.declareDef n a

  declarePostulate : Arg Name → Type → Tac ⊤
  declarePostulate n a = liftTC! $ TC.declarePostulate n a

  defineFun : Name → List Clause → Tac ⊤
  defineFun n cs = liftTC! $ TC.defineFun n cs

  getType : Name → Tac Type
  getType n = liftTC! $ TC.getType n

  getDefinition : Name → Tac Definition
  getDefinition n = liftTC! $ TC.getDefinition n

  error : List ErrorPart → Tac A
  error msg = liftTC! $ do
    TC.debugPrint "tac" 1 msg
    TC.typeError []

  debug : String → Nat → List ErrorPart → Tac ⊤
  debug s n msg = liftTC! $ TC.debugPrint ("tac." <> s) n msg

getHoleWithType : Tac (Term × Type)
getHoleWithType = do
  hole ← getHole
  holeType ← inferType hole
  return (hole , holeType)

qed : Tac A
qed = do
  hole , holeType ← getHoleWithType
  error $ strErr "Unsolved subgoal: " ∷ termErr hole ∷ strErr ":" ∷ termErr holeType ∷ []

now : Tac A → Tac B
now tac = tac >> qed

try : Tac A → Tac (Maybe A)
try tac = (just <$> tac) <|> return nothing

repeat : Nat → Tac ⊤ → Tac ⊤
repeat zero    tac = return _
repeat (suc k) tac = tac >> repeat k tac

fork2 : Tac A → Tac B → Tac (Either A B)
fork2 tac₁ tac₂ =
  duplicateGoal >>= λ where
    false → left  <$>′ tac₁
    true  → right <$>′ tac₂

fork : {A : Fin n → Set ℓ}
     → ((i : Fin n) → Tac (A i)) → Tac (Σ (Fin n) A)
fork {n = zero } tac = skip
fork {n = suc n} tac = do
  fork2 (tac 0) (fork (tac ∘ suc)) >>= λ where
    (left x)        → return $ zero , x
    (right (i , y)) → return $ suc i , y

forEach : List A → (A → Tac B) → Tac B
forEach xs f = snd <$> (fork $ f ∘ indexVec (listToVec xs))

alreadySolved : Tac A
alreadySolved = do
  hole , holeType ← getHoleWithType
  reduce hole >>= λ where
    hole@(meta _ _) → do
      debug "alreadySolved" 25 $ strErr "Unsolved subgoal: " ∷ termErr hole ∷ strErr ":" ∷ termErr holeType ∷ []
      backtrack
    _               → skip

unlessSolved : Tac A → Tac A
unlessSolved tac = alreadySolved <|> tac
