{-# OPTIONS --without-K --postfix-projections #-}

open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Utils
open import Container.List
open import Container.Traversable

import Tactic.Reflection
module TC = Tactic.Reflection
open TC using
  ( Name ; Term ; Type ; Arg ; ArgInfo ; unArg
  ; Abs ; unAbs
  ; Visibility ; getVisibility
  ; Relevance ; getRelevance
  ; Telescope
  ; Pattern ; Clause ; Definition
  ; TC ; ErrorPart
  ) public
open Term public
open Arg public
open ArgInfo public
open Visibility public
open Relevance public
open Pattern public
open Clause public
open Definition public
open ErrorPart public

private
  record Goal : Set where
    constructor mkGoal
    field
      theHole : Term
      goalCtx : Telescope
  open Goal

{-# NO_POSITIVITY_CHECK #-}
data Tac (A : Set ℓ) : Set ℓ where
  done      : A → Tac A
  step      : TC (Tac A) → Tac A
  goalTac   : (Goal → Tac A × Goal) → Tac A
  failTac   : Tac A
  chooseTac : Tac A → Tac A → Tac A
  skipTac   : Tac A
  forkTac   : Tac A → Tac A → Tac A

private
  {-# TERMINATING #-}
  runTac' : Tac A → Goal
          → TC (Maybe (List (A × Goal)))
          → TC (Maybe (List (A × Goal)))
  runTac' (done x) goal cont = fmap ((x , goal) ∷_) <$> cont
  runTac' (step mtac) goal cont = do
      tac ← mtac
      runTac' tac goal cont
  runTac' (goalTac f) goal cont =
      let tac' , goal' = f goal
      in  runTac' tac' goal' cont
  runTac' failTac goal cont = return nothing
  runTac' (chooseTac tac₁ tac₂) goal cont = do
      x ← TC.runSpeculative $ do
        just subgoals ← runTac' tac₁ goal cont
          where nothing → return $ nothing , false
        return $ just subgoals , true
      case x of λ where
        nothing         → runTac' tac₂ goal cont
        (just subgoals) → return $ just subgoals
  runTac' skipTac goal cont = cont
  runTac' (forkTac tac₁ tac₂) goal cont =
    runTac' tac₁ goal (runTac' tac₂ goal cont)

runTac : Tac A → Goal → TC (Maybe (List (A × Goal)))
runTac tac goal = runTac' tac goal (return $ just [])

toMacro : Tac ⊤ → TC.Tactic
toMacro tac hole = do
  `tac ← TC.quoteTC tac
  holeType ← TC.inferType hole
  TC.debugPrint "tac" 5 $
    strErr "Running tactic" ∷ termErr `tac     ∷
    strErr "on hole"        ∷ termErr hole     ∷
    strErr ":"              ∷ termErr holeType ∷ []
  just _ ← runTac tac $ mkGoal hole []
    where nothing → TC.typeError (strErr "Tactic" ∷ termErr `tac ∷ strErr "failed!" ∷ [])
  return _

macro
  run : Tac ⊤ → TC.Tactic
  run tac = toMacro tac

backtrack : Tac A
backtrack = failTac

getHole : Tac Term
getHole = goalTac λ goal → done (goal .theHole) , goal

setHole : Term → Tac ⊤
setHole hole = goalTac λ goal → done _ , mkGoal hole (goal .goalCtx)

getCtx : Tac Telescope
getCtx = goalTac λ goal → done (goal .goalCtx) , goal

addCtx : Arg Type → Tac ⊤
addCtx b = goalTac λ goal → done _ , mkGoal (goal .theHole) (b ∷ goal .goalCtx)

pass : A → Tac A
pass x = done x

skip : Tac A
skip = skipTac

duplicateGoal : Tac Bool
duplicateGoal = forkTac (done false) (done true)

private
  {-# TERMINATING #-}
  fmapTac : (A → B) → Tac A → Tac B
  fmapTac g (done x  ) = done $ g x
  fmapTac g (step mtac) = step $ fmapTac g <$>′ mtac
  fmapTac g (goalTac f) = goalTac λ goal → first (fmapTac g) $ f goal
  fmapTac g failTac = failTac
  fmapTac g (chooseTac tac₁ tac₂) = chooseTac (fmapTac g tac₁) (fmapTac g tac₂)
  fmapTac g skipTac = skipTac
  fmapTac g (forkTac tac₁ tac₂) = forkTac (fmapTac g tac₁) (fmapTac g tac₂)

  {-# TERMINATING #-}
  bindTac : Tac A → (A → Tac B) → Tac B
  bindTac (done x) g = g x
  bindTac (step mtac) g = step $ flip bindTac g <$>′ mtac
  bindTac (goalTac f) g = goalTac λ goal → first (flip bindTac g) $ f goal
  bindTac failTac g = failTac
  bindTac (chooseTac tac₁ tac₂) g = chooseTac (bindTac tac₁ g) (bindTac tac₂ g)
  bindTac skipTac g = skipTac
  bindTac (forkTac tac₁ tac₂) g = forkTac (bindTac tac₁ g) (bindTac tac₂ g)

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


liftTC' : TC (Tac A) → TC A → Tac A
liftTC' err m = do
  ctx ← getCtx
  step $ TC.catchTC
    (done <$> foldl (flip TC.extendContext) m ctx)
    err

-- Run TC action, backtracking on failure
liftTC : TC A → Tac A
liftTC = liftTC' $ return failTac

-- Run TC action, raising IMPOSSIBLE on failure
liftTC! : TC A → Tac A
liftTC! m = liftTC' fail m
  where
    fail : TC _
    fail = do
      `m ← TC.quoteTC m
      TC.typeError $ strErr "Primitive TC action" ∷ termErr `m ∷ strErr "failed!" ∷ []


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
  quoteTac x = liftTC! $ TC.quoteTC x

  unquoteTac : Term → Tac A
  unquoteTac u = liftTC! $ TC.unquoteTC u

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
