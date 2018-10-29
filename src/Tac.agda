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

record Tac {ℓ} (A : Set ℓ) : Set ℓ where
  field
    runTac : Goal → TC (List (A × Goal))
open Tac

toMacro : Tac ⊤ → Tactic
toMacro tac hole = do
  `tac ← quoteTC tac
  holeType ← TC.inferType hole
  ctx ← TC.getContext
  TC.debugPrint "tac" 5 $
    strErr "Running tactic" ∷ termErr `tac     ∷
    strErr "on hole"        ∷ termErr hole     ∷
    strErr ":"              ∷ termErr holeType ∷ []
  void $ tac .runTac λ where
    .theHole → hole
    .goalCtx → ctx

macro
  run : Tac ⊤ → Tactic
  run tac = toMacro tac


getHole : Tac Term
getHole .runTac goal = return [ (goal .theHole) , goal ]

setHole : Term → Tac ⊤
setHole hole .runTac goal = return [ _ , mkGoal hole (goal .goalCtx) ]

addCtx : Arg Type → Tac ⊤
addCtx b .runTac goal = return [ _ , mkGoal (goal .theHole) (b ∷ goal .goalCtx) ]

pass : A → Tac A
pass x .runTac goal = return [ x , goal ]

skip : Tac A
skip .runTac _ = return []

fork2 : Tac A → Tac B → Tac (Either A B)
fork2 tac₁ tac₂ .runTac goal = do
  xs ← map (first left)  <$>′ tac₁ .runTac goal
  ys ← map (first right) <$>′ tac₂ .runTac goal
  return $ xs ++ ys

liftTC : TC A → Tac A
liftTC m .runTac goal = do
  x ← foldl (flip TC.extendContext) m (goal .goalCtx)
  return [ x , goal ]

private
  fmapTac : (A → B) → Tac A → Tac B
  fmapTac f tac .runTac goal = fmap′ (fmap′ (first f)) $ tac .runTac goal

  bindTac : Tac A → (A → Tac B) → Tac B
  bindTac tac f .runTac goal = do
    xs ← tac .runTac goal
    concat <$> traverse′ (λ { (x , subgoal) → f x .runTac subgoal }) xs

  chooseTac : Tac A → Tac A → Tac A
  chooseTac tac₁ tac₂ .runTac goal =
    tac₁ .runTac goal <|> tac₂ .runTac goal

instance
  Functor′Tac : Functor′ {ℓ} {ℓ′} Tac
  Functor′Tac {{.fmap′}} = fmapTac

  FunctorTac : Functor {ℓ} Tac
  FunctorTac {{.fmap}} = fmapTac

  Applicative′Tac : Applicative′ {ℓ} {ℓ′} Tac
  Applicative′Tac {{._<*>′_}} = monadAp′ bindTac

  ApplicativeTac : Applicative (Tac {ℓ})
  ApplicativeTac {{.pure }} = pass
  ApplicativeTac {{._<*>_}} = monadAp bindTac

  Monad′Tac : Monad′ {ℓ} {ℓ′} Tac
  Monad′Tac {{._>>=_}} = bindTac

  MonadTac : Monad (Tac {ℓ})
  MonadTac .Monad._>>=_ = bindTac

  ZeroTac : FunctorZero (Tac {ℓ})
  ZeroTac {{.empty}} = liftTC empty

  AlternativeTac : Alternative (Tac {ℓ})
  AlternativeTac {{._<|>_}} = chooseTac


module _ where
  unify : Term → Term → Tac ⊤
  unify u v = liftTC $ TC.unify u v

  inferType : Term → Tac Type
  inferType u = liftTC $ TC.inferType u

  checkType : Term → Type → Tac Term
  checkType u a = liftTC $ TC.checkType u a

  newMeta : Type → Tac Term
  newMeta a = liftTC $ TC.newMeta a

  newMeta! : Tac Term
  newMeta! = liftTC TC.newMeta!

  newMetaCtx : Telescope → Type → Tac Term
  newMetaCtx tel a = liftTC $ extendCtxTel tel $ TC.newMeta a

  newMetaCtx! : Telescope → Tac Term
  newMetaCtx! tel = liftTC $ extendCtxTel tel TC.newMeta!

  normalise : Term → Tac Term
  normalise u = liftTC $ TC.normalise u

  reduce : Term → Tac Term
  reduce u = liftTC $ TC.reduce u

  quoteTac : A → Tac Term
  quoteTac x = liftTC $ quoteTC x

  unquoteTac : Term → Tac A
  unquoteTac u = liftTC $ unquoteTC u

  getContext : Tac Telescope
  getContext = liftTC TC.getContext

  freshName : String → Tac Name
  freshName n = liftTC $ TC.freshName n

  declareDef : Arg Name → Type → Tac ⊤
  declareDef n a = liftTC $ TC.declareDef n a

  declarePostulate : Arg Name → Type → Tac ⊤
  declarePostulate n a = liftTC $ TC.declarePostulate n a

  defineFun : Name → List Clause → Tac ⊤
  defineFun n cs = liftTC $ TC.defineFun n cs

  getType : Name → Tac Type
  getType n = liftTC $ TC.getType n

  getDefinition : Name → Tac Definition
  getDefinition n = liftTC $ TC.getDefinition n

  fail : List ErrorPart → Tac A
  fail = liftTC ∘ TC.typeError

  debug : String → Nat → List ErrorPart → Tac ⊤
  debug s n msg = liftTC $ TC.debugPrint ("tac." <> s) n msg

getHoleWithType : Tac (Term × Type)
getHoleWithType = do
  hole ← getHole
  holeType ← inferType hole
  return (hole , holeType)

qed : Tac A
qed = do
  hole , holeType ← getHoleWithType
  fail $ strErr "Unsolved subgoal: " ∷ termErr hole ∷ strErr ":" ∷ termErr holeType ∷ []

now : Tac A → Tac B
now tac = tac >> qed

try : Tac A → Tac (Maybe A)
try tac = (just <$> tac) <|> return nothing

repeat : Nat → Tac ⊤ → Tac ⊤
repeat zero    tac = return _
repeat (suc k) tac = tac >> repeat k tac

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
    hole@(meta _ _) → fail $ strErr "Unsolved subgoal: " ∷ termErr hole ∷ strErr ":" ∷ termErr holeType ∷ []
    _               → skip

unlessSolved : Tac A → Tac A
unlessSolved tac = alreadySolved <|> tac
