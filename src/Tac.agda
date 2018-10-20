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

Cont = Term → TC ⊤

record Tac {ℓ} (A : Set ℓ) : Set ℓ where
  field
    runTac : (A → Cont) → Cont
open Tac

toMacro : Tac ⊤ → Tactic
toMacro tac goal = do
  `tac ← quoteTC tac
  goalType ← TC.inferType goal
  TC.debugPrint "tac" 5 $
    strErr "Running tactic" ∷ termErr `tac     ∷
    strErr "on goal"        ∷ termErr goal     ∷
    strErr ":"              ∷ termErr goalType ∷ []
  tac .runTac (λ _ _ → return _) goal

macro
  run : Tac ⊤ → Tactic
  run tac = toMacro tac

getHole : Tac Term
getHole .runTac ret hole = ret hole hole

withHole : Term → Tac A → Tac A
withHole hole tac .runTac ret _ = tac .runTac ret hole

pass : A → Tac A
pass x .runTac ret = ret x

skip : Tac A
skip .runTac _ _ = return _

withTC : (TC ⊤ → TC ⊤) → Tac ⊤
withTC f .runTac ret hole = f $ ret _ hole

fork2 : Tac A → Tac B → Tac (Either A B)
fork2 tac₁ tac₂ .runTac ret hole = do
  tac₁ .runTac (ret ∘ left ) hole
  tac₂ .runTac (ret ∘ right) hole

liftTC : TC A → Tac A
liftTC m .runTac ret goal = do
  x ← m
  ret x goal

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

private
  fmapTac : (A → B) → Tac A → Tac B
  fmapTac f tac .runTac ret = tac .runTac $ ret ∘ f

  bindTac : Tac A → (A → Tac B) → Tac B
  bindTac tac f .runTac ret = tac .runTac $ λ x → f x .runTac ret

  chooseTac : Tac A → Tac A → Tac A
  chooseTac tac₁ tac₂ .runTac ret goal =
    tac₁ .runTac ret goal <|> tac₂ .runTac ret goal

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

getGoal : Tac (Term × Type)
getGoal = do
  hole ← getHole
  holeType ← inferType hole
  return (hole , holeType)

qed : Tac A
qed = do
  hole , holeType ← getGoal
  fail $ strErr "Unsolved subgoal: " ∷ termErr hole ∷ strErr ":" ∷ termErr holeType ∷ []

now : Tac A → Tac B
now tac = tac >> qed

try : Tac A → Tac (Maybe A)
try tac = (just <$> tac) <|> return nothing

defer : Term → Tac ⊤
defer hole = withHole hole $ pass _

commit : Tac A → Tac A
commit tac = tac <|> skip

cut : Tac ⊤
cut = commit $ pass _

addCtx : Arg Type → Tac ⊤
addCtx dom = withTC $ TC.extendContext dom

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
  hole , holeType ← getGoal
  reduce hole >>= λ where
    hole@(meta _ _) → fail $ strErr "Unsolved subgoal: " ∷ termErr hole ∷ strErr ":" ∷ termErr holeType ∷ []
    _               → skip

unlessSolved : Tac A → Tac A
unlessSolved tac = alreadySolved <|> tac
