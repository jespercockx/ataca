module Ataca.Tactics.BasicTactics where

open import Ataca.Utils
open import Ataca.Core

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
  getContext = map ("x" ,_) <$> liftTC! TC.getContext

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
  error msg = liftTC! $ TC.bindTC
    (TC.debugPrint "tac" 1 msg)
    (λ _ → TC.typeError [])

  debug : String → ℕ → List ErrorPart → Tac ⊤
  debug s n msg = liftTC! $ TC.debugPrint ("tac." String.++ s) n msg

backtrack : Tac A
backtrack = empty

pass : A → Tac A
pass x = return x

getHoleWithType : Tac (Term × Type)
getHoleWithType = do
  hole ← getHole
  holeType ← inferType hole
  return (hole , holeType)

noMoreGoals : Tac A
noMoreGoals = do
  lift (hole , holeType) ← liftF getHoleWithType
  error $ strErr "Unsolved subgoal: " ∷ termErr hole ∷ strErr ":" ∷ termErr holeType ∷ []

now : Tac A → Tac B
now {a} {A} {b} {B} tac = lowerF {ℓ = a} (liftF {ℓ = b} tac >> noMoreGoals)

try : Tac A → Tac (Maybe A)
try tac = (just <$> tac) <|> return nothing

repeat : ℕ → Tac ⊤ → Tac ⊤
repeat zero    tac = return _
repeat (suc k) tac = tac >> repeat k tac

fork2 : Tac A → Tac B → Tac (A ⊎ B)
fork2 {a} {A} {b} {B} tac₁ tac₂ = lowerF {ℓ = a ⊔ b} $
  liftF {ℓ = a ⊔ b} fork >>= λ where
    (lift false) → mapLift left <$> liftF tac₁
    (lift true)  → mapLift right <$> liftF tac₂

forkN : {A : Fin n → Set ℓ}
     → ((i : Fin n) → Tac (A i)) → Tac (Σ (Fin n) A)
forkN {n = zero } tac = skip
forkN {n = suc n} tac = do
  fork2 (tac zero) (forkN (tac ∘ suc)) >>= λ where
    (left x)        → return $ zero , x
    (right (i , y)) → return $ suc i , y

forEach : List A → (A → Tac B) → Tac B
forEach xs f = snd <$> (forkN $ f ∘ Vec.lookup (Vec.fromList xs))

qed : Tac A
qed = do
  lift (hole , holeType) ← liftF getHoleWithType
  liftF (reduce hole) >>= λ where
    (lift hole@(meta _ _)) → do
      --debug "qed" 25 $ strErr "Unsolved subgoal: " ∷ termErr hole ∷ strErr ":" ∷ termErr holeType ∷ []
      backtrack
    _               → skip

unlessSolved : Tac A → Tac A
unlessSolved tac = qed <|> tac
