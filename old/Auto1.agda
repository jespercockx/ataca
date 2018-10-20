open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Container.List
open import Container.Traversable
open import Tactic.Reflection
open import Tactic.Deriving.Eq

Cont = Term → TC ⊤

done : Cont
done _ = return _

Tac = Cont → Cont

try : Tac
try cont goal = cont goal <|> done goal

_and-then_ : Tac → Tac → Tac
(tac₁ and-then tac₂) ret goal = tac₁ (tac₂ ret) goal <|> tac₂ ret goal

repeat : Nat → Tac → Tac
repeat zero    tac ret      = ret
repeat (suc k) tac ret goal = tac (repeat k tac ret) goal <|> ret goal

assumption' : Tac
assumption' ret goal = do
    k ← length <$> getContext
    choice $ map tryVar (from 0 to k)
    where
      tryVar : Nat → TC ⊤
      tryVar i = unify (var i []) goal

macro
  assumption : Term → TC ⊤
  assumption = assumption' done

test₁ : Nat → Bool → Nat
test₁ x y = assumption

test₂ : Nat → Bool → Bool
test₂ x y = assumption

intro' : Cont → Term → TC ⊤
intro' ret goal@(meta _ _) = do
  t ← inferType goal
  pi a b ← reduce t
    where t → typeError $ strErr "Not a function type: " ∷ termErr t ∷ []
  body ← extendContext a $ newMeta (unAbs b)
  let v = getVisibility a
  unify (lam v (body <$ b)) goal
  extendContext a $ ret body
intro' ret goal = typeError $ strErr "Goal already solved: " ∷ termErr goal ∷ []

macro
  intro : Term → TC ⊤
  intro = intro' done

intros' : Nat → Tac
intros' k = repeat k intro'

macro
  intros : Term → TC ⊤
  intros = intros' 100 done

test₃ : Nat → Bool → ⊤
test₃ = intros

mini-auto' : Tac
mini-auto' = repeat 100 (assumption' and-then intro')

macro
  mini-auto : Tactic
  mini-auto = mini-auto' done

test₄ : Nat → Bool → Nat
test₄ = mini-auto
