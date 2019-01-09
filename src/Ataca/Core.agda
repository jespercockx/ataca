open import Prelude hiding (_>>=_; _>>_; abs) renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)
open import Container.List
open import Container.Traversable
import Tactic.Reflection

open import Ataca.Utils

module Ataca.Core where

module TC = Tactic.Reflection
open TC using
  ( Name ; Term ; Type ; Arg ; ArgInfo ; unArg ; getArgInfo
  ; Abs ; unAbs
  ; Visibility ; getVisibility
  ; Relevance ; getRelevance
  ; Telescope
  ; Pattern ; Clause ; Definition
  ; TC ; ErrorPart
  ) public
open Term       public
open Arg        public
open Abs        public
open ArgInfo    public
open Visibility public
open Relevance  public
open Pattern    public
open Clause     public
open Definition public
open ErrorPart  public

record TacCore : Setω where
  field
    Tac : (A : Set ℓ) → Set ℓ

    -- run tactic as Agda macro
    runTac : Tac ⊤ → TC.Tactic

    -- instances
    instance
      {{FunctorTac}}      : Functor (Tac {ℓ})
      {{FunctorTac′}}     : Functor′ {ℓ} {ℓ′} Tac
      {{ApplicativeTac}}  : Applicative (Tac {ℓ})
      {{ApplicativeTac′}} : Applicative′ {ℓ} {ℓ′} Tac
      {{MonadTac}}        : Monad (Tac {ℓ})
      {{MonadTac′}}       : Monad′ {ℓ} {ℓ′} Tac
      {{FunctorZeroTac}}  : FunctorZero (Tac {ℓ})
      {{AlternativeTac}}  : Alternative (Tac {ℓ})

    -- goal manipulation
    getHole : Tac Term
    setHole : Term → Tac ⊤
    getCtx  : Tac Telescope
    addCtx  : Arg Type → Tac ⊤

    -- lifting TC actions
    liftTC  : TC A → Tac A -- backtrack on failure
    liftTC! : TC A → Tac A -- abort on failure

    -- creating and destroying subgoals
    fork    : Tac Bool
    skip    : Tac A

  macro
    run : Tac ⊤ → TC.Tactic
    run tac = runTac tac

private
  record Goal : Set where
    constructor mkGoal
    field
      theHole : Term
      goalCtx : Telescope
  open Goal public

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

  getHole : Tac Term
  getHole = goalTac λ goal → done (goal .theHole) , goal

  setHole : Term → Tac ⊤
  setHole hole = goalTac λ goal → done _ , mkGoal hole (goal .goalCtx)

  getCtx : Tac Telescope
  getCtx = goalTac λ goal → done (goal .goalCtx) , goal

  addCtx : Arg Type → Tac ⊤
  addCtx b = goalTac λ goal → done _ , mkGoal (goal .theHole) (b ∷ goal .goalCtx)

  fork : Tac Bool
  fork = forkTac (done false) (done true)

  liftTC' : TC (Tac A) → TC A → Tac A
  liftTC' err m = goalTac λ goal → (_, goal) $
    step $ TC.catchTC
      (done <$> foldl (flip TC.extendContext) m (goal .goalCtx))
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
    Functor′Tac' : Functor′ {ℓ} {ℓ′} Tac
    Functor′Tac' .fmap′ = fmapTac

    FunctorTac' : Functor {ℓ} Tac
    FunctorTac' .fmap = fmapTac

    Applicative′Tac' : Applicative′ {ℓ} {ℓ′} Tac
    Applicative′Tac' ._<*>′_ = monadAp′ bindTac

    ApplicativeTac' : Applicative (Tac {ℓ})
    ApplicativeTac' .pure  = done
    ApplicativeTac' ._<*>_ = monadAp bindTac

    Monad′Tac' : Monad′ {ℓ} {ℓ′} Tac
    Monad′Tac' ._>>=_ = bindTac

    MonadTac' : Monad (Tac {ℓ})
    MonadTac' .Monad._>>=_ = bindTac

    ZeroTac' : FunctorZero (Tac {ℓ})
    ZeroTac' .empty = failTac

    AlternativeTac' : Alternative (Tac {ℓ})
    AlternativeTac' ._<|>_ = chooseTac

tacCore : TacCore
tacCore = λ where
  .TacCore.Tac     → Tac
  .TacCore.runTac  → toMacro
  .TacCore.getHole → getHole
  .TacCore.setHole → setHole
  .TacCore.getCtx  → getCtx
  .TacCore.addCtx  → addCtx
  .TacCore.liftTC  → liftTC
  .TacCore.liftTC! → liftTC!
  .TacCore.fork    → fork
  .TacCore.skip    → skipTac

open TacCore tacCore public
