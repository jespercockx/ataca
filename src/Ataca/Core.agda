
open import Ataca.Utils

module Ataca.Core where

record TacCore : Setω where
  field
    Tac : (A : Set ℓ) → Set ℓ

    -- run tactic as Agda macro
    runTac : Tac ⊤ → Term → TC ⊤

    -- instances
    instance
      {{functorTac}}         : Functor (Tac {ℓ})
      {{functorLiftTac}}     : FunctorLift Tac ℓ A
      {{applicativeTac}}     : Applicative (Tac {ℓ})
      {{monadTac}}           : Monad (Tac {ℓ})
      {{applicativeZeroTac}} : ApplicativeZero (Tac {ℓ})
      {{alternativeTac}}     : Alternative (Tac {ℓ})

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
    run : Tac ⊤ → Term → TC ⊤
    run tac = runTac tac

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

  toMacro : Tac ⊤ → Term → TC ⊤
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
  addCtx b = goalTac λ goal → done _ , mkGoal (goal .theHole) (("x" , b) ∷ goal .goalCtx)

  fork : Tac Bool
  fork = forkTac (done false) (done true)

  liftTC' : TC (Tac A) → TC A → Tac A
  liftTC' err m = goalTac λ goal → (_, goal) $
    step $ TC.catchTC
      (done <$> foldl (flip (uncurry TC.extendContext)) m (goal .goalCtx))
      err

  -- Run TC action, backtracking on failure
  liftTC : TC A → Tac A
  liftTC = liftTC' $ return failTac

  -- Run TC action, raising IMPOSSIBLE on failure
  liftTC! : TC A → Tac A
  liftTC! {A = A} m = liftTC' fail m
    where
      fail : TC (Tac A)
      fail = TC.bindTC
        (TC.quoteTC m)
        (λ `m → TC.typeError $ strErr "Primitive TC action" ∷ termErr `m ∷ strErr "failed!" ∷ [])

  {-# TERMINATING #-}
  fmapTac : (A → B) → Tac {ℓ} A → Tac {ℓ′} B
  fmapTac g (done x  ) = done $ g x
  fmapTac {ℓ = ℓ} {ℓ′ = ℓ′} g (step mtac) = step $ lowerF {ℓ = ℓ} (mapLift′ (fmapTac g) <$> liftF {ℓ = ℓ′} mtac)
  fmapTac g (goalTac f) = goalTac λ goal → first (fmapTac g) $ f goal
  fmapTac g failTac = failTac
  fmapTac g (chooseTac tac₁ tac₂) = chooseTac (fmapTac g tac₁) (fmapTac g tac₂)
  fmapTac g skipTac = skipTac
  fmapTac g (forkTac tac₁ tac₂) = forkTac (fmapTac g tac₁) (fmapTac g tac₂)

  {-# TERMINATING #-}
  bindTac : Tac {ℓ} A → (A → Tac {ℓ} B) → Tac B
  bindTac (done x) g = g x
  bindTac (step mtac) g = step $ flip bindTac g <$> mtac
  bindTac (goalTac f) g = goalTac λ goal → first (flip bindTac g) $ f goal
  bindTac failTac g = failTac
  bindTac (chooseTac tac₁ tac₂) g = chooseTac (bindTac tac₁ g) (bindTac tac₂ g)
  bindTac skipTac g = skipTac
  bindTac (forkTac tac₁ tac₂) g = forkTac (bindTac tac₁ g) (bindTac tac₂ g)

  {-# TERMINATING #-}
  liftFTac : Tac A → Tac (Lift ℓ A)
  liftFTac = fmapTac lift

  lowerFTac : Tac (Lift ℓ A) → Tac A
  lowerFTac = fmapTac lower

  instance
    monadTac : Monad (Tac {ℓ})
    monadTac .return = done
    monadTac ._>>=_  = bindTac

    functorTac : Functor (Tac {ℓ})
    functorTac = Monad.rawFunctor it

    applicativeTac : Applicative (Tac {ℓ})
    applicativeTac = Monad.rawIApplicative it

    applicativeZeroTac : ApplicativeZero (Tac {ℓ})
    applicativeZeroTac .ApplicativeZero.applicative = it
    applicativeZeroTac .empty = failTac

    alternativeTac : Alternative (Tac {ℓ})
    alternativeTac .Alternative.applicativeZero = it
    alternativeTac ._<|>_ = chooseTac

    functorLiftTac : FunctorLift Tac ℓ A
    functorLiftTac .liftF  = liftFTac
    functorLiftTac .lowerF = lowerFTac

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
