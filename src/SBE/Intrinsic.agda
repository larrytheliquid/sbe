open import SBE.Prelude
module SBE.Intrinsic where

----------------------------------------------------------------------

infixr 3 _`→_

data Type : Set where
  `ℕ : Type
  _`→_ : Type → Type → Type

----------------------------------------------------------------------

data Ctx : Set where
  ε : Ctx
  _,_ : Ctx → Type → Ctx

data Var : Ctx → Type → Set where
  here : ∀{Γ A} → Var (Γ , A) A
  there : ∀{Γ A B} → Var Γ A → Var (Γ , B) A

_++_ : (Γ Δ : Ctx) → Ctx
Γ ++ ε = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

assoc++ : (Γ Ξ Δ : Ctx) → (Γ ++ Ξ) ++ Δ ≡ Γ ++ (Ξ ++ Δ)
assoc++ Γ Ξ ε = refl
assoc++ Γ Ξ (Δ , A) = cong (λ Γ → Γ , A) (assoc++ Γ Ξ Δ)

----------------------------------------------------------------------

mutual
  data Val (Γ : Ctx) : Type → Set where
    `zero : Val Γ `ℕ
    `suc : Val Γ `ℕ → Val Γ `ℕ
    `λ : ∀{A B} → Val (Γ , A) B → Val Γ (A `→ B)
    `neut : ∀{A} → Neut Γ A → Val Γ A

  data Neut (Γ : Ctx) : Type → Set where
    `var : ∀{A} → Var Γ A → Neut Γ A
    `rec : ∀{C} → Val Γ C → Val Γ (C `→ C) → Neut Γ `ℕ → Neut Γ C
    _`∙_ : ∀{A B} → Neut Γ (A `→ B) → Val Γ A → Neut Γ B

----------------------------------------------------------------------

Ren : (Γ Δ : Ctx) → Set
Ren Γ Δ = ∀{A} → Var Γ A → Var Δ A

lift1Ren : ∀{Γ Δ A} → Ren Γ Δ → Ren (Γ , A) (Δ , A)
lift1Ren σ here = here
lift1Ren σ (there i) = there (σ i)

----------------------------------------------------------------------

ren : ∀{Γ Δ A} (σ : Ren Γ Δ) → Val Γ A → Val Δ A
renᴺ : ∀{Γ Δ A} (σ : Ren Γ Δ) → Neut Γ A → Neut Δ A

ren σ `zero = `zero
ren σ (`suc n) = `suc (ren σ n)
ren σ (`λ f) = `λ (ren (lift1Ren σ) f)
ren σ (`neut n) = `neut (renᴺ σ n)

renᴺ σ (`var j) = `var (σ j)
renᴺ σ (`rec cz cs n) = `rec (ren σ cz) (ren σ cs) (renᴺ σ n)
renᴺ σ (n `∙ a) = renᴺ σ n `∙ ren σ a

----------------------------------------------------------------------

wknRen : ∀{Γ} Δ → Ren Γ (Γ ++ Δ)
wknRen ε i = i
wknRen (Δ , A) i = there (wknRen Δ i)

wkn : ∀{Γ A} Δ → Val Γ A → Val (Γ ++ Δ) A
wkn Δ x = ren (wknRen Δ) x

wknᴺ : ∀{Γ A} Δ → Neut Γ A → Neut (Γ ++ Δ) A
wknᴺ Δ x = renᴺ (wknRen Δ) x

----------------------------------------------------------------------

⟦_⊢_⟧ : Ctx → Type → Set
⟦ Γ ⊢ A `→ B ⟧ = ∀ Δ → ⟦ Γ ++ Δ ⊢ A ⟧ → ⟦ Γ ++ Δ ⊢ B ⟧
⟦ Γ ⊢ `ℕ ⟧ = Val Γ `ℕ

----------------------------------------------------------------------

reflectᴺ : ∀{Γ} A → Neut Γ A → ⟦ Γ ⊢ A ⟧
reify : ∀{Γ} A → ⟦ Γ ⊢ A ⟧ → Val Γ A

reflectᴺ `ℕ n = `neut n
reflectᴺ (A `→ B) f = λ Δ a → reflectᴺ B (wknᴺ Δ f `∙ reify A a)

reify `ℕ n = n
reify (A `→ B) f = `λ (reify B (f (ε , A) (reflectᴺ A (`var here))) )

----------------------------------------------------------------------

⟦Env⟧ : (Γ Δ : Ctx) → Set
⟦Env⟧ ε Δ = ⊤
⟦Env⟧ (Γ , A) Δ = ⟦Env⟧ Γ Δ × ⟦ Δ ⊢ A ⟧

lookup : ∀{Γ Δ A}
  → ⟦Env⟧ Γ Δ → Var Γ A → ⟦ Δ ⊢ A ⟧
lookup (xs , x) here = x
lookup (xs , x) (there i) = lookup xs i

⟦wkn⟧ : ∀{Γ} A Δ → ⟦ Γ ⊢ A ⟧ → ⟦ Γ ++ Δ ⊢ A ⟧
⟦wkn⟧ `ℕ Δ n = wkn Δ n
⟦wkn⟧ {Γ = Γ} (A `→ B) Ξ f = lemma where
  lemma : (Δ : Ctx) → ⟦ (Γ ++ Ξ) ++ Δ ⊢ A ⟧ → ⟦ (Γ ++ Ξ) ++ Δ ⊢ B ⟧
  lemma Δ a rewrite assoc++ Γ Ξ Δ = f (Ξ ++ Δ) a

⟦wknᴱ⟧ : ∀{Ξ} Δ Γ → ⟦Env⟧ Γ Ξ → ⟦Env⟧ Γ (Ξ ++ Δ)
⟦wknᴱ⟧ Δ ε tt = tt
⟦wknᴱ⟧ Δ (Γ , A) (xs , x) = ⟦wknᴱ⟧ Δ Γ xs , ⟦wkn⟧ A Δ x

⟦idEnv⟧ : ∀ Γ → ⟦Env⟧ Γ Γ
⟦idEnv⟧ ε = tt
⟦idEnv⟧ (Γ , A) = (⟦wknᴱ⟧ (ε , A) Γ (⟦idEnv⟧ Γ)) , reflectᴺ A (`var here)

----------------------------------------------------------------------

_⟦∙⟧_ : ∀{Γ A B} → ⟦ Γ ⊢ A `→ B ⟧ → ⟦ Γ ⊢ A ⟧ → ⟦ Γ ⊢ B ⟧
f ⟦∙⟧ a = f ε a

⟦rec⟧ : ∀{Γ C} → ⟦ Γ ⊢ C ⟧ → ⟦ Γ ⊢ (C `→ C) ⟧ → ⟦ Γ ⊢ `ℕ ⟧ → ⟦ Γ ⊢ C ⟧
⟦rec⟧ cz cs `zero = cz
⟦rec⟧ cz cs (`suc n) = cs ε (⟦rec⟧ cz cs n)
⟦rec⟧ cz cs (`neut n) = reflectᴺ _ (`rec (reify _ cz) (`λ (`neut (`var here))) n)

----------------------------------------------------------------------

⟦sub⟧ : ∀{Γ Δ A} → Val Γ A → ⟦Env⟧ Γ Δ → ⟦ Δ ⊢ A ⟧
⟦subᴺ⟧ : ∀{Γ Δ A} → Neut Γ A → ⟦Env⟧ Γ Δ → ⟦ Δ ⊢ A ⟧

⟦sub⟧ `zero σ = `zero
⟦sub⟧ (`suc n) σ = `suc (⟦sub⟧ n σ)
⟦sub⟧ {Γ = Γ} {Δ = Ξ} (`λ f) σ = λ Δ a → ⟦sub⟧ f (⟦wknᴱ⟧ Δ Γ σ , a)
⟦sub⟧ (`neut x) σ = ⟦subᴺ⟧ x σ

⟦subᴺ⟧ (`var i) σ = lookup σ i
⟦subᴺ⟧ (f `∙ a) σ = ⟦subᴺ⟧ f σ ⟦∙⟧ ⟦sub⟧ a σ
⟦subᴺ⟧ (`rec cz cs n) σ = ⟦rec⟧ (⟦sub⟧ cz σ) (⟦sub⟧ cs σ) (⟦subᴺ⟧ n σ)

----------------------------------------------------------------------

Env : (Γ Δ : Ctx) → Set
Env ε Δ = ⊤
Env (Γ , A) Δ = Env Γ Δ × Val Δ A

wknᴱ : ∀{Ξ} Δ Γ → Env Γ Ξ → Env Γ (Ξ ++ Δ)
wknᴱ Δ ε tt = tt
wknᴱ Δ (Γ , A) (xs , x) = wknᴱ Δ Γ xs , wkn Δ x

idEnv : ∀ Γ → Env Γ Γ
idEnv ε = tt
idEnv (Γ , A) = (wknᴱ (ε , A) Γ (idEnv Γ)) , `neut (`var here)

reflectᴱ : ∀ Γ Δ → Env Γ Δ → ⟦Env⟧ Γ Δ
reflectᴱ ε Δ tt = tt
reflectᴱ (Γ , A) Δ (xs , x) = reflectᴱ Γ Δ xs , ⟦sub⟧ x (⟦idEnv⟧ Δ)

----------------------------------------------------------------------

sub : ∀{Γ Δ A} → Val Γ A → Env Γ Δ → Val Δ A
sub x σ = reify _ (⟦sub⟧ x (reflectᴱ _ _ σ))

subᴺ : ∀{Γ Δ A} → Neut Γ A → Env Γ Δ → Val Δ A
subᴺ x σ = reify _ (⟦subᴺ⟧ x (reflectᴱ _ _ σ))

sub1 : ∀{Γ A B} → Val (Γ , A) B → Val Γ A → Val Γ B
sub1 f a = sub f (idEnv _ , a)

----------------------------------------------------------------------

_∙_ : ∀{Γ A B} → Val Γ (A `→ B) → Val Γ A → Val Γ B
`λ f ∙ a = sub1 f a
`neut f ∙ a = `neut (f `∙ a)

----------------------------------------------------------------------

rec : ∀{Γ C} → Val Γ C → Val Γ (C `→ C) → Val Γ `ℕ → Val Γ C
rec cz cs `zero = cz
rec cz cs (`suc n) = cs ∙ rec cz cs n
rec cz cs (`neut n) = `neut (`rec cz cs n)

----------------------------------------------------------------------

data Expr : Ctx → Type → Set where
  `zero : ∀{Γ} → Expr Γ `ℕ
  `suc : ∀{Γ} → Expr Γ `ℕ → Expr Γ `ℕ 
  `λ : ∀{Γ A B} → Expr (Γ , A) B → Expr Γ (A `→ B)

  `var : ∀{Γ A} → Var Γ A → Expr Γ A
  `rec : ∀{Γ C} → Expr Γ C → Expr Γ (C `→ C) → Expr Γ `ℕ → Expr Γ C
  _`∙_ : ∀{Γ A B} → Expr Γ (A `→ B) → Expr Γ A → Expr Γ B

----------------------------------------------------------------------

norm : ∀{Γ A} → Expr Γ A → Val Γ A
norm `zero = `zero
norm (`suc n) = `suc (norm n)
norm (`λ f) = `λ (norm f)
norm (`var i) = `neut (`var i)
norm (`rec cz cs n) = rec (norm cz) (norm cs) (norm n)
norm (f `∙ a) = norm f ∙ norm a

----------------------------------------------------------------------

⟦eval⟧ : ∀{Γ Δ A} → Expr Γ A → ⟦Env⟧ Γ Δ → ⟦ Δ ⊢ A ⟧
⟦eval⟧ `zero σ = `zero
⟦eval⟧ (`suc n) σ = `suc (⟦eval⟧ n σ)
⟦eval⟧ {Γ = Γ} {Δ = Ξ} (`λ f) σ = λ Δ a → ⟦eval⟧ f (⟦wknᴱ⟧ Δ Γ σ , a)
⟦eval⟧ (`var i) σ = lookup σ i
⟦eval⟧ (`rec cz cs n) σ = ⟦rec⟧ (⟦eval⟧ cz σ) (⟦eval⟧ cs σ) (⟦eval⟧ n σ)
⟦eval⟧ (f `∙ a) σ = ⟦eval⟧ f σ ⟦∙⟧ ⟦eval⟧ a σ

eval : ∀{Γ Δ A} → Expr Γ A → Env Γ Δ → Val Δ A
eval x σ = reify _ (⟦eval⟧ x (reflectᴱ _ _ σ))

----------------------------------------------------------------------

