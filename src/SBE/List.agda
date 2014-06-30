open import SBE.Prelude
module SBE.List where

----------------------------------------------------------------------

infixr 3 _`→_

data Type : Set where
  `ℕ : Type
  `List : Type → Type
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
    `[] : ∀{A} → Val Γ (`List A)
    _`∷_ : ∀{A} → Val Γ A → Val Γ (`List A) → Val Γ (`List A)
    `λ : ∀{A B} → Val (Γ , A) B → Val Γ (A `→ B)
    `neut : ∀{A} → Neut Γ A → Val Γ A

  data Neut (Γ : Ctx) : Type → Set where
    `var : ∀{A} → Var Γ A → Neut Γ A
    `rec : ∀{C} → Val Γ C → Val Γ (`ℕ `→ C `→ C) → Neut Γ `ℕ → Neut Γ C
    `fold : ∀{A C} → Val Γ C
      → Val Γ (A `→ `List A `→ C `→ C)
      → Neut Γ (`List A) → Neut Γ C
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
ren σ `[] = `[]
ren σ (`suc n) = `suc (ren σ n)
ren σ (x `∷ xs) = ren σ x `∷ ren σ xs
ren σ (`λ f) = `λ (ren (lift1Ren σ) f)
ren σ (`neut n) = `neut (renᴺ σ n)

renᴺ σ (`var j) = `var (σ j)
renᴺ σ (`rec cz cs n) = `rec (ren σ cz) (ren σ cs) (renᴺ σ n)
renᴺ σ (`fold cn cc xs) = `fold (ren σ cn) (ren σ cc) (renᴺ σ xs)
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

data ⟦List⟧ (A Z : Set) : Set where
  [] : ⟦List⟧ A Z
  _∷_ : (x : A) (xs : ⟦List⟧ A Z) → ⟦List⟧ A Z
  neut : Z → ⟦List⟧ A Z

⟦_⊢_⟧ : Ctx → Type → Set
⟦ Γ ⊢ A `→ B ⟧ = ∀ Δ → ⟦ Γ ++ Δ ⊢ A ⟧ → ⟦ Γ ++ Δ ⊢ B ⟧
⟦ Γ ⊢ `List A ⟧ = ⟦List⟧ ⟦ Γ ⊢ A ⟧ (Neut Γ (`List A))
⟦ Γ ⊢ `ℕ ⟧ = Val Γ `ℕ

----------------------------------------------------------------------

reflect : ∀{Γ} A → Neut Γ A → ⟦ Γ ⊢ A ⟧
reify : ∀{Γ} A → ⟦ Γ ⊢ A ⟧ → Val Γ A

reflect `ℕ n = `neut n
reflect (`List A) n = neut n
reflect (A `→ B) f = λ Δ a → reflect B (wknᴺ Δ f `∙ reify A a)

reify `ℕ n = n
reify (`List A) [] = `[]
reify (`List A) (x ∷ xs) = reify A x `∷ reify (`List A) xs
reify (`List A) (neut xs) = `neut xs
reify (A `→ B) f = `λ (reify B (f (ε , A) (reflect A (`var here))) )

----------------------------------------------------------------------

⟦Env⟧ : (Γ Δ : Ctx) → Set
⟦Env⟧ ε Δ = ⊤
⟦Env⟧ (Γ , A) Δ = ⟦Env⟧ Γ Δ × ⟦ Δ ⊢ A ⟧

lookup : ∀{Γ Δ A}
  → ⟦Env⟧ Γ Δ → Var Γ A → ⟦ Δ ⊢ A ⟧
lookup (xs , x) here = x
lookup (xs , x) (there i) = lookup xs i

⟦wkn⟧ : ∀{Γ} A Δ → ⟦ Γ ⊢ A ⟧ → ⟦ Γ ++ Δ ⊢ A ⟧
⟦wkn-List⟧ : ∀ {Γ A} Δ
  → ⟦List⟧ ⟦ Γ ⊢ A ⟧ (Neut Γ (`List A))
  → ⟦List⟧ ⟦ Γ ++ Δ ⊢ A ⟧ (Neut (Γ ++ Δ) (`List A))

⟦wkn⟧ `ℕ Δ n = wkn Δ n
⟦wkn⟧ (`List A) Δ xs = ⟦wkn-List⟧ Δ xs
⟦wkn⟧ {Γ = Γ} (A `→ B) Ξ f = lemma where
  lemma : (Δ : Ctx) → ⟦ (Γ ++ Ξ) ++ Δ ⊢ A ⟧ → ⟦ (Γ ++ Ξ) ++ Δ ⊢ B ⟧
  lemma Δ a rewrite assoc++ Γ Ξ Δ = f (Ξ ++ Δ) a

⟦wkn-List⟧ Δ [] = []
⟦wkn-List⟧ Δ (x ∷ xs) = ⟦wkn⟧ _ Δ x ∷ ⟦wkn-List⟧ Δ xs
⟦wkn-List⟧ Δ (neut x) = neut (wknᴺ Δ x)

⟦wknᴱ⟧ : ∀{Ξ} Δ Γ → ⟦Env⟧ Γ Ξ → ⟦Env⟧ Γ (Ξ ++ Δ)
⟦wknᴱ⟧ Δ ε tt = tt
⟦wknᴱ⟧ Δ (Γ , A) (xs , x) = ⟦wknᴱ⟧ Δ Γ xs , ⟦wkn⟧ A Δ x

⟦idEnv⟧ : ∀ Γ → ⟦Env⟧ Γ Γ
⟦idEnv⟧ ε = tt
⟦idEnv⟧ (Γ , A) = (⟦wknᴱ⟧ (ε , A) Γ (⟦idEnv⟧ Γ)) , reflect A (`var here)

----------------------------------------------------------------------

_⟦∙⟧_ : ∀{Γ A B} → ⟦ Γ ⊢ A `→ B ⟧ → ⟦ Γ ⊢ A ⟧ → ⟦ Γ ⊢ B ⟧
f ⟦∙⟧ a = f ε a

⟦rec⟧ : ∀{Γ C} → ⟦ Γ ⊢ C ⟧ → ⟦ Γ ⊢ (`ℕ `→ C `→ C) ⟧ → ⟦ Γ ⊢ `ℕ ⟧ → ⟦ Γ ⊢ C ⟧
⟦rec⟧ cz cs `zero = cz
⟦rec⟧ {C = C} cz cs (`suc n) = cs ε n ε (⟦rec⟧ {C = C} cz cs n)
⟦rec⟧ {C = C} cz cs (`neut n) = reflect C (`rec (reify _ cz) (reify _ cs) n)

⟦fold⟧ : ∀{Γ A C} → ⟦ Γ ⊢ C ⟧ → ⟦ Γ ⊢ (A `→ `List A `→ C `→ C) ⟧
  → ⟦ Γ ⊢ `List A ⟧ → ⟦ Γ ⊢ C ⟧
⟦fold⟧ cn cc [] = cn
⟦fold⟧ cn cc (x ∷ xs) = cc ε x ε xs ε (⟦fold⟧ cn cc xs)
⟦fold⟧ cn cc (neut xs) = reflect _ (`fold (reify _ cn) (reify _ cc) xs)

----------------------------------------------------------------------

⟦sub⟧ : ∀{Γ Δ A} → Val Γ A → ⟦Env⟧ Γ Δ → ⟦ Δ ⊢ A ⟧
⟦subᴺ⟧ : ∀{Γ Δ A} → Neut Γ A → ⟦Env⟧ Γ Δ → ⟦ Δ ⊢ A ⟧

⟦sub⟧ `zero σ = `zero
⟦sub⟧ `[] σ = []
⟦sub⟧ (`suc n) σ = `suc (⟦sub⟧ n σ)
⟦sub⟧ (x `∷ xs) σ = ⟦sub⟧ x σ ∷ ⟦sub⟧ xs σ
⟦sub⟧ {Γ = Γ} {Δ = Ξ} (`λ f) σ = λ Δ a → ⟦sub⟧ f (⟦wknᴱ⟧ Δ Γ σ , a)
⟦sub⟧ (`neut x) σ = ⟦subᴺ⟧ x σ

⟦subᴺ⟧ (`var i) σ = lookup σ i
⟦subᴺ⟧ (_`∙_ {A = A} {B = B} f a) σ = _⟦∙⟧_ {A = A} {B = B} (⟦subᴺ⟧ f σ) (⟦sub⟧ a σ)
⟦subᴺ⟧ (`rec {C = C} cz cs n) σ = ⟦rec⟧ {C = C} (⟦sub⟧ cz σ) (⟦sub⟧ cs σ) (⟦subᴺ⟧ n σ)
⟦subᴺ⟧ (`fold {C = C} cn cc xs) σ = ⟦fold⟧ {C = C} (⟦sub⟧ cn σ) (⟦sub⟧ cc σ) (⟦subᴺ⟧ xs σ)

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

-- _∙_ : ∀{Γ A B} → Val Γ (A `→ B) → Val Γ A → Val Γ B
-- `λ f ∙ a = sub1 f a
-- `neut f ∙ a = `neut (f `∙ a)

-- ----------------------------------------------------------------------

-- rec : ∀{Γ C} → Val Γ C → Val Γ (C `→ C) → Val Γ `ℕ → Val Γ C
-- rec cz cs `zero = cz
-- rec cz cs (`suc n) = cs ∙ rec cz cs n
-- rec cz cs (`neut n) = `neut (`rec cz cs n)

-- ----------------------------------------------------------------------

-- data Expr : Ctx → Type → Set where
--   `zero : ∀{Γ} → Expr Γ `ℕ
--   `suc : ∀{Γ} → Expr Γ `ℕ → Expr Γ `ℕ 
--   `λ : ∀{Γ A B} → Expr (Γ , A) B → Expr Γ (A `→ B)

--   `var : ∀{Γ A} → Var Γ A → Expr Γ A
--   `rec : ∀{Γ C} → Expr Γ C → Expr Γ (C `→ C) → Expr Γ `ℕ → Expr Γ C
--   _`∙_ : ∀{Γ A B} → Expr Γ (A `→ B) → Expr Γ A → Expr Γ B

-- ----------------------------------------------------------------------

-- norm : ∀{Γ A} → Expr Γ A → Val Γ A
-- norm `zero = `zero
-- norm (`suc n) = `suc (norm n)
-- norm (`λ f) = `λ (norm f)
-- norm (`var i) = `neut (`var i)
-- norm (`rec cz cs n) = rec (norm cz) (norm cs) (norm n)
-- norm (f `∙ a) = norm f ∙ norm a

-- ----------------------------------------------------------------------
