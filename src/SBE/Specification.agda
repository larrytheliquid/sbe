open import SBE.Prelude
open import SBE.Intrinsic
module SBE.Specification where

----------------------------------------------------------------------

embed : ∀{Γ A} → Val Γ A → Expr Γ A
embedᴺ : ∀{Γ A} → Neut Γ A → Expr Γ A

embed `zero = `zero
embed (`suc n) = `suc (embed n)
embed (`λ b) = `λ (embed b)
embed (`neut x) = embedᴺ x

embedᴺ (`var i) = `var i
embedᴺ (`rec cz cs n) = `rec (embed cz) (embed cs) (embedᴺ n)
embedᴺ (f `∙ a) = embedᴺ f `∙ embed a

----------------------------------------------------------------------

record Kit (T : Ctx → Type → Set) : Set where
  field
    var    : ∀{Γ A} → Var Γ A → T Γ A
    term   : ∀{Γ A} → T Γ A → Expr Γ A
    weaken : ∀{Γ A B} → T Γ B → T (Γ , A) B

lift : ∀{T Γ Δ A B} → Kit T
  → (Var Γ B → T Δ B)
  → Var (Γ , A) B → T (Δ , A) B
lift k σ here = Kit.var k here
lift k σ (there i) = Kit.weaken k (σ i)

trav : ∀{Γ Δ A T} → Kit T → (σ : ∀{B} → Var Γ B → T Δ B) → Expr Γ A → Expr Δ A
trav k σ `zero = `zero
trav k σ (`suc n) = `suc (trav k σ n)
trav k σ (`λ f) = `λ (trav k (lift k σ) f)
trav k σ (`var j) = Kit.term k (σ j)
trav k σ (`rec cz cs n) = `rec (trav k σ cz) (trav k σ cs) (trav k σ n)
trav k σ (n `∙ a) = trav k σ n `∙ trav k σ a

----------------------------------------------------------------------

Sub : (Γ Δ : Ctx) → Set
Sub Γ Δ = ∀{A} → Var Γ A → Expr Δ A

renKit : Kit Var
renKit = record { var = id ; term = `var ; weaken = there }

renᴱ : ∀{Γ Δ A} → Ren Γ Δ → Expr Γ A → Expr Δ A
renᴱ σ x = trav renKit σ x

subKit : Kit Expr
subKit = record { var = `var ; term = id ; weaken = renᴱ there }

subᴱ : ∀{Γ Δ A} → Sub Γ Δ → Expr Γ A → Expr Δ A
subᴱ σ x = trav subKit σ x

sub0ᴱ : ∀{Γ A} → Expr Γ A → Sub (Γ , A) Γ
sub0ᴱ x here = x
sub0ᴱ x (there i) = `var i

_/_ : ∀{Γ A B} → Expr (Γ , A) B → Expr Γ A → Expr Γ B
x / y = subᴱ (sub0ᴱ y) x

----------------------------------------------------------------------

infix 1 _≈_

data _≈_ {Γ} : ∀{A} → Expr Γ A → Expr Γ A → Set where
  `refl : ∀{A} {x : Expr Γ A}
    → x ≈ x
  `sym : ∀{A} {x y : Expr Γ A}
    → x ≈ y → y ≈ x
  `trans : ∀{A} {x y z : Expr Γ A}
    → x ≈ y → y ≈ z → x ≈ z

  `cong-var : ∀{A} {i : Var Γ A}
    → `var i ≈ `var i
  `cong-zero :
    `zero ≈ `zero
  `cong-suc : ∀{m n}
    → m ≈ n → `suc m ≈ `suc n
  `cong-lam : ∀{A B} {b b' : Expr (Γ , A) B}
    → b ≈ b' → `λ b ≈ `λ b'
  `cong-rec : ∀{C n n'} {cz cz' : Expr Γ C} {cs cs' : Expr Γ (C `→ C)}
    → cz ≈ cz' → cs ≈ cs' → n ≈ n'
    → `rec cz cs n ≈ `rec cz' cs' n'
  `cong-app : ∀{A B} {f f' : Expr Γ (A `→ B)} {a a' : Expr Γ A}
    → f ≈ f' → a ≈ a'
    → f `∙ a ≈ f' `∙ a'

  `comp-app : ∀{A B} {b : Expr (Γ , A) B} {a : Expr Γ A}
    → `λ b `∙ a ≈ b / a
  `comp-recz : ∀{C} {cz : Expr Γ C} {cs : Expr Γ (C `→ C)}
    → `rec cz cs `zero ≈ cz
  `comp-recs : ∀{C} {cz : Expr Γ C} {cs : Expr Γ (C `→ C)} {n : Expr Γ `ℕ}
    → `rec cz cs (`suc n) ≈ cs `∙ `rec cz cs n

----------------------------------------------------------------------
