open import SBE.Prelude
open import SBE.Intrinsic
open import SBE.Specification
module SBE.Correct1 where

----------------------------------------------------------------------

comp : ∀{Γ Δ A} {x y : Expr Γ A}
  → x ≈ y → (σ : ⟦Env⟧ Γ Δ) → ⟦eval⟧ x σ ≡ ⟦eval⟧ y σ
comp `refl σ = refl
comp (`sym x) σ rewrite comp x σ = refl
comp (`trans x y) σ rewrite comp x σ | comp y σ = refl
comp `cong-var σ = refl
comp `cong-zero σ = refl
comp (`cong-suc n) σ rewrite comp n σ = refl
comp {Γ = Γ} (`cong-lam {A = A} {B = B} b) σ = ext2 (λ Δ a → comp b (⟦wknˢ⟧ Δ Γ σ , a))
comp (`cong-rec cz cs n) σ = cong₃ ⟦rec⟧ (comp cz σ) (comp cs σ) (comp n σ)
comp (`cong-app f a) σ = cong₂ _⟦∙⟧_ (comp f σ) (comp a σ)

comp `comp-app σ = {!!}

comp `comp-recz σ = refl
comp `comp-recs σ = refl

----------------------------------------------------------------------

completeness : ∀{Γ A} {x y : Expr Γ A}
  → x ≈ y → embed (nbe x) ≡ embed (nbe y)
completeness p rewrite comp p (⟦idEnv⟧ _) = refl

----------------------------------------------------------------------
