module SBE.Prelude where

----------------------------------------------------------------------

record ⊤ : Set where
  constructor tt

infixr 4 _,_
infixr 2 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_ public

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} (i : Fin n) → Fin (suc n)

----------------------------------------------------------------------

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
       (f : A → B → C) {x x' y y'} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
       (f : A → B → C → D) {x x' y y' z z'} → x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

----------------------------------------------------------------------

id : {A : Set} → A → A
id x = x

----------------------------------------------------------------------
