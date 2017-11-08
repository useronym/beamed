module Syntax where
open import Data.List using (List; _∷_; [_]) renaming ([] to ∅)
open import Data.Integer using (ℤ)


_,_ : ∀ {A : Set} → List A → A → List A
xs , x = x ∷ xs
infixl 8 _,_

data _∈_ {A : Set} : A → List A → Set where
  here : ∀ {a xs} → a ∈ xs , a
  there : ∀ {a b xs} → a ∈ xs → a ∈ xs , b
infix 7 _∈_

data ★ : Set where
  T Z : ★
  _⊳_ : ★ → ★ → ★
infixr 10 _⊳_

Ctx : Set
Ctx = List ★

data _⊢_ : Ctx → ★ → Set where
  truth : ∀ {Γ} → Γ ⊢ T
  int : ∀ {Γ} → ℤ → Γ ⊢ Z
  var : ∀ {Γ a} → a ∈ Γ → Γ ⊢ a
  lam : ∀ {Γ a b} → Γ , a ⊢ b → Γ ⊢ a ⊳ b
  app : ∀ {Γ a b} → Γ ⊢ a ⊳ b → Γ ⊢ a → Γ ⊢ b
infix 4 _⊢_


𝟎 : ∀ {A : Set} {a : A} {xs : List A} → a ∈ xs , a
𝟎 = here

𝟏 : ∀ {A : Set} {a b : A} {xs : List A} → a ∈ xs , a , b
𝟏 = there here

𝟐 : ∀ {A : Set} {a b c : A} {xs : List A} → a ∈ xs , a , b , c
𝟐 = there (there here)

idZ : ∅ ⊢ Z ⊳ Z
idZ = lam (var here)

C : ∀ {a b c} → ∅ ⊢ (a ⊳ b) ⊳ (b ⊳ c) ⊳ a ⊳ c
C = lam (lam (lam (app (var 𝟏) (app (var 𝟐) (var 𝟎)))))
