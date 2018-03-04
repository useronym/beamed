module Syntax where
open import Relation.Nullary
open import Relation.Binary.Core
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; _∷_; [_]; _++_) renaming ([] to ∅)

private
  _,_ : ∀ {A : Set} → List A → A → List A
  xs , x = x ∷ xs
  infixl 8 _,_

data _∈_ {A : Set} : A → List A → Set where
  here  : ∀ {a xs} → a ∈ xs , a
  there : ∀ {a b xs} → a ∈ xs → a ∈ xs , b
infix 7 _∈_

data _⊆_ {A : Set} : List A → List A → Set where
  stop : ∀ {Γ} → Γ ⊆ Γ
  drop : ∀ {Γ Δ a} → Γ ⊆ Δ → Γ ⊆ (Δ , a)
  keep : ∀ {Γ Δ a} → Γ ⊆ Δ → (Γ , a) ⊆ (Δ , a)

mono∈ : ∀ {A} {Γ Γ' : List A} {x : A} → Γ ⊆ Γ' → x ∈ Γ → x ∈ Γ'
mono∈ stop i             = i
mono∈ (drop e) i         = there (mono∈ e i)
mono∈ (keep e) here      = here
mono∈ (keep e) (there i) = there (mono∈ e i)


data ★ : Set where
  ⊤   : ★
  _⊳_ : ★ → ★ → ★
infixr 10 _⊳_

⊳-injₗ : ∀ {a a' b b'} → a ⊳ a' ≡ b ⊳ b' → a ≡ b
⊳-injₗ refl = refl

⊳-injᵣ : ∀ {a a' b b'} → a ⊳ a' ≡ b ⊳ b' → a' ≡ b'
⊳-injᵣ refl = refl

_≟_ : Decidable {A = ★} _≡_
⊤ ≟ ⊤        = yes refl
(α ⊳ α') ≟ ⊤ = no (λ ())
⊤ ≟ (β ⊳ β₁) = no (λ ())
(α ⊳ α') ≟ (β ⊳ β') with α ≟ β | α' ≟ β'
… | yes p₁ | yes p₂  rewrite p₁ | p₂ = yes refl
… | yes p | no ¬p                    = no λ x → ¬p (⊳-injᵣ x)
… | no ¬p | yes p                    = no λ x → ¬p (⊳-injₗ x)
… | no ¬p | no ¬p₁                   = no λ x → ¬p (⊳-injₗ x)

Ctx : Set
Ctx = List ★

data _⊢_ : Ctx → ★ → Set where
  unit      : ∀ {Γ} → Γ ⊢ ⊤
  var       : ∀ {Γ a} → a ∈ Γ → Γ ⊢ a
  lam       : ∀ {Γ a b} → Γ , a ⊢ b → Γ ⊢ a ⊳ b
  app       : ∀ {Γ a b} → Γ ⊢ a ⊳ b → Γ ⊢ a → Γ ⊢ b
  let[_]in_ : ∀ {Γ a b} → Γ ⊢ a → Γ , a ⊢ b → Γ ⊢ b
infix 4 _⊢_

⊢_ : ★ → Set
⊢ α = ∅ ⊢ α

weaken : ∀ {Γ Δ a} → Γ ⊢ a → Γ ⊆ Δ → Δ ⊢ a
weaken unit Γ⊆Δ           = unit
weaken (var x) Γ⊆Δ        = var (mono∈ Γ⊆Δ x)
weaken (lam t) Γ⊆Δ        = lam (weaken t (keep Γ⊆Δ))
weaken (app t₁ t₂) Γ⊆Δ    = app (weaken t₁ Γ⊆Δ) (weaken t₂ Γ⊆Δ)
weaken (let[ x ]in t) Γ⊆Δ = let[ weaken x Γ⊆Δ ]in weaken t (keep Γ⊆Δ)


𝟎 : ∀ {A : Set} {a : A} {xs : List A} → a ∈ xs , a
𝟎 = here

𝟏 : ∀ {A : Set} {a b : A} {xs : List A} → a ∈ xs , a , b
𝟏 = there here

𝟐 : ∀ {A : Set} {a b c : A} {xs : List A} → a ∈ xs , a , b , c
𝟐 = there (there here)

id⊤ : ∅ ⊢ ⊤ ⊳ ⊤
id⊤ = lam (var 𝟎)

C : ∅ ⊢ (⊤ ⊳ ⊤) ⊳ (⊤ ⊳ ⊤) ⊳ ⊤ ⊳ ⊤
C = lam (lam (lam (app (var 𝟏) (app (var 𝟐) (var 𝟎)))))

test : ∅ ⊢ ⊤ ⊳ ⊤
test = let[ id⊤ ]in let[ weaken C (drop stop) ]in app ( app (var 𝟎) (var 𝟏)) (var 𝟏)
