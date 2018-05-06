module Syntax where
open import Prelude


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
… | yes p₁ | yes p₂ rewrite p₁ | p₂ = yes refl
… | no ¬p  | _                      = no (¬p ∘ ⊳-injₗ)
… | _      | no ¬p                  = no λ x → ¬p (⊳-injᵣ x)

Ctx : Set
Ctx = List ★

data _⊢_ : Ctx → ★ → Set where
  unit      : ∀ {Γ} → Γ ⊢ ⊤
  var       : ∀ {Γ a} → a ∈ Γ → Γ ⊢ a
  lam       : ∀ {Γ a b} → Γ ⹁ a ⊢ b → Γ ⊢ a ⊳ b
  app       : ∀ {Γ a b} → Γ ⊢ a ⊳ b → Γ ⊢ a → Γ ⊢ b
  let[_]in_ : ∀ {Γ a b} → Γ ⊢ a → Γ ⹁ a ⊢ b → Γ ⊢ b
infix 4 _⊢_

⊢_ : ★ → Set
⊢ α = ∅ ⊢ α
infix 4 ⊢_

weaken : ∀ {Γ Δ a} → Γ ⊢ a → Γ ⊆ Δ → Δ ⊢ a
weaken unit Γ⊆Δ           = unit
weaken (var x) Γ⊆Δ        = var (mono∈ Γ⊆Δ x)
weaken (lam t) Γ⊆Δ        = lam (weaken t (keep Γ⊆Δ))
weaken (app t₁ t₂) Γ⊆Δ    = app (weaken t₁ Γ⊆Δ) (weaken t₂ Γ⊆Δ)
weaken (let[ x ]in t) Γ⊆Δ = let[ weaken x Γ⊆Δ ]in weaken t (keep Γ⊆Δ)


id⊤ : ⊢ ⊤ ⊳ ⊤
id⊤ = lam (var 𝟎)

C : ⊢ (⊤ ⊳ ⊤) ⊳ (⊤ ⊳ ⊤) ⊳ ⊤ ⊳ ⊤
C = lam (lam (lam (app (var 𝟏) (app (var 𝟐) (var 𝟎)))))

test : ⊢ ⊤ ⊳ ⊤
test = let[ id⊤ ]in let[ weaken C (drop stop) ]in app ( app (var 𝟎) (var 𝟏)) (var 𝟏)
