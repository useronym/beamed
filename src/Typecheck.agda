module Typecheck where
open import Prelude
open import Syntax
import Parse as P
open import Data.Maybe using (Maybe; just; nothing; monad)
open import Data.String using (String; _==_)
open import Category.Monad


import Level
open RawMonad (monad {Level.zero})


Bindings : Set
Bindings = List (String × ★)

types : Bindings → List ★
types = map snd

-- Lookup a specific binding under a name.
lookup : (Γ : Bindings) → (x : String) → (α : ★) → Maybe (α ∈ (types Γ))
lookup ∅ x α        = nothing
lookup ((x' , α') ∷ Γ) x α with x == x'
… | false = there <$> lookup Γ x α
… | true with α ≟ α'
… | no ¬p           = nothing
… | yes p rewrite p = just here

-- Lookup any binding under a name.
lookup' : (Γ : Bindings) → (x : String) → Maybe (∃[ α ] (α ∈ (types Γ)))
lookup' ∅ x = nothing
lookup' ((x' , α) ∷ Γ) x with x == x'
… | true  = just (α , here)
… | false = lookup' Γ x >>= λ {(β , β∈Γ) → just (β , there β∈Γ)}


typecheck : (Γ : Bindings) → P.Term → (α : ★) → Maybe (types Γ ⊢ α)
typecheck Γ P.unit ⊤              = just unit
typecheck Γ P.unit (α ⊳ β)        = nothing
typecheck Γ (P.var x) α           = var <$> lookup Γ x α
typecheck Γ (P.lam x t) ⊤         = nothing
typecheck Γ (P.lam x t) (α ⊳ β)   = lam <$> typecheck ((x , α) ∷ Γ) t β
typecheck Γ (P.app t₁ (t₂ , α)) β =
  typecheck Γ t₁ (α ⊳ β) >>= λ t₁' → typecheck Γ t₂ α >>= λ t₂' → just (app t₁' t₂')
typecheck Γ (P.let[ x ]=[ t₁ , α ]in t) β =
  typecheck Γ t₁ α >>= λ t₁' → typecheck ((x , α) ∷ Γ) t β >>= λ t' → just (let[ t₁' ]in t')

go : P.Term → (α : ★) → Maybe (⊢ α)
go = typecheck ∅
