module Typecheck where
open import Syntax
import Parse as P
open import Relation.Nullary
open import Data.Maybe using (Maybe; just; nothing; monad)
open import Data.String using (String; _==_)
open import Data.Bool using (true; false; if_then_else_; _∧_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Category.Monad
open import Data.List using (List; _∷_; [_]; map) renaming ([] to ∅)


import Level
open RawMonad (monad {Level.zero})


Bindings : Set
Bindings = List (String × ★)

types : Bindings → List ★
types = map proj₂

-- Lookup a specific type under a name.
lookup : (Γ : Bindings) → (x : String) → (α : ★) → Maybe (α ∈ (types Γ))
lookup ∅ x α        = nothing
lookup ((x' , α') ∷ Γ) x α with x == x'
… | false = there <$> lookup Γ x α
… | true with α ≟ α'
… | no ¬p           = nothing
… | yes p rewrite p = just here

-- Lookup any type under a name.
lookup' : (Γ : Bindings) → (x : String) → Maybe (∃[ α ] (α ∈ (types Γ)))
lookup' ∅ x = nothing
lookup' ((x' , α) ∷ Γ) x = if x == x'
                            then just (α , here)
                            else lookup' Γ x >>= λ {(β , β∈Γ) → just (β , there β∈Γ)}


typecheck : (Γ : Bindings) → P.Term → (α : ★) → Maybe (types Γ ⊢ α)
typecheck Γ P.unit ⊤              = just unit
typecheck Γ P.unit (α ⊳ β)        = nothing
typecheck Γ (P.var x) α           = lookup Γ x α >>= λ α∈Γ → just (var α∈Γ)
typecheck Γ (P.lam x t) ⊤         = nothing
typecheck Γ (P.lam x t) (α ⊳ β)   =
  typecheck ((x , α) ∷ Γ) t β >>= λ t' → just (lam t')
typecheck Γ (P.app t₁ (t₂ , α)) β =
  typecheck Γ t₁ (α ⊳ β) >>= λ t₁' → typecheck Γ t₂ α >>= λ t₂' → just (app t₁' t₂')
typecheck Γ (P.let[ x ]=[ t₁ , α ]in t) β =
  typecheck Γ t₁ α >>= λ t₁' → typecheck ((x , α) ∷ Γ) t β >>= λ t' → just (let[ t₁' ]in t')

go : P.Term → (α : ★) → Maybe (∅ ⊢ α)
go = typecheck ∅
