open import Data.List using (List; _∷_; []; [_]; reverse)
open import Data.String using (String; toList; fromList)
open import Category.Monad.State


data _∈_ {A : Set} : A → List A → Set where
  here  : ∀ {a xs} → a ∈ (a ∷ xs)
  there : ∀ {a b xs} → a ∈ xs → a ∈ (b ∷ xs)
infix 7 _∈_

Ctx : Set
Ctx = List {!!} -- whatever

-- Compilation state: list of identifiers assigned to bound variables.
St : Ctx → Set
St Γ = ∀ {x} → x ∈ Γ → String

open RawMonadState (StateMonadState (St {!!})) -- What do I put here?

-- Compilation monad.
Compile : Ctx → _
Compile Γ = State (St Γ)
