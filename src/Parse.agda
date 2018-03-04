module Parse where
open import Syntax
open import Data.String
open import Data.Sum
open import Data.Product


data Term : Set where
  unit          : Term
  var           : String → Term
  lam           : String → Term → Term
  app           : Term → Term × ★ → Term
  let[_]=[_]in_ : String → Term × ★ → Term → Term

Error : Set
Error = String

--parse : ∀ {α} → String → Error ⊎ (∅ ⊢ α)
--parse s = {!!}
