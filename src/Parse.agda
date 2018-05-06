module Parse where
open import Prelude
open import Syntax
open import Data.String using (String)


data Term : Set where
  unit          : Term
  var           : String → Term
  lam           : String → Term → Term
  app           : Term → Term × ★ → Term
  let[_]=[_]in_ : String → Term × ★ → Term → Term
