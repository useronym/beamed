open import Data.String
open import Data.List using (List; []; _∷_)


record Print (A : Set) : Set where
  field
    print : A → String
open Print {{…}} public

data StringyList : Set where
  wrap : List String → StringyList

instance
  printString : Print String
  printString = record { print = λ x → x }

  printList : ∀ {A : Set} → {{_ : Print A}} → Print (List A)
  printList {A} = record { print = pList }
    where pList : List A → String
          pList []       = "[]"
          pList (x ∷ xs) = "whatevs"

  printStringyList : Print StringyList
  printStringyList = record { print = λ {(wrap xs) → print xs }}
