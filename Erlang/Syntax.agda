module Erlang.Syntax where
open import Data.Nat renaming (ℕ to Nat)
open import Data.Integer renaming (ℤ to Int)
open import Data.Float
open import Data.Char
open import Data.String
open import Data.List
open import Data.Product


Var Atom : Set
Var   = String
Atom  = String

data Lit : Set where
  int    : Int → Lit
  float  : Float → Lit
  atom   : Atom → Lit
  char   : Char → Lit
  string : String → Lit

data Const : Set where
  lit : Lit → Const
  list : List Const → Const
  tuple : List Const → Const

Fname : Set
Fname = String

mutual
  data Expr : Set where
    var    : Var → Expr
    fname  : Fname → Expr
    lit    : Lit → Expr
    fun    : Fun → Expr
    list   : List Expr → Expr
    tuple  : List Expr → Expr
    lett   : (Var × Expr) → Expr → Expr
    --case
    --letrec : List (Fname × Fun) → Exprs → Expr
    apply  : Expr → Exprs → Expr
    call   : Expr → Expr → Exprs → Expr
    --primop
    --receive
    --try
    --do
    --catch

  Exprs : Set
  Exprs = List Expr

  record Fun : Set where
    inductive
    constructor _⇒_
    field
      args  : List Var
      exprs : Exprs

record Module : Set where
  field
    name    : String
    exports : List (Atom × Nat)
    attrs   : List (Atom × Const)
    funs    : List (Fname × Fun)
