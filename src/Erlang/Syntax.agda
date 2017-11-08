-- Some outdated formalization of Core Erlang: https://www.it.uu.se/research/group/hipe/cerl/
-- Robert Virding's comments:
-- the definition of exprs is 'exprs ::= expr | < expr1,  . . . ,  exprn >' which is NOT a sequence of expressions. The second alternative is for returning multiple values (which core supports in a limited way)
-- vars has a similar definition 'vars ::= var | < var1,  . . . ,  varn >'.
-- Inside a let it means that the body can return multiple values which I can bind to multiple variables.
-- The number of return values and variables MUST be the same, it is up to the compiler to ensure that.
-- akr: that description is a little old and there doesn't really exist any good description of core as it is today. You can look in 'cerl' module to see the actual parts but there is no clear description of exactly how they should be used.
-- The safest way is to compiler erlang files with the 'to_core0' option and look at the resultant .core file.
-- The 'to_core0' or 'dcore' options outputs core before optimisation while 'to_core' and 'dcopt' outputs after optimisation. It is interesting to see the difference
-- There is no need to try and optimise yourself, leave it to core optimisation passes.
-- These options are undocumented.


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
