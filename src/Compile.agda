module Compile where
open import Syntax
open import Erlang.Syntax
open import Data.List


cTerm : ∀ {Γ α} → Γ ⊢ α → Expr
cTerm truth     = tuple []
cTerm (int x)   = lit (int x)
cTerm (var x)   = var "x"
cTerm (lam t)   = fun ([ "x" ] ⇒ [ cTerm t ])
cTerm (app f x) = apply (cTerm f) [ cTerm x ]

t t2 : Expr
t = cTerm idZ
t2 = cTerm (C {Z} {Z} {Z})
