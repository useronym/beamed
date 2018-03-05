module Compile where -- we compile shit.
open import Syntax
open import Erlang.Syntax
open import Function using (_∘_; flip; _$_; const)
open import Data.Nat using (_+_)
open import Data.List using (List; _∷_; []; [_]; _++_; reverse)
open import Data.String using (String; toList; fromList)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; Σ)
open import Category.Monad.Identity
open import Category.Monad.State
open import Data.Char
open import Data.Maybe

-- Compilation state: list of identifiers assigned to bound variables.
St : Ctx → Set
St Γ = ∀ {x} → x ∈ Γ → String

open RawIMonadState (StateTIMonadState St IdentityMonad)

-- Compilation monad.
Compile : _
Compile = IStateT St Identity

-- Get the next sensible identifier.
nextChar : Char → Char × Bool
nextChar c = if c == 'z' then 'a' , true
                         else (fromNat $ 1 + (toNat c)) , false

nextId' : List Char → List Char
nextId' [] = [ 'a' ]
nextId' (c ∷ cs) with (nextChar c)
nextId' (c ∷ cs) | c' , false = c' ∷ cs
nextId' (c ∷ cs) | c' , true  = c' ∷ nextId' cs

nextId : String → String
nextId = fromList ∘ reverse ∘ nextId' ∘ reverse ∘ toList

-- Get the last bound variable. Is this usage of implicit arguments cheating?
getHead : ∀ {Γ} → Compile Γ Γ String
getHead {[]}    = return "a"
getHead {x ∷ Γ} = λ s → s here , s

-- Get the Nth bound variable.
getNth : {α : ★} {Γ : Ctx} → α ∈ Γ → Compile Γ Γ String
getNth n = get >>= λ s → return (s n)

-- Put in a new variable of type α.
putHead : ∀ {Γ} {α} → String → Compile Γ (α ∷ Γ) String
putHead x = λ s → x , λ { here → x; (there n) → s n }

-- Bind a new variable.
bindVar : ∀ {Γ} {α} → Compile Γ (α ∷ Γ) String
bindVar = getHead >>= λ x → putHead (nextId x)

-- Perform a stateful computation in isolation, not letting it modify the current state.
isolate : ∀ {A : Set} {Γ Δ} → Compile Γ Δ A → Compile Γ Γ A
isolate m = get >>= λ s → m >>= λ m' → put s >> _,_ m'

-- If we open up this term as much as we can, which types will get into the context?
binds : ∀ {Γ α} → Γ ⊢ α → List ★
binds unit                     = []
binds (var x)                  = []
binds {_} {α ⊳ β} (lam t)      = α ∷ (binds t)
binds (app {_} {α} {β} t₁ t₂)  = []
binds (let[_]in_ {_} {β} t' t) = β ∷ (binds t)

postulate
  dayum : ∀ {A : Set} {x a : A} {Γ Δ} → x ∈ (a ∷ Γ ++ Δ) → x ∈ (Γ ++ (a ∷ Δ))

-- Actually compile.
-- TODO: rewrite with do-notation.
cTerm : ∀ {Γ α} → (t : Γ ⊢ α) → Compile Γ ((binds t) ++ Γ) Expr
cTerm unit           = return (tuple [])
cTerm (var n)        = getNth n >>= return ∘ var
cTerm (lam t)        = bindVar >>= λ x → cTerm t >>= λ t' s → fun ([ x ] ⇒ [ t' ]) , λ x∈xs → s (dayum {Γ = binds t} x∈xs)
cTerm (app f x)      = isolate (cTerm f) >>= λ f' → isolate (cTerm x) >>= λ x' → return (apply f' [ x' ])
cTerm (let[ x ]in f) = isolate (cTerm x) >>= λ x' → bindVar >>= λ a' → cTerm f >>= λ f' s → lett (a' , x') f' , λ p → s (dayum {Γ = binds f} p)

-- Start the compilation with an empty list of bound variables.
compile : ∀ {α} → [] ⊢ α → Expr
compile t = proj₁ (cTerm t (λ {x} → λ ()))

-- Fun examples.
t t2 t3 : Expr
t = compile id⊤
t2 = compile C
t3 = compile test
