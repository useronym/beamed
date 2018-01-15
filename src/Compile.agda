module Compile where -- we compile shit.
open import Syntax
open import Erlang.Syntax
open import Function using (_∘_; flip; _$_)
open import Data.Nat using (_+_)
open import Data.List using (List; _∷_; []; [_]; reverse)
open import Data.String using (String; toList; fromList)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁)
open import Category.Monad.State
open import Data.Char

-- Compilation state: list of bound variables.
St = List String

open RawMonadState (StateMonadState St)

-- Compilation monad.
Compile : _
Compile = State St

-- Get the next sensible identifier.
nextChar : Char → Char × Bool
nextChar c = if c == 'z' then 'a' , true
                         else (fromNat $ 1 + (toNat c)) , false

nextId' : List Char → List Char
nextId' [] = [ 'a' ]
nextId' (c ∷ cs) with (nextChar c)
nextId' (c ∷ cs) | c' , false = c' ∷ cs
nextId' (c ∷ cs) | c' , true = c' ∷ nextId' cs

nextId : String → String
nextId = fromList ∘ reverse ∘ nextId' ∘ reverse ∘ toList

-- List functions we wouldn't need if we only promised to compile closed terms…
-- But how would we recurse?
-- (also we would need to prove that we don't need these)
def : ∀ {A : Set} → List A → A → A
def [] d       = d
def (x ∷ xs) _ = x

nth : ∀ {A : Set} {a : ★} {xs : Ctx} → List A → a ∈ xs → A → A
nth [] n d               = d
nth (x ∷ xs) here d      = x
nth (x ∷ xs) (there n) d = nth xs n d

-- Get the last bound variable.
getHead : Compile String
getHead = get >>= return ∘ flip def ""

-- Get the Nth bound variable.
getNth : {a : ★} {xs : Ctx} → a ∈ xs → Compile String
getNth n = get >>= λ s → return (nth s n "error")

-- Bind a new variable.
putHead : String → Compile String
putHead a = get >>= λ xs → put (a ∷ xs) >> return a

-- Perform a stateful computation in isolation, not letting it modify the current state.
isolate : ∀ {A : Set} → Compile A → Compile A
isolate m = get >>= λ s → m >>= λ m' → put s >> return m'

-- Actually compile.
-- TODO: rewrite with do-notation.
cTerm : ∀ {Γ α} → Γ ⊢ α → Compile Expr
cTerm unit           = return (tuple [])
cTerm (var x)        = getNth x >>= return ∘ var
cTerm (lam t)        = getHead >>= λ x → putHead (nextId x) >>= λ x' → cTerm t >>= λ t' → return $ fun ([ x' ] ⇒ [ t' ])
cTerm (app f x)      = isolate (cTerm f) >>= λ f' → isolate (cTerm x) >>= λ x' → return $ apply f' [ x' ]
cTerm (let[ x ]in f) = isolate (cTerm x) >>= λ x' → getHead >>= λ a → putHead (nextId a) >>= λ a' → cTerm f >>= λ f' → return $ lett (a' , x') f'

-- Start the compilation with an empty list of bound variables.
compile : ∀ {α} → [] ⊢ α → Expr
compile t = proj₁ (cTerm t [])

-- Fun examples.
t t2 t3 : Expr
t = compile id⊤
t2 = compile C
t3 = compile test
