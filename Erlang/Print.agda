module Erlang.Print where
open import Erlang.Syntax
open import Function
open import Category.Monad
open import Data.Product
open import Data.Nat renaming (ℕ to Nat)
open import Data.Integer renaming (ℤ to Int)
open import Data.Float
open import Data.Char
open import Data.String
open import Data.List using (List; []; _∷_)


record Print (A : Set) : Set where
  field
    print : A → String
open Print {{…}} public


instance
  printChar : Print Char
  printChar = record { print = Data.Char.show }

  printInt : Print Int
  printInt = record { print = Data.Integer.show }

  printFloat : Print Float
  printFloat = record { print = Data.Float.show }

  printString : Print String
  printString = record { print = id }

  printVar : Print Var
  printVar = printString

  printAtom : Print Atom
  printAtom = printString

  printList : ∀ {A : Set} → {{_ : Print A}} → Print (List A)
  printList {A} = record { print = pList }
    where pList : List A → String
          pList [] = "[]"
          pList (x ∷ xs) = "[" ++ (print x) ++ "|" ++ (pList xs) ++ "]"

  printLit : Print Lit
  printLit = record { print = pLit }
    where pLit : Lit → String
          pLit (int x)    = print x
          pLit (float x)  = print x
          pLit (atom x)   = print x
          pLit (char x)   = print x
          pLit (string x) = print x

  {-# TERMINATING #-} -- TODO
  printConst : Print Const
  printConst = record { print = pConst }
    where pConst : Const → String
          pConst (lit x)   = print x
          pConst (list x)  = print x
          pConst (tuple x) = print x -- TODO

  printFname : Print Fname
  printFname = printString

mutual
  instance
    printFun : Print Fun
    printFun = record { print =
      λ { (args ⇒ exprs) → "fun (" ++ (print args) ++ ") -> \n" ++
                           (print exprs) } }

    {-# TERMINATING #-} -- TODO
    printExpr : Print Expr
    printExpr = record { print = pExpr }
      where pExpr : Expr → String
            pExpr (var x)          = print x
            pExpr (fname x)        = print x
            pExpr (lit x)          = print x
            pExpr (fun x)          = print x
            pExpr (list x)         = print x
            pExpr (tuple x)        = print x
            pExpr (lett (v , e) f) = "let <" ++ (print v) ++ "> =\n" ++
                                     (print e) ++
                                     "\nin\n" ++
                                     (print f)
            pExpr (apply f xs)     = "apply " ++ (print f) ++ (print xs)
            pExpr (call m f xs)    = "call " ++ (print m) ++ ":" ++ (print f) ++ (print xs)
