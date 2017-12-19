module Sets where

open import Category
open import Prelude.Nat
open import Prelude.Function
open import Prelude.Equality
open import Prelude.Product

SetCat : Category (lsuc lzero) (lzero)
SetCat = record
                { Object = Set
                ; _⇒_ = λ A B → (A → B)
                ; _∙_ = λ f g → λ z → f (g z)
                ; Id = λ A → id
                ; assoc = λ A B C D f g h → refl
                ; ident = λ A B f → refl , refl
                }
