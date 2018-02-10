module Construction.Op where

open import Level
open import Category
open import Relation.Binary
open import Relation.Binary.SetoidReasoning

op : ∀ {o a e} → (Category o a e) → Category o a e
op C = let module C = Category.Category C in
       record
         { Object = C.Object
         ; _⇒_ = λ A B → B C.⇒ A
         ; _∙_ = λ g f → f C.∙ g
         ; Id = C.Id
         ; _≈_ = C._≈_
         ; assoc = sym C.isEq C.assoc
         ; id-l = sym C.isEq C.id-r
         ; id-r = sym C.isEq C.id-l
         ; isEq = C.isEq
         ; congl = λ _ _ p _ → sym C.isEq (C.congr _ _ (sym C.isEq p) _)
         ; congr = λ _ _ p _ → sym C.isEq (C.congl _ _ (sym C.isEq p) _)
         }
