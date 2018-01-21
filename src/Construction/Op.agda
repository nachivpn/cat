module Construction.Op where


open import Level
open import Category
open import Prelude.Function
open import Relation.Binary

op : ∀ {o a e} → (Category o a e) → Category o a e
op C = let module C = Category.Category C in
       record
         { Object = C.Object
         ; _⇒_ = flip C._⇒_
         ; _∙_ = flip C._∙_
         ; Id = C.Id
         ; _≈_ = C._≈_
         ; assoc = {!!}
         ; id-l = {!!}
         ; id-r = {!!}
         ; isEq = C.isEq
         ; congl = {!!}
         ; congr = {!!}
         }
