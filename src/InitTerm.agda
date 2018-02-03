module InitTerm where

open import Level
open import Category

module Core {o a e} (C : Category o a e) where

  open Category.Category C 

  record initial (O : Object) : Set (o ⊔ a ⊔ e)  where
    field
      init : ∀ {C : Object} → ∃! O ⇒ C

  record terminal (T : Object) : Set (o ⊔ a ⊔ e) where
    field
      term : ∀ {C : Object} → ∃! C ⇒ T
