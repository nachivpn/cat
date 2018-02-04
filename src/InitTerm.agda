module InitTerm where

open import Level
open import Category

module Core {o a e} (C : Category o a e) where

  open Category.Category C 

  data initial (O : Object) : Set (o ⊔ a ⊔ e)  where
      init : (∀ (C : Object) → ∃! O ⇒ C) → initial O

  data terminal (T : Object) : Set (o ⊔ a ⊔ e) where
      term : (∀ (C : Object) → ∃! C ⇒ T) → terminal T
