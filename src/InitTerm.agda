open import Level
open import Category

module InitTerm where

record HasInitial {o a e} (C : Category o a e) : Set (o ⊔ a ⊔ e) where
  open Category.Category C
  field
    𝟘    : Object
    uni  : (∀ (C : Object) → ∃! 𝟘 ⇒ C)

open HasInitial


record HasTerminal {o a e} (C : Category o a e) : Set (o ⊔ a ⊔ e) where
  open Category.Category C
  field
    𝟙    : Object
    uni  : (∀ (C : Object) → ∃! C ⇒ 𝟙)

