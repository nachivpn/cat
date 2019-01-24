open import Category

module InitTerm where

record HasInitial {o a e} (C : Category o a e) : Set (o ⊔ a ⊔ e) where

  open Category.Category C
  
  field
    𝟘    : Object
    uni  : (∀ (C : Object) → ∃! 𝟘 ⇒ C)
    
  init : ∀ {a} → 𝟘 ⇒ a
  init = witness (uni _)
  
  uniq-init :  ∀ {a} {f : 𝟘 ⇒ a} → init ≈ f
  uniq-init {a} {f = f} = ump (uni a) {f} tt

record HasTerminal {o a e} (C : Category o a e) : Set (o ⊔ a ⊔ e) where

  open Category.Category C
  
  field
    𝟙    : Object
    uni  : (∀ (C : Object) → ∃! C ⇒ 𝟙)
    
  unit : ∀ {a} → a ⇒ 𝟙
  unit = witness (uni _)

  uniq-unit :  ∀ {a} {f : a ⇒ 𝟙} → unit ≈ f
  uniq-unit {a} {f = f} = ump (uni a) {f} tt
