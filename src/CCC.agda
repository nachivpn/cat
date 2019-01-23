open import Level
open import Category

module CCC  where

  open import Product public
  open import InitTerm public
  
  record IsCCC {o a e} (C : Category o a e) : Set (o ⊔ a ⊔ e) where
  
    open Category.Category C
    
    field
      hasTerm  : HasTerminal C
      hasProd  : HasProducts C
      _^_      : ∀ (A B : Object) → Object

    open HasTerminal hasTerm public
    open HasProducts hasProd public
    
    field
    
      curry : ∀ {A B C : Object}  → (A x B) ⇒ C → A ⇒ (C ^ B)
      
      eval  : ∀ {A B   : Object}  → ((B ^ A ) x A) ⇒ B

      eval-curry : ∀ {A B C : Object}  → (f : (A x B) ⇒ C) → eval ∙ (curry f ⊗ Id B) ≈ f
