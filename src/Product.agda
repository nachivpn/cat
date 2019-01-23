module Product where

open import Level
open import Category
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.SetoidReasoning
open import Data.Product using (_×_)


record HasProducts {o a e} (C : Category o a e) : Set (o ⊔ a ⊔ e) where
  open Category.Category C
  field
    _x_       : (A B : Object) → Object
    π₁        : {A B : Object} → (A x B) ⇒ A
    π₂        : {A B : Object} → (A x B) ⇒ B
    uni       : ∀ {A B : Object} (Z : Object) (z₁ : Z ⇒ A) (z₂ : Z ⇒ B) →
      ∃! Z ⇒ (A x B) , λ u → π₁ ∙ u ≈ z₁ × π₂ ∙ u ≈ z₂

  <_,_> : ∀ {c a b} → c ⇒ a → c ⇒ b → c ⇒ (a x b)
  < p , q > = witness (uni _ p q)
  
  _⊗_ : ∀{a b c d} → a ⇒ b → c ⇒ d → (a x c) ⇒ (b x d)  -- \ o x
  f ⊗ g = < (f ∙ π₁) , (g ∙ π₂) >

record HasCoProducts {o a e} (C : Category o a e) : Set (o ⊔ a ⊔ e) where
  open Category.Category C
  field
    _+_       : (A B : Object) → Object
    i₁        : {A B : Object} → A ⇒ (A + B) 
    i₂        : {A B : Object} → B ⇒ (A + B)
    uni       : ∀ {A B : Object} (Z : Object) (z₁ : A ⇒ Z) (z₂ : B ⇒ Z) →
      ∃! (A + B) ⇒ Z , λ u → u ∙ i₁ ≈ z₁ × u ∙ i₂ ≈ z₂



  
