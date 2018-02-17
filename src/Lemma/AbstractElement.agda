module Lemma.AbstractElement where

-- Lemmas about generalized elements

open import Level
open import Category


module Core {o a e} {C : Category o a e} where

  open Category.Category C
  
  squareCommutes : ∀ {A B C D : Object}
    {α : B ⇒ C} {β : D ⇒ C} {f : A ⇒ B} {g : A ⇒ D}
    → (∀ {X : Object} {x : X ⇒ A} → α ∙ f ∙ x ≈ β ∙ g ∙ x)
    → α ∙ f ≈ β ∙ g
  squareCommutes p = trans isEq (sym isEq id-l) (trans isEq p id-l)

    
