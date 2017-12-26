module Functor where

open import Level as L
open import Category
open import Prelude.Equality

Obj = Category.Object
Arr = Category._⇒_
Id = Category.Id

record _⇒_ {co ca do da} (C : Category co ca) (D : Category do da) :
  Set (lsuc (co ⊔ ca ⊔ do ⊔ da) ) where
  field
   F₀ : Obj C → Obj D
   F₁ : ∀ {C₁ C₂} → Arr C C₁ C₂ → Arr D (F₀ C₁) (F₀ C₂)
   F-id : ∀ {A : Obj C} → F₁ (Id C A) ≡ Id D (F₀ A)
   -- F-∙  : ∀ {g f} → F₁ ? ≡ F₁ g ∙ F₁ f  
