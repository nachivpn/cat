module Construction.Arrow where


open import Level
open import Category
open import Relation.Binary hiding (_⇒_)
open import Data.Product

module Core {o a e} (C : Category o a e) where

  module C = Category.Category C
  open Category.Category C


  _⇒ₐ_ : ∃₂ (λ A B → A C.⇒ B) → ∃₂ (λ X Y → X C.⇒ Y) → Set (a)
  (A , B , _) ⇒ₐ (X , Y , _) =  A ⇒ X × B ⇒ Y

  _∙ₐ_ : {A : ∃₂ (λ A₁ A₂ → A₁ ⇒ A₂)}
         {B : ∃₂ (λ B₁ B₂ → B₁ ⇒ B₂)}
         {C : ∃₂ (λ C₁ C₂ → C₁ ⇒ C₂)}
         → B ⇒ₐ C → A ⇒ₐ B → A ⇒ₐ C
  (g₁ , g₂) ∙ₐ (f₁ , f₂) = g₁ C.∙ f₁ , g₂ C.∙ f₂

  _≈ₐ_ : {A : ∃₂ (λ A₁ A₂ → A₁ ⇒ A₂)}
         {B : ∃₂ (λ B₁ B₂ → B₁ ⇒ B₂)}
         → Rel (A ⇒ₐ B) e
  (g₁ , g₂) ≈ₐ (h₁ , h₂) =  g₁ C.≈ h₁ × g₂ C.≈ h₂

  C⟶ : Category (a ⊔ o) (a) e
  C⟶ = record
              { Object = ∃₂ λ A B → A C.⇒ B 
              ; _⇒_ = _⇒ₐ_
              ; _∙_ = λ {A} {B} {C} g f → _∙ₐ_ {A} {B} {C} g f
              ; Id = λ _ → Id _ , Id _
              ; _≈_ = λ {A} {B} → _≈ₐ_ {A} {B}
              ; assoc = {!!}
              ; id-l = {!!}
              ; id-r = {!!}
              ; isEq = {!!}
              ; congl = {!!}
              ; congr = {!!}
              }
