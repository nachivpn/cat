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
              ; assoc = assoc , assoc
              ; id-l = id-l , id-l
              ; id-r = id-r , id-r
              ; isEq =
                record {
                  refl = (refl isEq) , refl isEq ;
                  sym = λ x → sym isEq (proj₁ x) , sym isEq (proj₂ x) ;
                  trans =
                    λ x y → (trans isEq (proj₁ x) (proj₁ y)) , trans isEq (proj₂ x) (proj₂ y)
                }
              ; congl = λ x y p f →
                congl (proj₁ x) (proj₁ y) (proj₁ p) (proj₁ f) ,
                congl (proj₂ x) (proj₂ y) (proj₂ p) (proj₂ f)
              ; congr = λ x y p f →
                congr (proj₁ x) (proj₁ y) (proj₁ p) (proj₁ f) ,
                congr (proj₂ x) (proj₂ y) (proj₂ p) (proj₂ f)
              }
