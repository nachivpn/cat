module Functor where

open import Level as L
open import Category


record _⇒_ {co ca ce do da de} (C : Category co ca ce) (D : Category do da de) :
  Set (co ⊔ ca ⊔ ce ⊔ do ⊔ da ⊔ de) where
  private
    module C = Category.Category C
    module D = Category.Category D
  field
   -- object map 
   F₀   : C.Object → D.Object
   -- fmap
   F₁   : ∀ {A B} → A C.⇒ B → (F₀ A) D.⇒ (F₀ B)
   
   -- ≈ preservation
   F-≈ : ∀ {A B : C.Object} {f g : A C.⇒ B} → f C.≈ g → (F₁ f) D.≈ (F₁ g)

   -- functor law: identity
   F-id : ∀ {A : C.Object} → F₁ (C.Id A) D.≈ D.Id (F₀ A)

   -- functor law: composition
   F-∙  : ∀ {A' B' C' : C.Object} (g : B' C.⇒ C') (f : A' C.⇒ B')
     → F₁ (g C.∙ f) D.≈ (F₁ g) D.∙ (F₁ f)

