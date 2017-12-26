module Functor where

open import Level as L
open import Category
open import Prelude.Equality


record _⇒_ {co ca do da} (C : Category co ca) (D : Category do da) :
  Set (co ⊔ ca ⊔ do ⊔ da) where
  private
    module C = Category.Category C
    module D = Category.Category D
  field
   -- object map 
   F₀   : C.Object → D.Object
   -- fmap
   F₁   : ∀ {A B} → A C.⇒ B → (F₀ A) D.⇒ (F₀ B)

   -- functor law: identity
   F-id : ∀ {A} → F₁ (C.Id A) ≡ D.Id (F₀ A)

   -- functor law: composition
   F-∙  : ∀ {A' B' C'} (g : B' C.⇒ C') (f : A' C.⇒ B')
     → F₁ (g C.∙ f) ≡ (F₁ g) D.∙ (F₁ f)
