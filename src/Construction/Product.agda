
module Construction.Product where

open import Level
open import Category
open import Functor
open import Data.Product
open import Relation.Binary hiding (_⇒_)

module Core {o a e} {C D : Category o a e} where

  module C = Category.Category C
  module D = Category.Category D
   
  _x_ : (C D : Category o a e) → Category o a e
  C x D = record
       { Object = C.Object × D.Object
       ; _⇒_ = λ o₁ o₂ →  (proj₁ o₁ C.⇒ proj₁ o₂) × (proj₂ o₁ D.⇒ proj₂ o₂)
       ; _∙_ = λ f g → (proj₁ f C.∙ proj₁ g) , (proj₂ f D.∙ proj₂ g)
       ; Id = λ A → C.Id (proj₁ A) , D.Id (proj₂ A)
       ; _≈_ = λ f g → (proj₁ f C.≈ proj₁ g) × (proj₂ f D.≈ proj₂ g)
       ; assoc = C.assoc , D.assoc
       ; id-l = C.id-l , D.id-l
       ; id-r = C.id-r , D.id-r
       ; isEq = record {
         refl = refl C.isEq , refl D.isEq ;
         sym = λ x → sym C.isEq (proj₁ x) , sym D.isEq (proj₂ x) ;
         trans = λ x y →
           trans C.isEq (proj₁ x) (proj₁ y) , trans D.isEq (proj₂ x) (proj₂ y) }
       ; congl = λ x y p f →
               C.congl (proj₁ x) (proj₁ y) (proj₁ p) (proj₁ f) ,
               D.congl (proj₂ x) (proj₂ y) (proj₂ p) (proj₂ f)
       ; congr = λ x y p f →
               C.congr (proj₁ x) (proj₁ y) (proj₁ p) (proj₁ f) ,
               D.congr (proj₂ x) (proj₂ y) (proj₂ p) (proj₂ f)
       }


-- Projection functors

  π₁ : (C x D) ⇒ C
  π₁ = record 
    { F₀ = proj₁
    ; F₁ = proj₁
    ; F-≈ = proj₁
    ; F-id =  λ {A} → refl C.isEq
    ; F-∙ = λ _ _ → refl C.isEq }

  π₂ : (C x D) ⇒ D
  π₂ = record 
    { F₀ = proj₂
    ; F₁ = proj₂
    ; F-≈ = proj₂
    ; F-id = λ {A} → refl D.isEq
    ; F-∙ = λ _ _ → refl D.isEq }
