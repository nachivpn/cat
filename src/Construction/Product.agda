
module Construction.Product where

open import Level
open import Category
open import Functor
open import Prelude.Product
open import Relation.Binary hiding (_⇒_)

module Core {o a e} {C D : Category o a e} where

  module C = Category.Category C
  module D = Category.Category D
   
  _x_ : (C D : Category o a e) → Category o a e
  C x D = record
       { Object = C.Object × D.Object
       ; _⇒_ = λ o₁ o₂ →  (fst o₁ C.⇒ fst o₂) × (snd o₁ D.⇒ snd o₂)
       ; _∙_ = λ f g → (fst f C.∙ fst g) , (snd f D.∙ snd g)
       ; Id = λ A → C.Id (fst A) , D.Id (snd A)
       ; _≈_ = λ f g → (fst f C.≈ fst g) × (snd f D.≈ snd g)
       ; assoc = C.assoc , D.assoc
       ; id-l = C.id-l , D.id-l
       ; id-r = C.id-r , D.id-r
       ; isEq = record {
         refl = refl C.isEq , refl D.isEq ;
         sym = λ x → sym C.isEq (fst x) , sym D.isEq (snd x) ;
         trans = λ x y →
           trans C.isEq (fst x) (fst y) , trans D.isEq (snd x) (snd y) }
       ; congl = λ x y p f →
               C.congl (fst x) (fst y) (fst p) (fst f) ,
               D.congl (snd x) (snd y) (snd p) (snd f)
       ; congr = λ x y p f →
               C.congr (fst x) (fst y) (fst p) (fst f) ,
               D.congr (snd x) (snd y) (snd p) (snd f)
       }


-- Projection functors

  π₁ : (C x D) ⇒ C
  π₁ = record 
    { F₀ = fst
    ; F₁ = fst
    ; F-≈ = fst
    ; F-id =  λ {A} → refl C.isEq
    ; F-∙ = λ _ _ → refl C.isEq }

  π₂ : (C x D) ⇒ D
  π₂ = record 
    { F₀ = snd
    ; F₁ = snd
    ; F-≈ = snd
    ; F-id = λ {A} → refl D.isEq
    ; F-∙ = λ _ _ → refl D.isEq }
