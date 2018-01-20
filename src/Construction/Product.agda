module Construction.Product where

open import Level
open import Category
open import Prelude.Product
open import Relation.Binary

_x_ : ∀ {o a e} (C D : Category o a e) → Category o a e
C x D = let 
     module C = Category.Category C
     module D = Category.Category D
     refl = IsEquivalence.refl
     sym = IsEquivalence.sym
     trans = IsEquivalence.trans
  in record
       { Object = C.Object × D.Object
       ; _⇒_ = λ o₁ o₂ →  (fst o₁ C.⇒ fst o₂) × (snd o₁ D.⇒ snd o₂)
       ; _∙_ = λ f g → (fst f C.∙ fst g) , (snd f D.∙ snd g)
       ; Id = λ A → C.Id (fst A) , D.Id (snd A)
       ; _≈_ = λ f g → (fst f C.≈ fst g) × (snd f D.≈ snd g)
       ; assoc = λ f g h → C.assoc _ _ _ , D.assoc _ _ _
       ; id-l = λ A B f → C.id-l _ _ _ , D.id-l _ _ _
       ; id-r = λ A B f → C.id-r _ _ _ , D.id-r _ _ _
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
