module Product where


open import Level
open import Category
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.SetoidReasoning
import Data.Product as DP


module Core {o a e} (C : Category o a e) where

  open Category.Category C

  record _x_ (A B : Object) : Set (o ⊔ a ⊔ e) where
    field
     pobj      : Object
     π₁        : pobj ⇒ A
     π₂        : pobj ⇒ B
     uni : ∀ (Z : Object) (z₁ : Z ⇒ A) (z₂ : Z ⇒ B) →
       ∃! Z ⇒ pobj , λ u → π₁ ∙ u ≈ z₁ DP.× π₂ ∙ u ≈ z₂

  record _+_ (A B : Object) : Set (o ⊔ a ⊔ e) where
    field
     cpobj     : Object
     i₁        : A ⇒ cpobj
     i₂        : B ⇒ cpobj
     uni : ∀ (Z : Object) (z₁ : A ⇒ Z) (z₂ : B ⇒ Z) →
       ∃! cpobj ⇒ Z , λ u → u ∙ i₁ ≈ z₁ DP.× u ∙ i₂ ≈ z₂



  
