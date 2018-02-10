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
     prod      : Object
     π₁        : prod ⇒ A
     π₂        : prod ⇒ B
     universal : ∀ (Z : Object) (z₁ : Z ⇒ A) (z₂ : Z ⇒ B) →
       ∃! Z ⇒ prod , λ u → π₁ ∙ u ≈ z₁ DP.× π₂ ∙ u ≈ z₂



  
