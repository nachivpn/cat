module EpiMono where

open import Level
open import Category
open import Data.Product


module Core {o a e} {C : Category o a e} where

  open Category.Category C

  record mono {A B} (f : A ⇒ B) : Set (o ⊔ a ⊔ e) where
    field
      monic : ∀ {C} {i j : C ⇒ A} → f ∙ i ≈ f ∙ j → i ≈ j

  record epi {A B} (f : A ⇒ B) : Set (o ⊔ a ⊔ e) where
    field
      epic : ∀ {C} {i j : B ⇒ C} → i ∙ f ≈ j ∙ f → i ≈ j

  record split-mono {A B} (f : A ⇒ B) : Set (o ⊔ a ⊔ e) where
    field
      l-inv : ∃ λ g → g ∙ f ≈ Id A

  record split-epi {A B} (f : A ⇒ B) : Set (o ⊔ a ⊔ e) where
    field
     l-inv : ∃ λ g → f ∙ g ≈ Id B



   


  
