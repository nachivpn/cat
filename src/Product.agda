module Product where

open import Level
open import Category
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.SetoidReasoning
open import Data.Product as ′ using (_×_ ; proj₁ ; proj₂)


record HasProducts {o a e} (C : Category o a e) : Set (o ⊔ a ⊔ e) where

  open Category.Category C
  
  field
    _x_       : (A B : Object) → Object
    π₁        : {A B : Object} → (A x B) ⇒ A
    π₂        : {A B : Object} → (A x B) ⇒ B
    uni       : ∀ {A B : Object} (Z : Object) (z₁ : Z ⇒ A) (z₂ : Z ⇒ B) →
      ∃! Z ⇒ (A x B) , λ u → π₁ ∙ u ≈ z₁ × π₂ ∙ u ≈ z₂

  <_,_> : ∀ {c a b} → c ⇒ a → c ⇒ b → c ⇒ (a x b)
  < p , q > = witness (uni _ p q)
  
  _⊗_ : ∀{a b c d} → a ⇒ b → c ⇒ d → (a x c) ⇒ (b x d)  -- \ o x
  f ⊗ g = < (f ∙ π₁) , (g ∙ π₂) >

  π₁-pair : ∀{A B C} {f : A ⇒ B} {g : A ⇒ C} → π₁ ∙ < f , _ > ≈ f
  π₁-pair {f = f} {g = g} = proj₁ (witness-pr (uni _ f g))

  π₂-pair : ∀{A B C} {f : A ⇒ B} {g : A ⇒ C} → π₂ ∙ < _ , g > ≈ g
  π₂-pair {f = f} {g = g} = proj₂ (witness-pr (uni _ f g))

  uniq-pair  : ∀ {A B Z z₁ z₂} {y : Z ⇒ (A x B)}
      → (π₁ ∙ y) ≈ z₁ → (π₂ ∙ y) ≈ z₂ → < z₁ , z₂ > ≈ y
  uniq-pair p q = ump (uni _ _ _) (p ′., q)
  
record HasCoProducts {o a e} (C : Category o a e) : Set (o ⊔ a ⊔ e) where

  open Category.Category C
  
  field
    _+_       : (A B : Object) → Object
    i₁        : {A B : Object} → A ⇒ (A + B) 
    i₂        : {A B : Object} → B ⇒ (A + B)
    uni       : ∀ {A B : Object} (Z : Object) (z₁ : A ⇒ Z) (z₂ : B ⇒ Z) →
      ∃! (A + B) ⇒ Z , λ u → u ∙ i₁ ≈ z₁ × u ∙ i₂ ≈ z₂

  [_,_] : ∀ {a b c} → a ⇒ c → b ⇒ c → (a + b) ⇒ c
  [ f , g ] = witness (uni _ f g)

  match-i₁ : ∀{a b c} {f : a ⇒ c} {g : b ⇒ c} → ([ f , _ ] ∙ i₁) ≈ f
  match-i₁ {f = f} {g = g} = proj₁ (witness-pr (uni _ f g))

  match-i₂ : ∀{a b c} {f : a ⇒ c} {g : b ⇒ c} → ([ _ , g ] ∙ i₂) ≈ g
  match-i₂ {f = f} {g = g} = proj₂ (witness-pr (uni _ f g))
  
  uniq-match : ∀ {A B Z z₁ z₂} {y : (A + B) ⇒ Z} →
      ((y ∙ i₁) ≈ z₁) → ((y ∙ i₂) ≈ z₂) → [ z₁ , z₂ ] ≈ y
  uniq-match p q = ump (uni _ _ _) (p ′., q)
