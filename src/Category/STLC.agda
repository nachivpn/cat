module Category.STLC where

open import Category hiding (refl ; sym ; trans)
open import Relation.Binary.PropositionalEquality
open import Product
open import Data.Product

STLCCat : Category (lsuc lzero) lzero lzero
STLCCat = record
                { Object = Set
                ; _⇒_ = λ A B → (A → B)
                ; _∙_ = λ f g → (λ x → f (g x))
                ; Id = λ A → (λ x → x)
                ; _≈_ = _≡_
                ; isEq = isEquivalence
                ; assoc = refl
                ; id-l = refl
                ; id-r = refl
                ; congl = λ x y p f → cong _ p
                ; congr = λ x y p f → cong _ p
                }

open Category.Category STLCCat
open Product.Core STLCCat

_×'_ : (A B : Object) → A x B
A ×' B = record {
  pobj = A × B ;
  π₁ = proj₁ ;
  π₂ = proj₂ ;
  uni = λ Z z₁ z₂ → (λ x → z₁ x , z₂ x) , (refl , refl) , auxlem }
  where
  auxlem : ∀ {Z z₁ z₂} {y : Z → A × B} →
       proj₁ ∙ y ≡ z₁ × proj₂ ∙ y ≡ z₂ →
       (λ x → z₁ x , z₂ x) ≡ y
  auxlem (refl , refl) = refl

data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B

open _+_

_+'_ : (A B : Object) → A + B
A +' B = record {
  cpobj = Either A B ;
  i₁ = left ;
  i₂ = right ;
  uni = λ Z z₁ z₂ → u z₁ z₂ , (refl , refl) , aux₂ z₁ z₂ }
  where
  u : ∀ {A B Z} → (z₁ : A ⇒ Z) (z₂ : B ⇒ Z) → Either A B ⇒ Z
  u z₁ z₂ (left x) = z₁ x
  u z₁ z₂ (right x) = z₂ x
  aux₂ : ∀ {A B Z} (z₁ : A → Z) (z₂ : B → Z) {y : Either A B → Z} →
    y ∙ left ≈ z₁ × y ∙ right ≈ z₂ → u z₁ z₂ ≈ y
  aux₂
    .(λ x → y (left x))
    .(λ x → y (right x)) {y} (refl , refl) = {!!}
