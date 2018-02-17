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
