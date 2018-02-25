module Category.STLC where

open import Category hiding (refl ; sym ; trans)
open import Product
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)
open import Equality.Extensionality as Ext using (_≈_ ; IsEquivalence; eq ; _$≈_)
open import Relation.Binary.PropositionalEquality

STLCCat : Category (lsuc lzero) lzero lzero
STLCCat = record
                { Object = Set
                ; _⇒_ = λ A B → (A → B)
                ; _∙_ = λ f g → (λ x → f (g x))
                ; Id = λ A → (λ x → x)
                ; _≈_ = _≈_
                ; isEq = IsEquivalence
                ; assoc = eq λ x → refl
                ; id-l = eq λ x → refl
                ; id-r = eq λ x → refl
                ; congl = λ _ _ p f → eq λ x → cong f (p $≈ x)
                ; congr = λ _ _ p f → eq λ x → p $≈ f x
                }

open Category.Category STLCCat
open Product.Core STLCCat
open ≡-Reasoning

_×'_ : (A B : Object) → A x B
A ×' B = record {
  pobj = A × B ;
  π₁ = proj₁ ;
  π₂ = proj₂ ;
  uni = λ Z z₁ z₂ →
    (λ x → (z₁ x) , z₂ x) ,
    (eq (λ x → refl) , eq λ x → refl) ,
    λ {y} p → eq λ x → 
      begin
        z₁ x , z₂ x
          ≡⟨ subst
             (λ q → (z₁ x , _) ≡ (q , _))
             (sym (proj₁ p $≈ x))
             (subst (λ q → (_ , z₂ x) ≡ (_ , q))
               (sym ((proj₂ p $≈ x)))
               refl) ⟩
        (proj₁ ∙ y) x , (proj₂ ∙ y) x
          ≡⟨ refl ⟩
        y x ∎  }
      
data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B

open _+_

_+'_ : (A B : Object) → A + B
A +' B = record {
  cpobj = Either A B ;
  i₁ = left ;
  i₂ = right ;
  uni = λ Z z₁ z₂ →
    u z₁ z₂ ,
    ((eq λ x → refl) , (eq λ x → refl)) ,
    λ {y} p → eq λ x₁ → lemma1 y x₁ p}
  where
  u : ∀ {A B Z} → (z₁ : A ⇒ Z) (z₂ : B ⇒ Z) → Either A B ⇒ Z
  u z₁ z₂ (left x) = z₁ x
  u z₁ z₂ (right x) = z₂ x
  lemma1 : ∀ {A B Z} {z₁ : A → Z} {z₂ : B → Z}
        → (y : Either A B → Z)
        → (x : Either A B)
        → (y ∙ left) Ext.≈ z₁ × (y ∙ right) Ext.≈ z₂ 
        → u z₁ z₂ x ≡ y x
  lemma1 _ (left x)  (p , _) = sym (p $≈ x)
  lemma1 _ (right x) (_ , q) = sym (q $≈ x)
