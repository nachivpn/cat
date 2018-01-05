module SetsInj where

open import Category
open import Prelude.Function
open import Relation.Binary.PropositionalEquality
open import Prelude.Product

-- injective function
record _⇒ᵢ_ (from : Set) (to : Set) : Set₁ where
  field
    fun  : from → to
    inj  : ∀ a a' → fun a ≡ fun a' → a ≡ a'   

-- utilities
fun = _⇒ᵢ_.fun
inj = _⇒ᵢ_.inj

-- composing injective functions yields an injective function
_∙ᵢ_ : ∀ {A B C} → B ⇒ᵢ C → A ⇒ᵢ B  → A ⇒ᵢ C
q ∙ᵢ p =
                let
                  f     = fun p
                  inj-f = inj p
                  g     = fun q
                  inj-g = inj q
                in
                record{
                  fun = λ z → g (f z) ;
                  inj = λ a a' gfa≡gfa' →
                    inj-f a a'
                      (inj-g (f a) (f a') gfa≡gfa')
                }
                
-- Category of sets with arrows as injective functions
-- (a restricted version of Sets category)
SetsInj : Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
SetsInj = record{
              Object = Set ;
              _⇒_ = _⇒ᵢ_;
              _∙_ = _∙ᵢ_;
              Id = λ A → record { fun = id ; inj = λ a a' ida≡ida' → ida≡ida' } ;
              _≈_ = _≡_ ;
              isEq = isEquivalence ;
              assoc = λ A B C D f g h → refl ;
              id-l = λ A B f → refl ;
              id-r = λ A B f → refl
            }

                
