module SetsInj where

open import Category
open import Prelude.Nat
open import Prelude.Function
open import Prelude.Equality
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

SetsInj : Category (lsuc lzero) (lsuc lzero)
SetsInj = record{
              Object = Set ;
              _⇒_ = _⇒ᵢ_;
              _∙_ = _∙ᵢ_;
              Id = λ A → record { fun = id ; inj = λ a a' ida≡ida' → ida≡ida' } ;
              assoc = λ A B C D f g h → refl ;
              ident = λ A B f → refl , refl
            }

                
