module Rel where

open import Category
open import Level
open import Prelude.Product
open import Prelude.Equality

R : Set → Set → Set₁
R A B  = A → B → Set

_∙ᵣ_ : {A B C : Set} → R B C → R A B → R A C
RBC ∙ᵣ RAB = λ A C → ∀ {B} → RBC B C → RAB A B

Idᵣ : (A : Set) → R A A
Idᵣ A = λ a₁ a₂ → a₁ ≡ a₂

Rel : Category (lsuc lzero) (lsuc lzero)
Rel = record
        {
          Object = Set ;
          _⇒_ = R ;
          _∙_ = _∙ᵣ_ ;
          Id = Idᵣ ;
          assoc = {!!} ;
          ident = {!!}
        }

