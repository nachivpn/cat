module Rel where

open import Category
open import Level
open import Prelude.Product
open import Prelude.Equality


R : Set → Set → Set₁
R A B  = A × B → Set

_∙ᵣ_ : {A B C : Set} → R B C → R A B → R A C
RBC ∙ᵣ RAB = λ AxC → ∀ {B} → RBC (B , snd AxC) → RAB (fst AxC , B)

Idᵣ : (A : Set) → R A A
Idᵣ _ = λ AxB → fst AxB ≡ snd AxB
 
Rel : Category (lsuc lzero) (lsuc lzero)
Rel = record
        {
          Object = Set ;
          _⇒_ = R ;
          _∙_ = _∙ᵣ_ ;
          Id = Idᵣ ;
          assoc = λ A B C D f g h → {!!} ;
          ident = λ A B f → {!!} , {!!}
        }

