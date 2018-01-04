module Rel where

open import Category
open import Prelude.Product
open import Prelude.Equality

R : Set → Set → Set₁
R A B  = A × B → Set

data ∃ (A : Set) (P : A → Set) : Set where
 <_,_> : (a : A) → P a → ∃ A P

∃-elim : {A : Set} → {P : A → Set} → {Q : Set}
  → ((a : A) → P a → Q) → ∃ A P → Q
∃-elim f < a , p > = f a p

_∧_ = _×_

_∙ᵣ_ : {A B C : Set} → R B C → R A B → R A C
_∙ᵣ_ {A} {B} {C} RBC RAB = λ axc → ∃ B (λ b → RAB (fst axc , b) ∧ RBC (b , snd axc))

Idᵣ : (A : Set) → R A A
Idᵣ _ = λ AxB → fst AxB ≡ snd AxB

-- a useful lemma?
lem : ∀ (X Y : Set) (P : X → Y → Set) → ∃ X (λ x → ∃ Y (λ y → P x y) ) ≡ ∃ Y (λ y → ∃ X (λ x → P x y))
lem X Y P = {!!}

Rel : Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
Rel = record
        {
          Object = Set ;
          _⇒_ = R ;
          _∙_ = _∙ᵣ_ ;
          Id = Idᵣ ;
          _≈_ = _≡_ ;
          assoc = λ A B C D f g h → {!!} ;
          id-l = {!!} ;
          id-r = {!!}
        }

