module Rel where

open import Category
open import Prelude.Function
open import Prelude.Product
open import Relation.Binary.PropositionalEquality

R : Set → Set → Set₁
R A B  = A × B → Set

data _≈ᵣ_ {A B} (P Q : R A B) : Set where
  eq :  (∀ x → P x → Q x) → (∀ y → Q y → P y) → P ≈ᵣ Q

data ∃ (A : Set) (P : A → Set) : Set where
 <_,_> : (a : A) → P a → ∃ A P

∃-elim : {A : Set} → {P : A → Set} → {Q : Set}
  → ((a : A) → P a → Q) → ∃ A P → Q
∃-elim f < a , p > = f a p

_∧_ = _×_

_∙ᵣ_ : {A B C : Set} → R B C → R A B → R A C
_∙ᵣ_ {A} {B} {C} RBC RAB =  λ axc → ∃ B (λ b → RAB (fst axc , b) ∧ RBC (b , snd axc))

Idᵣ : (A : Set) → R A A
Idᵣ _ = λ AxB → fst AxB ≡ snd AxB

refl-≈ᵣ : ∀ {A B} {R : R A B} → R ≈ᵣ R
refl-≈ᵣ = let id' = (λ _ → id) in eq  id' id'

sym-≈ᵣ : ∀ {A B} {R S : R A B} → R ≈ᵣ S → S ≈ᵣ R
sym-≈ᵣ (eq p q) = eq q p

trans-≈ᵣ : ∀ {A B} {R S T : R A B} → R ≈ᵣ S → S ≈ᵣ T → R ≈ᵣ T
trans-≈ᵣ (eq p q) (eq x y) = eq (λ x₁ z → x x₁ (p x₁ z)) (λ y₁ z → q y₁ (y y₁ z))

assoc-∙ : (A B C D : Set) (f : R A B) (g : R B C) (h : R C D) → (h ∙ᵣ (g ∙ᵣ f)) ≈ᵣ ((h ∙ᵣ g) ∙ᵣ f)
assoc-∙ A B C D f g h = eq lem₁ lem₂
  where
    -- the following lemmas are simply a swap of ∃ c ∃ b and ∃ b ∃ c 
    lem₁ : ∀ x → (h ∙ᵣ (g ∙ᵣ f)) x → ((h ∙ᵣ g) ∙ᵣ f) x
    lem₁ _ (< c , (< b , (fab , gbc) > , hcd) >) = < b , (fab , < c , (gbc , hcd) >) >
    lem₂ : (y : Σ A (λ _ → D)) → ((h ∙ᵣ g) ∙ᵣ f) y → (h ∙ᵣ (g ∙ᵣ f)) y
    lem₂ _ < b , (fab , < c , (gbc , hcd) >) > = < c , (< b , (fab , gbc) > , hcd) >

Rel : Category (lsuc lzero) (lsuc lzero) (lzero)
Rel = record
        {
          Object = Set ;
          _⇒_ = R ;
          _∙_ = _∙ᵣ_ ;
          Id = Idᵣ ;
          _≈_ = _≈ᵣ_ ;
          isEq = record { refl = refl-≈ᵣ; sym = sym-≈ᵣ ; trans = trans-≈ᵣ } ;
          assoc = assoc-∙ ;
          id-l = {!!} ;
          id-r = {!!}
        }

