module Rel where

open import Category
open import Prelude.Function
open import Prelude.Product
open import Relation.Binary.PropositionalEquality
open import Logic.Predicate

R : Set → Set → Set₁
R A B  = A × B → Set

data _≈ᵣ_ {A B} (P Q : R A B) : Set where
  eq :  (∀ x → P x → Q x) → (∀ y → Q y → P y) → P ≈ᵣ Q

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

id-l : (A B : Set) (f : R A B) → (f ∙ᵣ Idᵣ A) ≈ᵣ f
id-l A B f = eq lem₁ lem₂
  where
  lem₁ : ∀ x → (f ∙ᵣ Idᵣ A) x → f x
  lem₁ (.a , b) < a , (refl , fab) > = fab
  lem₂ : ∀ y → f y → (f ∙ᵣ Idᵣ A) y
  lem₂ (a , b) fab = < a , (refl , fab) >

id-r : (A B : Set) (f : R A B) → f ≈ᵣ (Idᵣ B ∙ᵣ f)
id-r A B f = eq lem₁ lem₂
  where
  lem₁ : ∀ x → f x → (Idᵣ B ∙ᵣ f) x
  lem₁ (a , b) fab = < b , (fab , refl) >
  lem₂ : ∀ y → (Idᵣ B ∙ᵣ f) y → f y
  lem₂ (a , b) < .b , (fab , refl) > = fab

congl : {A B C : Set} (x y : R A B) →
  x ≈ᵣ y → (f : R B C) → (f ∙ᵣ x) ≈ᵣ (f ∙ᵣ y)
congl x y (eq y2x x2y) f = eq lem₁ lem₂
  where
  lem₁ : ∀ z → (f ∙ᵣ x) z → (f ∙ᵣ y) z
  lem₁ (a , c) < b , (fbc , xab) > = < b , (y2x (a , b) fbc , xab) >
  lem₂ : ∀ z → (f ∙ᵣ y) z → (f ∙ᵣ x) z
  lem₂ (a , c) < b , (yab , fbc) > = < b , (x2y (a , b) yab , fbc) >

congr : {A B C : Set} (x y : R B C) →
  x ≈ᵣ y → (f : R A B) → (x ∙ᵣ f) ≈ᵣ (y ∙ᵣ f)
congr x y (eq x2y y2x) f = eq lem₁ lem₂
  where
  lem₁ : ∀ x₁ → (x ∙ᵣ f) x₁ → (y ∙ᵣ f) x₁
  lem₁ (a , c) < b , (fab , xbc) > = < b , (fab , x2y (b , c) xbc) >
  lem₂ : ∀ y₁ → (y ∙ᵣ f) y₁ → (x ∙ᵣ f) y₁
  lem₂ (a , c) < b , (fab , ybc) > = < b , (fab , y2x (b , c) ybc) >
  
Rel : Category (lsuc lzero) (lsuc lzero) (lzero)
Rel = record {
          Object = Set ;
          _⇒_ = R ;
          _∙_ = _∙ᵣ_ ;
          Id = Idᵣ ;
          _≈_ = _≈ᵣ_ ;
          isEq = record { refl = refl-≈ᵣ; sym = sym-≈ᵣ ; trans = trans-≈ᵣ } ;
          assoc = assoc-∙ _ _ _ _ ;
          id-l = id-l ;
          id-r = id-r ;
          congl = congl ;
          congr = congr
        }
