module Mon where

open import Category
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Prelude.Function

record Monoid : Set₁ where
  field
    A      : Set
    u      : A
    _∙_    : A → A → A
    assoc  : ∀ {a b c} → a ∙ (b ∙ c) ≡ (a ∙ b) ∙ c
    unit-l : ∀ {x} → x ∙ u ≡ x
    unit-r : ∀ {x} → x ≡ u ∙ x

-- Monoid homomorphism
record _⇒_ (M N : Monoid) : Set where
  private
    module M = Monoid M
    module N = Monoid N
  field
    -- function for the underlying set
    f      : M.A → N.A
    -- preservation of composition, i.e, "structural preservation"
    pres-∙ : ∀ {m₁ m₂ : M.A} → f (m₁ M.∙ m₂) ≡ f m₁ N.∙ f m₂
    -- preservation of unit
    pres-u : f M.u ≡ N.u

_∙_ : ∀ {X Y Z} (g : Y ⇒ Z) (f : X ⇒ Y) → X ⇒ Z
g ∙ f = let
  module f = _⇒_ f
  module g = _⇒_ g in record {
    f =  g.f ∘ f.f ;
    pres-∙ = trans (cong g.f f.pres-∙) g.pres-∙ ;
    pres-u = trans (cong g.f f.pres-u) g.pres-u }
    
Id : (A : Monoid) → A ⇒ A
Id A = record { f = id ; pres-∙ = refl ; pres-u = refl }

MonoidCategory : Monoid → Category lzero lzero lzero
MonoidCategory M = let module M = Monoid M in record
                { Object = ⊤
                ; _⇒_ = λ _ _ → M.A
                ; _∙_ = M._∙_
                ; Id = λ _ → M.u
                ; _≈_ = _≡_
                ; isEq = isEquivalence
                ; assoc = λ _ _ _ _ _ _ _ → M.assoc
                ; id-l = λ _ _ _ → M.unit-l
                ; id-r = λ _ _ _ → M.unit-r
                }

Mon : Category (lsuc lzero) lzero lzero
Mon = record
                { Object = Monoid
                ; _⇒_ = _⇒_
                ; _∙_ = _∙_
                ; Id = Id
                ; _≈_ = {!!}
                ; isEq = {!!}
                ; assoc = λ A B C D f g h → {!!}
                ; id-l = λ A B f → {!!}
                ; id-r = λ A B f → {!!}
                }
