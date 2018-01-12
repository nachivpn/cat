module Cat where

open import Category
open import Level
open import Functor
open import Prelude.Function
open import Relation.Binary hiding (_⇒_)

_∙_ : ∀ {o a e} {C D E : Category o a e} → D ⇒ E → C ⇒ D → C ⇒ E
_∙_ {E = E} G F = let
            module G = _⇒_ G
            module F = _⇒_ F
            module E = Category.Category E
         in record {
            F₀ = G.F₀ ∘ F.F₀ ;
            F₁ = λ {A} {B} f → G.F₁ (F.F₁ f) ;
            F-≈ = G.F-≈ ∘ F.F-≈ ;
            F-id = λ {O} →
              IsEquivalence.trans E.isEq (G.F-≈ F.F-id) G.F-id ;
            F-∙ = λ g f →
              IsEquivalence.trans E.isEq
                (G.F-≈ (F.F-∙ g f)) (G.F-∙ (F.F₁ g) (F.F₁ f))}

Id : ∀ {o a e} → (A : Category o a e) → A ⇒ A
Id A = let module A = Category.Category A in
  record {
    F₀ = id ;
    F₁ = id ;
    F-≈ = id ;
    F-id = λ {A₁} → IsEquivalence.refl (A.isEq {A₁} {A₁}) ;
    F-∙ = λ {A} {_} {C} g f → IsEquivalence.refl (A.isEq {A} {C})
  }

Cat : ∀ (o a e : Level) → Category (lsuc (o ⊔ a ⊔ e)) (o ⊔ a ⊔ e) (e)
Cat o a e = record
        { Object = Category o a e
        ; _⇒_ = _⇒_
        ; _∙_ = _∙_
        ; Id = Id
        ; _≈_ = {!!}
        ; isEq = {!!}
        ; assoc = {!!}
        ; id-l = {!!}
        ; id-r = {!!}
        ; congl = {!!}
        ; congr = {!!}
        }
