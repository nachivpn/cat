module Cat where

open import Category
open import Level
open import Functor
open import Prelude.Function
open import Prelude.Equality

_∙_ : ∀ {o a e} {A B C : Category o a e} → B ⇒ C → A ⇒ B → A ⇒ C
G ∙ F = let module G = _⇒_ G
            module F = _⇒_ F
         in record {
            F₀ = G.F₀ ∘ F.F₀ ;
            F₁ = λ {A} {B} f → G.F₁ (F.F₁ f) ;
            F-≈ = {!!};
            F-id = {!!} ;
            F-∙ = {!!} }

Id : ∀ {o a e} → (A : Category o a e) → A ⇒ A
Id A = let module A = Category.Category A in
  record { F₀ = id ; F₁ = id ; F-≈ = λ f g f≈g → f≈g ; F-id = {!!} ; F-∙ = {!!} }

Cat : ∀ (o a e : Level) → Category (lsuc (o ⊔ a ⊔ e)) (o ⊔ a ⊔ e) (e)
Cat o a e = record
        { Object = Category o a e
        ; _⇒_ = _⇒_
        ; _∙_ = _∙_
        ; Id = Id
        ; _≈_ = {!!}
        ; assoc = {!!}
        ; id-l = {!!}
        ; id-r = {!!}
        }
