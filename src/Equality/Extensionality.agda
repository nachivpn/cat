module Equality.Extensionality where

open import Level
open import Relation.Binary.PropositionalEquality
  public using (_≡_ ; refl ; sym ; trans)
import Relation.Binary as RB using (IsEquivalence)

data _≈_ {a} {A B : Set a} (f g : A → B) : Set a where
  eq : (∀ x → f x ≡ g x) → f ≈ g

_$≈_ : ∀ {a} {A B : Set a} {f g : A → B} → f ≈ g → (∀ x → f x ≡ g x)
_$≈_ (eq x) = x

IsEquivalence : ∀ {a} {A B : Set a} → RB.IsEquivalence (_≈_ {a} {A} {B})
IsEquivalence =
  record {
    refl = eq λ _ → refl ;
    sym = λ i≈j → eq λ x → sym (i≈j $≈ x) ;
    trans = λ i≈j j≈k → eq λ x → trans (i≈j $≈ x) (j≈k $≈ x) }
