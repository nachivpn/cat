module Category.Sets where

open import Category hiding (refl ; sym ; trans)
open import Prelude.Function
open import Relation.Binary.PropositionalEquality

SetCat : Category (lsuc lzero) lzero lzero
SetCat = record
                { Object = Set
                ; _⇒_ = λ A B → (A → B)
                ; _∙_ = λ f g → f ∘ g
                ; Id = λ A → id
                ; _≈_ = _≡_
                ; isEq = isEquivalence
                ; assoc = refl
                ; id-l = refl
                ; id-r = refl
                ; congl = {!!}
                ; congr = {!!}
                }
