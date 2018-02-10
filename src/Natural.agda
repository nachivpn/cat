module Natural where

open import Level
open import Category
open import Functor

record _𝕟⇒_ {o a e} {C D : Category o a e} (F G : C ⇒ D) : Set (o ⊔ a ⊔ e) where

  module C = Category.Category C
  module D = Category.Category D
  module F = _⇒_ F
  module G = _⇒_ G

  field
    η   : ∀ (X : C.Object) → F.F₀ X D.⇒ G.F₀ X
    nat : ∀ {X Y} (f : X C.⇒ Y) → η Y D.∙ F.F₁ f D.≈ G.F₁ f D.∙ η X
