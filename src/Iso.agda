module Iso where


open import Level
open import Category


module Core {o a e} {C : Category o a e} where

  open Category.Category C

  record _≅_ (A B : Object) : Set (a ⊔ e) where
    field
      forth : A ⇒ B
      back  : B ⇒ A
      bnf   : back ∙ forth ≈ Id A
      fnb   : forth ∙ back ≈ Id B
