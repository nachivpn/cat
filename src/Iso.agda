module Iso where


open import Level
open import Category
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.EqReasoning


module Core {o a e} {C : Category o a e} where

  open Category.Category C

  record _≅_ (A B : Object) : Set (a ⊔ e) where
    field
      forth : A ⇒ B
      back  : B ⇒ A
      bnf   : back ∙ forth ≈ Id A
      fnb   : forth ∙ back ≈ Id B

  open _≅_
  
  unique-inverse : ∀ {A B} (iso : A ≅ B) (g : B ⇒ A)
    → g ∙ forth iso ≈ Id A
    → forth iso ∙ g ≈ Id B
    → back iso ≈ g
  unique-inverse {A} {B} iso g p q =
    let
      trans = IsEquivalence.trans
      sym = IsEquivalence.trans
      f = forth iso
      f⁻¹ = back iso
    in 
    (begin
      {!!})
      {!!}
