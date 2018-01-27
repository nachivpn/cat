module Iso where


open import Level
open import Category
open import Relation.Binary hiding (_⇒_)
open import Data.Maybe
open import Relation.Binary.SetoidReasoning
open import Data.Nat


module Core {o a e} {C : Category o a e} where

  open Category.Category C

  record _≅_ (A B : Object) : Set (a Level.⊔ e) where
    field
      forth : A ⇒ B
      back  : B ⇒ A
      bnf   : back ∙ forth ≈ Id A
      fnb   : forth ∙ back ≈ Id B

  open _≅_
  
  unique-inverse : ∀ {A B} (iso : A ≅ B) (g : B ⇒ A)
    → g ∙ forth iso ≈ Id A
    → forth iso ∙ g ≈ Id B
    → g ≈ back iso
  unique-inverse {A} {B} iso g p q =
    let
      trans = IsEquivalence.trans
      sym = IsEquivalence.sym
      f = forth iso
      f⁻¹ = back iso
    in begin⟨ Hom B A ⟩
      g
          ≈⟨ sym isEq (id-l _ _ _) ⟩
      g ∙ Id B
          ≈⟨ congl (Id B) (f ∙  f⁻¹) (sym isEq (fnb iso)) g ⟩
      g ∙ (f ∙ f⁻¹)
          ≈⟨ assoc _ _ _  ⟩
      ( g ∙ f ) ∙  f⁻¹
          ≈⟨ congr (g ∙ f) (Id A) p f⁻¹ ⟩
      Id A ∙  f⁻¹
           ≈⟨ sym isEq (id-r _ _ _) ⟩
       f⁻¹
      ∎
