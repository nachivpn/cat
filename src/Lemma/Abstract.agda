module Lemma.Abstract where


open import Level
open import Category
open import Iso
open import EpiMono
open import Relation.Binary.SetoidReasoning

module _ {o a e} {C : Category o a e} where

  open Category.Category C
  open Iso.Core {C = C}
  open EpiMono.Core {C = C}
  open iso
  
  isoIsEpi : ∀ {A B} {f : A ⇒ B} → iso f → epi f
  isoIsEpi {A} {B} {f} iso =
    record { epic = λ {C} {i} {j} if≈jf →
      begin⟨ Hom B C ⟩
        i
          ≈⟨ sym isEq id-l ⟩
        i ∙ Id B
          ≈⟨ congl _ _ (sym isEq (fnb iso)) i ⟩
        i ∙ (forth iso ∙ back iso)
          ≈⟨ assoc ⟩
        (i ∙ forth iso) ∙ back iso
          ≈⟨ congr _ _ if≈jf (back iso) ⟩
        (j ∙ forth iso) ∙ back iso
          ≈⟨ sym isEq assoc ⟩
        j ∙ (forth iso ∙ back iso)
          ≈⟨ congl _ _ (fnb iso) j ⟩
        j ∙ Id B
          ≈⟨ id-l ⟩
        j ∎  }

  isoIsMono : ∀ {A B} {f : A ⇒ B} → iso f → mono f
  isoIsMono {A} {B} {f} iso =
    record { monic = λ {C} {i} {j} fi≈fj →
      begin⟨ Hom C A ⟩
        i
          ≈⟨ id-r ⟩
        Id A ∙ i
          ≈⟨ congr _ _ (sym isEq (bnf iso)) i ⟩
        back iso ∙ forth iso ∙ i
          ≈⟨ sym isEq assoc ⟩
        back iso ∙ (forth iso ∙ i)
          ≈⟨ congl _ _ fi≈fj (back iso) ⟩
        back iso ∙ (forth iso ∙ j)
          ≈⟨ assoc ⟩
        (back iso ∙ forth iso) ∙ j
          ≈⟨ congr _ _ (bnf iso) j ⟩
        Id A ∙ j
          ≈⟨ sym isEq id-r ⟩
        j ∎      }
