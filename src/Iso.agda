open import Category as CatLib
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.SetoidReasoning
open import Data.Product

module Iso {o a e} (C : Category o a e) where

  open CatLib.Category C

  record IsIso {A B : Object} (f : A ⇒ B) : Set (o ⊔ a ⊔ e) where

    field
      inv : B ⇒ A
      
    forth : A ⇒ B
    forth = f

    back : B ⇒ A
    back = inv

    field
      bnf : (back ∙ forth ≈ Id A)
      fnb : (forth ∙ back ≈ Id B)

  -- end of IsIso
  
  record _≅_ (X Y : Object) : Set (o ⊔ a ⊔ e) where
    field
      ∃iso : ∃ λ (f : X ⇒ Y) → IsIso f
      
  -- end of _≅_
  
  open IsIso

  -- start of proofs
  
  unique-inverse : ∀ {A B} {f : A ⇒ B} (iso : IsIso f) (g : B ⇒ A)
      → g ∙ forth iso ≈ Id A
      → forth iso ∙ g ≈ Id B
      → g ≈ back iso
  unique-inverse {A} {B} iso g p q =  
      let
        f = forth iso
        f⁻¹ = back iso
      in
      begin⟨ Hom B A ⟩
      g
          ≈⟨ sym isEq id-l ⟩
      g ∙ Id B
          ≈⟨ congl (Id B) (f ∙ f⁻¹) (sym isEq (fnb iso)) g ⟩
      g ∙ (f ∙ f⁻¹)
          ≈⟨ assoc ⟩
      (g ∙ f) ∙  f⁻¹
          ≈⟨ congr (g ∙ f) (Id A) p f⁻¹ ⟩
      Id A ∙  f⁻¹
           ≈⟨ sym isEq id-r ⟩
      f⁻¹
     ∎


  open _≅_
  
  refl-≅ : ∀ {A : Object} → A ≅ A
  refl-≅ {A} = record { ∃iso = (Id A) ,
    record {
      inv = Id A ;
      bnf = id-l ;
      fnb = id-l } } 

  
  sym-≅ : ∀ {A B} → A ≅ B → B ≅ A
  sym-≅ record { ∃iso = (f , isof) } =
    record {
      ∃iso = back isof ,
        record {
          inv = forth isof ;
          bnf = fnb isof ;
          fnb = bnf isof
        }
    }

  trans-≅ : ∀ {A B C} → A ≅ B → B ≅ C → A ≅ C
  trans-≅ {A} {B} {C} record { ∃iso = (f , isof) } record { ∃iso = (g , isog) } =
    let fi = inv isof
        gi = inv isog
    in record {
      ∃iso = g ∙ f ,
        record {
          inv =  inv isof ∙ inv isog ;
          bnf =  
            begin⟨ Hom A A ⟩
               (fi ∙ gi) ∙ (g ∙ f)
                   ≈⟨ assoc4  ⟩
               fi ∙ (gi ∙ g) ∙ f
                   ≈⟨ congr _ _ (congl _ _ (bnf isog) fi) f ⟩
               fi ∙ Id B ∙ f
                   ≈⟨ congr _ _ id-l f ⟩
               fi ∙ f
                   ≈⟨ bnf isof ⟩
               Id A ∎ ;
          fnb = 
            begin⟨ Hom C C ⟩
              (g ∙ f) ∙ (fi ∙ gi)
                   ≈⟨ assoc4 ⟩
              g ∙ (f ∙ fi) ∙ gi
                   ≈⟨ congr _ _ (congl _ _ (fnb isof) g) gi ⟩
              g ∙ Id B ∙ gi
                   ≈⟨ congr _ _ id-l gi ⟩
              g ∙ gi
                   ≈⟨ fnb isog ⟩
              Id C ∎
        }
      }

  isoIsEq : IsEquivalence _≅_
  isoIsEq = record { refl = refl-≅ ; sym = sym-≅ ; trans = trans-≅ }
