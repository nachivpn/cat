module Lemma.AbstractProduct where

-- Lemmas about products

open import Level
open import Category

module Core {o a e} {C : Category o a e} where

  open import Iso
  open import Relation.Binary.SetoidReasoning
  open import Data.Product
  
  open import Product

  open Category.Category C
  open Iso.Core C

  open Product.Core C
  open _x_
    
  prod-unique : ∀ {A B} {P Q : A x B} → pobj P ≅ pobj Q
  prod-unique {A} {B} {P} {Q} = let
        module P = _x_ P
        module Q = _x_ Q
        testPonQ = Q.uni P.pobj P.π₁ P.π₂
        testQonP = P.uni Q.pobj Q.π₁ Q.π₂
        testPonP = P.uni P.pobj P.π₁ P.π₂
        testQonQ = Q.uni Q.pobj Q.π₁ Q.π₂
        f = witness testPonQ
        b = witness testQonP
        f-pr = witness-pr testPonQ
        b-pr = witness-pr testQonP
        umpP₁ : witness testPonP ≈ Id P.pobj
        umpP₁ = ump testPonP (id-l , id-l)
        umpP₂ : witness testPonP ≈ b ∙ f
        umpP₂ = ump testPonP (
          (begin⟨ Hom P.pobj A ⟩
            P.π₁ ∙ (b ∙ f)
              ≈⟨ assoc ⟩
            (P.π₁ ∙ b) ∙ f
              ≈⟨ substl (proj₁ b-pr) ⟩
            Q.π₁ ∙ f
              ≈⟨ proj₁ f-pr ⟩
            P.π₁ ∎) ,
          (begin⟨ Hom P.pobj B ⟩
            P.π₂ ∙ (b ∙ f)
              ≈⟨ assoc ⟩
            (P.π₂ ∙ b) ∙ f
              ≈⟨ substl (proj₂ b-pr) ⟩
            Q.π₂ ∙ f
              ≈⟨ proj₂ f-pr ⟩
            P.π₂ ∎) )
        umpQ₁ : witness testQonQ ≈ Id Q.pobj
        umpQ₁ = ump testQonQ (id-l , id-l)
        umpQ₂ : witness testQonQ ≈ f ∙ b
        umpQ₂ = ump testQonQ (
          (begin⟨ Hom Q.pobj A ⟩
            Q.π₁ ∙ (f ∙ b)
              ≈⟨ assoc ⟩
            (Q.π₁ ∙ f) ∙ b
              ≈⟨ substl (proj₁ f-pr) ⟩
            P.π₁ ∙ b
              ≈⟨ proj₁ b-pr ⟩
            Q.π₁ ∎) ,
          (begin⟨ Hom Q.pobj B ⟩
            Q.π₂ ∙ (f ∙ b)
               ≈⟨ assoc ⟩
            (Q.π₂ ∙ f) ∙ b
              ≈⟨ substl (proj₂ f-pr) ⟩
            P.π₂ ∙ b
              ≈⟨ proj₂ b-pr ⟩
            Q.π₂ ∎))
      in record {
        ∃iso = f ,
        record {
          inv = b ;
          bnf = trans isEq (sym isEq umpP₂) umpP₁;
          fnb = trans isEq (sym isEq umpQ₂) umpQ₁ } }
