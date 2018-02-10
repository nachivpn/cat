module Lemma.Abstract where


open import Level
open import Category
open import Iso
open import EpiMono
open import Relation.Binary.SetoidReasoning
open import Data.Product
open import InitTerm
open import Product

module _ {o a e} {C : Category o a e} where

  open Category.Category C
  open Iso.Core C
  open EpiMono.Core C
  open InitTerm.Core C
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

  splitMonoIsMono : ∀ {A B} {f : A ⇒ B} → split-mono f → mono f
  splitMonoIsMono {A} {B} {f} record { l-inv = (g , gf≈Id) } =
    record { monic = λ {C} {i} {j} fi≈fj →
      begin⟨ Hom C A ⟩
        i
          ≈⟨ id-r ⟩
        Id A ∙ i
          ≈⟨ substl (sym isEq gf≈Id) ⟩
        g ∙ f ∙ i
          ≈⟨ sym isEq assoc ⟩
        g ∙ (f ∙ i)
          ≈⟨ substr fi≈fj ⟩
        g ∙ (f ∙ j)
          ≈⟨ assoc ⟩
        g ∙ f ∙ j
          ≈⟨ substl gf≈Id ⟩
        Id A ∙ j
          ≈⟨ sym isEq id-r ⟩
       j ∎ }

  splitEpiIsEpi : ∀ {A B} {f : A ⇒ B} → split-epi f → epi f
  splitEpiIsEpi {A} {B} {f} record { r-inv = (g , fg≈Id) } =
    record { epic = λ {C} {i} {j} if≈jf →
      begin⟨ Hom B C ⟩
      i
        ≈⟨ sym isEq id-l ⟩
      i ∙ Id B
        ≈⟨ substr (sym isEq fg≈Id) ⟩
      i ∙ (f ∙ g)
        ≈⟨ assoc ⟩
      (i ∙ f) ∙ g
        ≈⟨ substl if≈jf ⟩
      (j ∙ f) ∙ g
        ≈⟨ sym isEq assoc ⟩
      j ∙ (f ∙ g)
        ≈⟨ substr fg≈Id ⟩
      j ∙ Id B
        ≈⟨ id-l ⟩
      j ∎  }

  iso∙isoIsIso : ∀ {A B C} {f : A ⇒ B} {g : B ⇒ C} → iso f → iso g → iso (g ∙ f)
  iso∙isoIsIso {A} {B} {C} {f} {g} isof isog =
    record { inv = inv isof ∙ inv isog ;
             bnf = 
               begin⟨ Hom A A ⟩
               (back isof ∙ back isog) ∙ (g ∙ f)
                 ≈⟨ assoc4 ⟩
               back isof ∙ (back isog ∙ g) ∙ f
                 ≈⟨ substl (substr (bnf isog)) ⟩
               back isof ∙ (Id B) ∙ f
                 ≈⟨ substl id-l ⟩
               back isof ∙ f
                 ≈⟨ bnf isof ⟩
               Id A ∎ ;
             fnb =
               begin⟨ Hom C C ⟩
               (g ∙ f) ∙ (back isof ∙ back isog) 
                 ≈⟨ assoc4 ⟩
               g ∙ (f ∙ back isof) ∙ back isog
                 ≈⟨ substl (substr (fnb isof)) ⟩
               g ∙ Id B ∙ back isog 
                 ≈⟨ substl id-l ⟩
               g ∙ back isog
                 ≈⟨ fnb isog ⟩
               Id C ∎ }
  
  initialsAreIsom : ∀ {A B} → initial A → initial B → A ≅ B
  initialsAreIsom {A} {B} (init A2) (init B2) = 
    record {
      ∃iso = witness (A2 B) ,
      record {
        inv = witness (B2 A) ;
        bnf = trans isEq (sym isEq (!A2A tt)) (!A2A tt); 
        fnb = trans isEq (sym isEq (!B2B tt)) (!B2B tt) } }
    where
    !A2A = ump (A2 A)
    !B2B = ump (B2 B)
     
  terminalsAreIsom : ∀ {A B} → terminal A → terminal B → A ≅ B
  terminalsAreIsom {A} {B} (term 2A) (term 2B) =
    record {
      ∃iso = witness (2B A) ,
      record {
        inv = witness (2A B) ;
        bnf = trans isEq (sym isEq (!A2A tt)) (!A2A tt) ;
        fnb = trans isEq (sym isEq (!B2B tt)) (!B2B tt)} }
    where
    !A2A = ump (2A A)
    !B2B = ump (2B B)


  private
    open Product.Core C
    open _x_
    
    prod-unique : ∀ {A B} {P Q : A x B} → pobj P ≅ pobj Q
    prod-unique {A} {B} {P} {Q} =
      let
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
