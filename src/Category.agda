{-# OPTIONS --universe-polymorphism #-}

module Category where

open import Level as L public
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.SetoidReasoning
open import Data.Unit public
open import Data.Product as DP using (∃! ; ∃ ; _×_ ; proj₁ ; proj₂)

lsuc = L.suc
lzero = L.zero
refl  = IsEquivalence.refl
sym   = IsEquivalence.sym
trans = IsEquivalence.trans

record Category o a e : Set (lsuc (o ⊔ a ⊔ e)) where
  field
   Object : Set o
   _⇒_  : Object → Object → Set a

   -- Arrow composition
   _∙_    : {A B C : Object} → B ⇒ C → A ⇒ B → A ⇒ C

   -- Identity
   Id     : (A : Object) → A ⇒ A

   -- Arrow equality
   _≈_ : {A B : Object} → Rel (A ⇒ B) e

  infix 19 _≈_
  infixl 20 _∙_
  
  field
   -- associativity law of arrow composition
   assoc : {A B C D : Object}
     {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
     → h ∙ ( g ∙ f) ≈ (h ∙ g) ∙ f

   -- left identity law
   id-l : {A B : Object}
     → {f : A ⇒ B}
     → f ∙ (Id A) ≈ f

   -- right identity law
   id-r : {A B : Object}
     → {f : A ⇒ B}
     → f ≈ (Id B) ∙ f

   isEq : {A B : Object} → IsEquivalence (_≈_ {A} {B})

   congl : ∀ {A B C : Object} (x y : A ⇒ B) → x ≈ y → (f : B ⇒ C) → f ∙ x ≈ f ∙ y

   congr : ∀ {A B C : Object} (x y : B ⇒ C) → x ≈ y → (f : A ⇒ B) → x ∙ f ≈ y ∙ f


  dom : ∀ {A B : Object} → A ⇒ B → Object
  dom {A = A} _ = A

  cod : ∀ {A B : Object} → A ⇒ B → Object
  cod {B = B} _ = B

  Hom : (A B : Object) → Setoid a e
  Hom A B = record {
    Carrier = A ⇒ B ;
    _≈_ = _≈_ ;
    isEquivalence = isEq }

  substl : ∀ {A B C : Object} {x y : B ⇒ C} {f : A ⇒ B} → x ≈ y → x ∙ f ≈ y ∙ f
  substl {A} {B} {C} {x} {y} {f} x≈y = congr x y x≈y f

  substr : ∀ {A B C : Object} {x y : A ⇒ B} {f : B ⇒ C} → x ≈ y → f ∙ x ≈ f ∙ y
  substr {A} {B} {C} {x} {y} {f} x≈y = congl x y x≈y f

  ∃!_⇒_,_ : ∀ {b} (A B : Object) (P : A ⇒ B → Set b) → Set (a ⊔ e ⊔ b)
  ∃! A ⇒ B , P = DP.∃! _≈_ λ x → P x

  ∃!_⇒_ : (A B : Object) → Set (a ⊔ e)
  ∃! A ⇒ B  = ∃! A ⇒ B , λ x → ⊤

  witness : ∀ {b} {A B : Object} {P : A ⇒ B → Set b} → ∃! A ⇒ B , P → A ⇒ B
  witness = DP.proj₁

  witness-pr : ∀ {b} {A B : Object} {P : A ⇒ B → Set b} → (p : ∃! A ⇒ B , P) → P (witness p)
  witness-pr p = DP.proj₁ (DP.proj₂ p)

  -- Universal Mapping Property
  ump : ∀ {b} {A B : Object} {P : A ⇒ B → Set b} → (p : ∃! A ⇒ B , P)
    → ({y : A ⇒ B} → P y → witness p ≈ y)
  ump p = DP.proj₂ (DP.proj₂ p)

  ------------
  -- Lemmas --
  ------------
  
  assoc4 : ∀ {A B C D E : Object}
    { f : A ⇒ B } {g : B ⇒ C} {h : C ⇒ D} {i : D ⇒ E} →
    (i ∙ h) ∙ (g ∙ f) ≈ i ∙ (h ∙ g) ∙ f
  assoc4 {A} {B} {C} {D} {E} {f = f} {g = g} {h = h} {i = i} =
    begin⟨ Hom A E ⟩
      (i ∙ h) ∙ (g ∙ f)
        ≈⟨ assoc ⟩
      (i ∙ h) ∙ g ∙ f
         ≈⟨ congr _ _ (sym isEq assoc) f ⟩
      i ∙ (h ∙ g) ∙ f
    ∎ 
