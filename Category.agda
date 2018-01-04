{-# OPTIONS --universe-polymorphism #-}

module Category where

open import Level as L

lsuc = L.suc
lzero = L.zero

record Category o a e : Set (lsuc (o ⊔ a ⊔ e)) where
  field
   Object : Set o
   _⇒_  : Object → Object → Set a

   -- Arrow composition
   _∙_    : {A B C : Object} → B ⇒ C → A ⇒ B → A ⇒ C

   -- Identity
   Id     : (A : Object) → A ⇒ A

   -- Arrow equality
   _≈_ : {A B : Object} (f g : A ⇒ B) → Set e

  infix 19 _≈_
  
  field
   -- associativity law of arrow composition
   assoc : (A B C D : Object)
     → (f : A ⇒ B) → (g : B ⇒ C) → (h : C ⇒ D)
     → h ∙ ( g ∙ f) ≈ (h ∙ g) ∙ f

   -- left identity law
   id-l : (A B : Object)
     → (f : A ⇒ B)
     → f ∙ (Id A) ≈ f

   -- right identity law
   id-r : (A B : Object)
     → (f : A ⇒ B)
     → f ≈ (Id B) ∙ f
