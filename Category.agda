{-# OPTIONS --universe-polymorphism #-}

module Category where

open import Level as L
open import Prelude.Equality
open import Prelude.Product

lsuc = L.suc
lzero = L.zero

record Category o a : Set (lsuc (o ⊔ a)) where
  field
   Object : Set o
   _⇒_  : Object → Object → Set a
   _∙_    : {A B C : Object} → B ⇒ C → A ⇒ B → A ⇒ C
   Id     : (A : Object) → A ⇒ A

   -- properties
   assoc : (A B C D : Object)
     → (f : A ⇒ B) → (g : B ⇒ C) → (h : C ⇒ D)
     → h ∙ ( g ∙ f) ≡ (h ∙ g) ∙ f

   ident : (A B : Object)
     → (f : A ⇒ B)
     → f ∙ (Id A) ≡ f × f ≡ (Id B) ∙ f
