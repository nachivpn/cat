{-# OPTIONS --universe-polymorphism #-}

module Category where

open import Level
open import Prelude.Function
open import Prelude.Equality
open import Prelude.Product

record Category x : Set (suc x) where
  field
   Object : Set x
   Arrow  : Object → Object → Set
   _∙_    : {A B C : Object} → Arrow B C → Arrow A B → Arrow A C
   Id     : (A : Object) → Arrow A A
   

   -- properties
   assoc : (A B C D : Object)
     → (f : Arrow A B) → (g : Arrow B C) → (h : Arrow C D)
     → h ∙ ( g ∙ f) ≡ (h ∙ g) ∙ f

   ident : (A B : Object)
     → (f : Arrow A B)
     → f ∙ (Id A) ≡ f × f ≡ (Id B) ∙ f  

SetCategory : Category (suc zero)
SetCategory = record
                { Object = Set
                ; Arrow = λ A B → (A → B)
                ; _∙_ = λ f g → λ z → f (g z)
                ; Id = λ A → id
                ; assoc = λ A B C D f g h → refl
                ; ident = λ A B f → refl , refl
                }
