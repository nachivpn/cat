{-# OPTIONS --universe-polymorphism #-}

module Category where

open import Level
open import Prelude.Function
open import Prelude.Equality
open import Prelude.Product

record Category o a : Set (suc (o ⊔ a)) where
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

SetCategory : Category (suc zero) (zero)
SetCategory = record
                { Object = Set
                ; _⇒_ = λ A B → (A → B)
                ; _∙_ = λ f g → λ z → f (g z)
                ; Id = λ A → id
                ; assoc = λ A B C D f g h → refl
                ; ident = λ A B f → refl , refl
                }

record SetWithRelation : Set₂ where
  field
    set : Set₁
    R : set → set → Set

-- how does one concretely represent a partially ordered set?
Poset : SetWithRelation
Poset = record { set = Set ; R = λ A B → {!!} }

PosetCategory : Category (suc zero) (suc zero)
PosetCategory = record
                  { Object = {!!}
                  ; _⇒_ = {!!}
                  ; _∙_ = {!!}
                  ; Id = {!!}
                  ; assoc = {!!}
                  ; ident = {!!}
                  }
