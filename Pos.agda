module Pos where

open import Category
open import Prelude.Function
open import Prelude.Product
open import Prelude.Equality hiding (Eq ; trans)

record Eq (A : Set) : Set₁ where
  field
    _≅_ : A → A → Set

-- Partially ordered set
record Poset : Set₁ where
  field
    A     : Set
    eq    : Eq A
  open Eq eq public
  field
    _<=_  : A → A → Set 
    reflx  : ∀ (a : A) → a <= a
    asymt  : ∀ (a b : A) → a <= b → b <= a → a ≅ b
    trans : ∀ (a b c : A) → a <= b → b <= c → a <= c

-- Monotonic function
record _⇒_ (P Q : Poset) : Set where
  private
    module P = Poset P
    module Q = Poset Q
  field
    m        : P.A → Q.A
    monotone : ∀ (a a' : P.A) → a P.<= a' → m a Q.<= m a' 

-- composing monotones gives a monotone
_∙_ : {A B C : Poset} → B ⇒ C → A ⇒ B → A ⇒ C
g ∙ f = record {
  m = (_⇒_.m g) ∘ (_⇒_.m f) ;
  monotone = λ a a' a<=a' →
    let f-m = _⇒_.m f 
        g-m = _⇒_.m g in
    _⇒_.monotone g (f-m a) (f-m a') (_⇒_.monotone f a a' a<=a') }

Id : (A : Poset) → A ⇒ A
Id = λ A → record { m = id ; monotone = λ a a' a<=a' → a<=a' }

-- category of posets
Pos : Category (lsuc lzero) lzero
Pos = record {
  Object = Poset ;
  _⇒_ = _⇒_ ;
  _∙_ = _∙_ ;
  Id = Id ;
  assoc = λ A B C D f g h → refl ;
  ident = λ A B f → refl , refl }

-- a poset as a category
PosetAsCategory : Poset → Category lzero lzero
PosetAsCategory P = let module P = Poset P in record {
  Object = P.A ;
  _⇒_ = λ a b → a P.<= b ;
  _∙_ = λ {A} {B} {C} B<=C A<=B → P.trans A B C A<=B B<=C ;
  Id = P.reflx ;
  assoc = λ A B C D f g h → {!!} ;
  ident = λ A B f → {!!} , {!!} }
