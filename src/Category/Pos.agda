module Category.Pos where

open import Category hiding (refl ; sym ; trans)
open import Prelude.Function
open import Prelude.Product
open import Relation.Binary hiding (_⇒_ ; Poset)
open import Relation.Binary.PropositionalEquality as Eq hiding (trans)
open import Prelude.Unit

-- Partially ordered set
record Poset : Set₁ where
  field
    Car    : Set
    _<=_   : Car → Car → Set 
    reflx  : ∀ (a : Car) → a <= a
    asymt  : ∀ (a b : Car) → a <= b → b <= a → a ≡ b
    trans  : ∀ {a b c : Car} → a <= b → b <= c → a <= c
  -- Constructions of <= (proofs) are unique
  -- This aids the "an arrow per <= relation"
  -- construction in PosetAsCategory
  _≈_ : {a b : Car} → (f g : a <= b) → Set
  _≈_ f g = ⊤
  isEq : {a b : Car} → IsEquivalence (_≈_ {a} {b})
  isEq = record { refl = tt ; sym = λ {i} {j} _ → tt ; trans = λ _ _ → tt }

-- Monotonic function
record _⇒_ (P Q : Poset) : Set where
  private
    module P = Poset P
    module Q = Poset Q
  field
    m        : P.Car → Q.Car
    monotone : ∀ (a a' : P.Car) → a P.<= a' → m a Q.<= m a'

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

congl  : {A B C : Poset} (x y : A ⇒ B) →
  x ≡ y → (f : B ⇒ C) → (f ∙ x) ≡ (f ∙ y)
congl x .x refl f = refl

congr : {A B C : Poset} (x y : B ⇒ C) →
  x ≡ y → (f : A ⇒ B) → (x ∙ f) ≡ (y ∙ f)
congr x .x refl f = refl

-- category of posets
Pos : Category (lsuc lzero) lzero lzero
Pos = record {
  Object = Poset ;
  _⇒_ = _⇒_ ;
  _∙_ = _∙_ ;
  Id = Id ;
  _≈_ = _≡_ ;
  isEq = isEquivalence ;
  assoc = refl ;
  id-l = refl ;
  id-r = refl ;
  congl = congl ;
  congr = congr }

-- a poset as a category
PosetAsCategory : Poset → Category lzero lzero lzero
PosetAsCategory P =
  let
    module P = Poset P
  in record {
    Object = P.Car ;
    _⇒_ = λ a b → a P.<= b ;
    _∙_ = λ {a} {b} {c} b<=c a<=b → P.trans a<=b b<=c ;
    Id = P.reflx ;
    _≈_ = P._≈_  -- arrows are unique by definition
  }
