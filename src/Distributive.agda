open import Category
open import BCCC
open import CCC
open import Product
import Iso

module Distributive where
    
record IsDistributive {o a e} (C : Category o a e) : Set (o ⊔ a ⊔ e) where

    open Category.Category C
    
    field
      isBCCC : IsBCCC C

    open Iso C
    open IsBCCC isBCCC
    open IsCCC isCCC
    open HasCoProducts hasCoProd
    open HasProducts hasProd
    
    field
      dist   : ∀ {a b c} → (a x (b + c)) ≅ ((a x b) + (a x c))
