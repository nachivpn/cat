open import Category
open import CCC  
open import InitTerm
open import Product

module BCCC  where

  record IsBCCC {o a e} (C : Category o a e) : Set (o ⊔ a ⊔ e) where
  
    open Category.Category C
    
    field
      isCCC     : IsCCC C
      hasInit   : HasInitial C
      hasCoProd : HasCoProducts C

