open import Level
open import Category

module BCCC  where

  open import CCC public  
  open import InitTerm public
  
  record IsBCCC {o a e} (C : Category o a e) : Set (o ⊔ a ⊔ e) where
  
    open Category.Category C
    
    field
      isCCC     : IsCCC C
      hasInit   : HasInitial C
      hasCoProd : HasCoProducts C

    open HasInitial hasInit public   
    open HasCoProducts hasCoProd public   
     
