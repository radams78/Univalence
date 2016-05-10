open import Grammar.Base

module Reduction (G : Grammar)   
  (R : ∀ {V} {K} {C : Grammar.Kind G (Grammar.-Constructor {G} K)} → 
    Grammar.Constructor G C → 
    Grammar.Subexpression G V (Grammar.-Constructor {G} K) C → 
    Grammar.Expression G V K → Set) where

open import Reduction.Base G R public
open import Reduction.SN G R public
