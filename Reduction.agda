open import Grammar.Base

module Reduction (G : Grammar) (R : Grammar.Reduction G) where

open import Reduction.Base G R public
open import Reduction.SN G R public
