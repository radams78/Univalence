module Prelims.ListR where

--Lists with cons on the right

data ListR (A : Set) : Set where
  [] : ListR A
  _∷_ : ListR A → A → ListR A
