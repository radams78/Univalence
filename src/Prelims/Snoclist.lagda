\begin{code}
module Prelims.Snoclist where

infixl 20 _snoc_
data snocList (A : Set) : Set where
  [] : snocList A
  _snoc_ : snocList A → A → snocList A
\end{code}
