\AgdaHide{
\begin{code}
module Prelims.RTClosure where

Relation : Set → Set₁
Relation A = A → A → Set

data RTClose {A : Set} (R : Relation A) : Relation A where
  inc : ∀ {x} {y} → R x y → RTClose R x y
  ref : ∀ {x} → RTClose R x x
  trans : ∀ {x} {y} {z} → RTClose R x y → RTClose R y z → RTClose R x z
\end{code}
}