\AgdaHide{
\begin{code}
module Prelims.Closure where

Relation : Set → Set₁
Relation A = A → A → Set

data TClose {A : Set} (R : Relation A) : Relation A where
  inc : ∀ {x} {y} → R x y → TClose R x y
  trans : ∀ {x} {y} {z} → TClose R x y → TClose R y z → TClose R x z

data RTClose {A : Set} (R : Relation A) : Relation A where
  inc : ∀ {x} {y} → R x y → RTClose R x y
  ref : ∀ {x} → RTClose R x x
  trans : ∀ {x} {y} {z} → RTClose R x y → RTClose R y z → RTClose R x z
\end{code}
}
