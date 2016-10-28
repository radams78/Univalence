\AgdaHide{
\begin{code}
module Prelims.Closure where
open import Relation.Binary.PropositionalEquality hiding (trans)
import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary

Relation : Set → Set₁
Relation A = A → A → Set

data RClose {A : Set} (R : Relation A) : Relation A where
  inc : ∀ {x} {y} → R x y → RClose R x y
  ref : ∀ {x} → RClose R x x

data TClose {A : Set} (R : Relation A) : Relation A where
  inc : ∀ {x} {y} → R x y → TClose R x y
  trans : ∀ {x} {y} {z} → TClose R x y → TClose R y z → TClose R x z

data RTClose {A : Set} (R : Relation A) : Relation A where
  inc : ∀ {x} {y} → R x y → RTClose R x y
  ref : ∀ {x} → RTClose R x x
  trans : ∀ {x} {y} {z} → RTClose R x y → RTClose R y z → RTClose R x z

RTCLOSE : ∀ {A} → Relation A → Preorder _ _ _
RTCLOSE {A} R = record { 
  Carrier = A ; 
  _≈_ = _≡_ ; 
  _∼_ = RTClose R ; 
  isPreorder = record { 
    isEquivalence = Relation.Binary.PropositionalEquality.Core.isEquivalence ; 
    reflexive = λ { {x} .{x} refl → ref } ; 
    trans = trans } }
\end{code}
}
