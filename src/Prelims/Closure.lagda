\AgdaHide{
\begin{code}
module Prelims.Closure where
open import Relation.Binary.PropositionalEquality hiding (sym;trans)
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

R-sub-RT : ∀ {A} {R} {x} {y} → RClose {A} R x y → RTClose R x y
R-sub-RT (inc xRy) = inc xRy
R-sub-RT ref = ref

T-sub-RT : ∀ {A} {R} {x} {y} → TClose {A} R x y → RTClose R x y
T-sub-RT (inc xRy) = inc xRy
T-sub-RT (trans xRy yRz) = trans (T-sub-RT xRy) (T-sub-RT yRz)

data RSTClose {A : Set} (R : Relation A) : Relation A where
  inc : ∀ {x y} → R x y → RSTClose R x y
  ref : ∀ {x} → RSTClose R x x
  sym : ∀ {x y} → RSTClose R x y → RSTClose R y x
  trans : ∀ {x y z} → RSTClose R x y → RSTClose R y z → RSTClose R x z

RT-sub-RST : ∀ {A R x y} → RTClose {A} R x y → RSTClose R x y
RT-sub-RST (inc xRy) = inc xRy
RT-sub-RST ref = ref
RT-sub-RST (trans xRTy yRTz) = trans (RT-sub-RST xRTy) (RT-sub-RST yRTz)
\end{code}
}
