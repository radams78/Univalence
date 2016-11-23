module Prelims.Closure where
open import Relation.Binary.PropositionalEquality hiding (sym;trans)
import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary

data RClose {i} {A : Set} (R : Rel A i) : Rel A i where
  inc : ∀ {x} {y} → R x y → RClose R x y
  ref : ∀ {x} → RClose R x x

data TClose {i} {A : Set} (R : Rel A i) : Rel A i where
  inc : ∀ {x} {y} → R x y → TClose R x y
  trans : ∀ {x} {y} {z} → TClose R x y → TClose R y z → TClose R x z

data RTClose {i} {A : Set} (R : Rel A i) : Rel A i where
  inc : ∀ {x} {y} → R x y → RTClose R x y
  ref : ∀ {x} → RTClose R x x
  trans : ∀ {x} {y} {z} → RTClose R x y → RTClose R y z → RTClose R x z

RTCLOSE : ∀ {i A} → Rel A i → Preorder _ _ _
RTCLOSE {i} {A} R = record { 
  Carrier = A ; 
  _≈_ = _≡_ ; 
  _∼_ = RTClose R ; 
  isPreorder = record { 
    isEquivalence = Relation.Binary.PropositionalEquality.Core.isEquivalence ; 
    reflexive = λ { {x} .{x} refl → ref } ; 
    trans = trans } }

RT-mono : ∀ {i A} {R S : Rel A i} {x y} → (∀ {x y} → R x y → S x y) → RTClose R x y → RTClose S x y
RT-mono R⊆S (inc Rxy) = inc (R⊆S Rxy)
RT-mono R⊆S ref = ref
RT-mono R⊆S (trans RTxy RTyz) = trans (RT-mono R⊆S RTxy) (RT-mono R⊆S RTyz)

R-sub-RT : ∀ {i} {A} {R : Rel A i} {x} {y} → RClose {A = A} R x y → RTClose R x y
R-sub-RT (inc xRy) = inc xRy
R-sub-RT ref = ref

T-sub-RT : ∀ {i} {A} {R : Rel A i} {x} {y} → TClose {A = A} R x y → RTClose R x y
T-sub-RT (inc xRy) = inc xRy
T-sub-RT (trans xRy yRz) = trans (T-sub-RT xRy) (T-sub-RT yRz)

data RSTClose {i} {A : Set} (R : Rel A i) : Rel A i where
  inc : ∀ {x y} → R x y → RSTClose R x y
  ref : ∀ {x} → RSTClose R x x
  sym : ∀ {x y} → RSTClose R x y → RSTClose R y x
  trans : ∀ {x y z} → RSTClose R x y → RSTClose R y z → RSTClose R x z

RSTCLOSE : ∀ {i A} → Rel A i → Setoid _ _
RSTCLOSE {i} {A} R = record { 
  Carrier = A ; 
  _≈_ = RSTClose R ; 
  isEquivalence = record { 
    refl = ref ; 
    sym = sym ; 
    trans = trans } }

RT-sub-RST : ∀ {i A} {R : Rel A i} {x y} → RTClose {A = A} R x y → RSTClose R x y
RT-sub-RST (inc xRy) = inc xRy
RT-sub-RST ref = ref
RT-sub-RST (trans xRTy yRTz) = trans (RT-sub-RST xRTy) (RT-sub-RST yRTz)
