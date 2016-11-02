\begin{code}
module Prelims.Snoclist where
open import Data.Nat
open import Data.Fin

infixl 20 _snoc_
data snocList (A : Set) : Set where
  [] : snocList A
  _snoc_ : snocList A → A → snocList A

replicate : ∀ {A} → ℕ → A → snocList A
replicate zero _ = []
replicate (suc n) a = replicate n a snoc a

data snocVec (A : Set) : ℕ → Set where
  [] : snocVec A zero
  _snoc_ : ∀ {n} → snocVec A n → A → snocVec A (suc n)

lookup : ∀ {A : Set} {n} → Fin n → snocVec A n → A
lookup zero (_ snoc x) = x
lookup (suc i) (v snoc _) = lookup i v
\end{code}
