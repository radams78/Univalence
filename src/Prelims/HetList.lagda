\AgdaHide{
\begin{code}
module Prelims.HetList where
open import Data.Product hiding (zip)
open import Data.List hiding (all;zip)
open import Prelims.Snoclist

data HetList {A : Set} (B : A → Set) : List A → Set where
  [] : HetList B []
  _∷_ : ∀ {a aa} → B a → HetList B aa → HetList B (a ∷ aa)

K : ∀ A B → List A → Set
K A B = HetList {A} (λ _ → B)

zip : ∀ {A : Set} {B C : A → Set} {aa : List A} → HetList B aa → HetList C aa → 
  HetList (λ a → B a × C a) aa
zip [] [] = []
zip (b ∷ bb) (c ∷ cc) = (b , c) ∷ zip bb cc

data all {A} {B : A → Set} (C : ∀ {a} → B a → Set) : ∀ (aa : List A) → 
  HetList B aa → Set where
  [] : all C [] []
  _∷_ : ∀ {a} {aa} {b} {bb} → C {a} b → all C aa bb → all C (a ∷ aa) (b ∷ bb)

unhet : ∀ {A B aa} → K A B aa → List B
unhet [] = []
unhet (b ∷ bb) = b ∷ unhet bb

infixl 20 _snoc_
data HetsnocList {A} (B : A → Set) : snocList A → Set where
  [] : HetsnocList B []
  _snoc_ : ∀ {aa} {a} → HetsnocList B aa → B a → HetsnocList B (aa snoc a)
\end{code}
}
