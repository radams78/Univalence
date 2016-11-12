\AgdaHide{
\begin{code}
module Prelims.HetList where
open import Data.Product hiding (zip)
open import Data.List hiding (all;zip)

data HetList {A : Set} (B : A → Set) : List A → Set where
  [] : HetList B []
  _∷_ : ∀ {a aa} → B a → HetList B aa → HetList B (a ∷ aa)

zip : ∀ {A : Set} {B C : A → Set} {aa : List A} → HetList B aa → HetList C aa → 
  HetList (λ a → B a × C a) aa
zip [] [] = []
zip (b ∷ bb) (c ∷ cc) = (b , c) ∷ zip bb cc

data all {A} {B : A → Set} (C : ∀ {a} → B a → Set) : ∀ (aa : List A) → 
  HetList B aa → Set where
  [] : all C [] []
  _∷_ : ∀ {a} {aa} {b} {bb} → C {a} b → all C aa bb → all C (a ∷ aa) (b ∷ bb)
\end{code}
}
