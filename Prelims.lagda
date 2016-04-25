\section{Preliminaries}

\begin{code}
module Prelims where

open import Relation.Binary.PropositionalEquality public using (_≡_;refl;sym;trans;cong;cong₂;subst;subst₂) 

module ≡-Reasoning {a} {A : Set a} where
  open Relation.Binary.PropositionalEquality.≡-Reasoning {a} {A} public

  infixr 2 _≡⟨⟨_⟩⟩_
  _≡⟨⟨_⟩⟩_ : ∀ (x : A) {y z} → y ≡ x → y ≡ z → x ≡ z
  _ ≡⟨⟨ y≡x ⟩⟩ y≡z = trans (sym y≡x) y≡z
--TODO Add this to standard library
\end{code}

