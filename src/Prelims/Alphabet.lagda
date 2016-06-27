\AgdaHide
{
\begin{code}
module Prelims.Alphabet where
open import Data.List
\end{code}
}

Let $A$ be a set of \emph{kinds}.  An \emph{alphabet} is a sequence of \emph{variables},
to each of which is associated a kind.

\begin{code}
infixl 55 _,_
data Alphabet (A : Set) : Set where
  ∅ : Alphabet A
  _,_ : Alphabet A → A → Alphabet A

extend : ∀ {A} → Alphabet A → List A → Alphabet A
extend V [] = V
extend V (A ∷ AA) = extend (V , A) AA

_⊎_ : ∀ {A} → Alphabet A → Alphabet A → Alphabet A
A ⊎ ∅ = A
A ⊎ (B , K) = (A ⊎ B) , K
\end{code}

Given an alphabet $V$ and kind $K$, we write \textsf{Var \, A \, K} for the set of variables in $A$ of kind $K$.

%TODO Proper formatting

\begin{code}
data Var {A} : Alphabet A → A → Set where
  x₀ : ∀ {A} {K} → Var (A , K) K
  ↑  : ∀ {A} {K} {L} → Var A L → Var (A , K) L

x₁ : ∀ {A} {V} {K} {L} → Var {A} (V , K , L) K
x₁ = ↑ x₀

x₂ : ∀ {S} {V} {K} {L} {L'} → Var {S} (V , K , L , L') K
x₂ = ↑ x₁
\end{code}
