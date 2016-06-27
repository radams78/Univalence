\AgdaHide{
\begin{code}
module Prelims.PiExp where
open import Data.List
open import Prelims.Alphabet
\end{code}
}

A \emph{$\Pi$-expression} over $S$ and $T$ is an expression of the form $A_1 \rightarrow \cdots \rightarrow A_n \rightarrow B$, where each $A_i \in S$ and $B \in T$.

\begin{code}
record PiExp (S : Set) (T : Set) : Set where
  constructor _⟶_
  field
    dom : List S
    cod : T

dom : ∀ {S} {T} → Alphabet S → PiExp S T → Alphabet S
dom V (AA ⟶ _) = extend V AA
\end{code}
