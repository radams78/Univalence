\begin{code}
module PHOPL.SN where
open import PHOPL.Grammar
open import PHOPL.Red

postulate βE-exp : ∀ {V} {A} {M N : Term V} {P} {Q} →
                 SN M → SN N → SN Q →
                 SN (P ⟦ x₀:= M • x₀:= (N ⇑) • x₀:= (Q ⇑ ⇑) ⟧) →
                 SN (app* M N (λλλ A P) Q)
\end{code}
