module PHOPL.SN where
open import PHOPL
open import PHOPL.Red

postulate βE-exp : ∀ {V} {A} {M N : Term V} {P} {Q} →
                 SN M → SN N → SN Q →
                 SN (P ⟦ x₀:= (Q ⇑ ⇑) ⟧ ⟦ x₀:= (N ⇑) ⟧ ⟦ x₀:= M ⟧) →
                 SN (app* M N (λλλ A P) Q)
