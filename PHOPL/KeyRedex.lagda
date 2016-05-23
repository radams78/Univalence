\begin{code}
module PHOPL.KeyRedex where
open import PHOPL.Grammar
open import PHOPL.Red

data key-redex {V} : ∀ {K} → Expression V K → Expression V K → Set where
  βkr : ∀ {φ : Term V} {δ ε} (SNφ : SN φ) (SNε : SN ε) → key-redex (appP (ΛP φ δ) ε) (δ ⟦ x₀:= ε ⟧)
  βEkr : ∀ {N N' : Term V} {A} {P} {Q} (SNN : SN N) (SNN' : SN N') (SNQ : SN Q) →
           key-redex (app* N N' (λλλ A P) Q) (P ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧)
  appTkr : ∀ {M N P : Term V} → key-redex M N → key-redex (appT M P) (appT N P)
\end{code}
