\begin{code}
module PHOPL.SN where
open import PHOPL.Grammar
open import PHOPL.Red

private βR-exp' : ∀ {V} {φ : Term V} {δ} {ε} {χ} → SN φ → SN δ → SN ε →
         SN (δ ⟦ x₀:= ε ⟧) → appP (ΛP φ δ) ε ⇒ χ → SN χ
βR-exp' SNφ SNδ SNε SNδε (redex βR) = SNδε
βR-exp' SNφ SNδ SNε SNδε (app (appl (redex ())))
βR-exp' (SNI φ SNφ) SNδ SNε SNδε (app (appl (app (appl φ⇒φ')))) = 
  SNI _ (λ _ → βR-exp' (SNφ _ φ⇒φ') SNδ SNε SNδε) 
βR-exp' SNφ (SNI δ SNδ) SNε SNδε (app (appl (app (appr (appl δ⇒δ'))))) = 
  SNI _ (λ _ → βR-exp' SNφ (SNδ _ δ⇒δ') SNε (SNred SNδε (apredr substitution R-respects-sub (osr-red δ⇒δ'))))
βR-exp' SNφ SNδ SNε SNδε (app (appl (app (appr (appr ())))))
βR-exp' {δ = δ} SNφ SNδ (SNI ε SNε) SNδε (app (appr (appl ε⇒ε'))) = 
  SNI _ (λ _ → βR-exp' SNφ SNδ (SNε _ ε⇒ε') (SNred SNδε (apredl substitution {E = δ} R-respects-sub (botsub-red ε⇒ε'))))
βR-exp' SNφ SNδ SNε SNδε (app (appr (appr ())))

βR-exp : ∀ {V} {φ : Term V} {δ} {ε} → SN φ → SN ε →
         SN (δ ⟦ x₀:= ε ⟧) → SN (appP (ΛP φ δ) ε)
βR-exp {φ = φ} {δ} {ε} SNφ SNε SNδε = SNI (appP (ΛP φ δ) ε) (λ χ → βR-exp' SNφ 
  (SNap' {Ops = substitution} R-respects-sub SNδε) SNε SNδε)

postulate βE-exp : ∀ {V} {A} {M N : Term V} {P} {Q} →
                 SN M → SN N → SN Q →
                 SN (P ⟦ x₀:= M • x₀:= (N ⇑) • x₀:= (Q ⇑ ⇑) ⟧) →
                 SN (app* M N (λλλ A P) Q)
\end{code}
