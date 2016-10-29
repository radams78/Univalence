\begin{code}
module PHOPL.SN where
open import Data.Empty renaming (⊥ to Empty)
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Red
open import Reduction.Botsub PHOPL R

private βR-exp' : ∀ {V} {φ : Term V} {δ} {ε} {χ} → SN φ → SN δ → SN ε →
         SN (δ ⟦ x₀:= ε ⟧) → appP (ΛP φ δ) ε ⇒ χ → SN χ
βR-exp' _ _ _ _ (redex (βR ()))
βR-exp' _ _ _ SNδε (redex (R₀R (βR _ _))) = SNδε
βR-exp' _ _ _ _ (app (appl (redex (βR ()))))
βR-exp' _ _ _ _ (app (appl (redex (R₀R ()))))
βR-exp' (SNI _ SNφ) SNδ SNε SNδε (app (appl (app (appl φ⇒φ')))) = SNI _ (λ _ → βR-exp' (SNφ _ φ⇒φ') SNδ SNε SNδε)
βR-exp' SNφ (SNI _ SNδ) SNε SNδε (app (appl (app (appr (appl δ⇒δ'))))) = 
  SNI _ (λ _ → βR-exp' SNφ (SNδ _ δ⇒δ') SNε (SNred SNδε (apredr SUB R-respects-sub (inc δ⇒δ'))))
βR-exp' _ _ _ _ (app (appl (app (appr (appr ())))))
βR-exp' {δ = δ} SNφ SNδ (SNI _ SNε) SNδε (app (appr (appl ε⇒ε'))) = 
  SNI _ (λ _ → βR-exp' SNφ SNδ (SNε _ ε⇒ε') 
    (SNred SNδε (apredl SUB {E = δ} R-respects-sub (botsub-red ε⇒ε'))))
βR-exp' _ _ _ _ (app (appr (appr ())))

βR-exp : ∀ {V} {φ : Term V} {δ} {ε} → SN φ → SN ε →
         SN (δ ⟦ x₀:= ε ⟧) → SN (appP (ΛP φ δ) ε)
βR-exp {φ = φ} {δ} {ε} SNφ SNε SNδε = SNI (appP (ΛP φ δ) ε) (λ χ → βR-exp' SNφ 
  (SNap' {Ops = SUB} R-respects-sub SNδε) SNε SNδε)

private βE-exp' : ∀ {V} {A} {M N : Term V} {P} {Q} {R} →
                 SN M → SN N → SN P → SN Q →
                 SN (P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧) →
                 app* M N (λλλ A P) Q ⇒ R →
                 SN R
βE-exp' SNM SNN SNP SNQ SNPMNQ (redex (βR ()))
βE-exp' SNM SNN SNP SNQ SNPMNQ (redex (R₀R (βE _ _ _ _))) = SNPMNQ
βE-exp' {P = P} (SNI M SNM) SNN SNP SNQ SNPMNQ (app (appl M⇒M')) = 
  SNI _ (λ _ → βE-exp' (SNM _ M⇒M') SNN SNP SNQ 
    (SNred SNPMNQ (apredl SUB {E = P} R-respects-sub 
      (botsub₃-red (inc M⇒M') ref ref)))) 
βE-exp' {P = P} SNM (SNI _ SNN) SNP SNQ SNPMNQ (app (appr (appl N⇒N'))) = 
  SNI _ (λ _ → βE-exp' SNM (SNN _ N⇒N') SNP SNQ 
    (SNred SNPMNQ (apredl SUB {E = P} R-respects-sub 
      (botsub₃-red ref (inc N⇒N') ref))))
βE-exp' SNM SNN SNP SNQ SNPMNQ (app (appr (appr (appl (redex (βR ()))))))
βE-exp' SNM SNN SNP SNQ SNPMNQ (app (appr (appr (appl (redex (R₀R ()))))))
βE-exp' SNM SNN (SNI _ SNP) SNQ SNPMNQ (app (appr (appr (appl (app (appl P⇒P')))))) = 
  SNI _ (λ _ → βE-exp' SNM SNN (SNP _ P⇒P') SNQ
    (SNred SNPMNQ (apredr SUB R-respects-sub (inc P⇒P'))))
βE-exp' SNM SNN SNP SNQ SNPMNQ (app (appr (appr (appl (app (appr ()))))))
βE-exp' {P = P} SNM SNN SNP (SNI _ SNQ) SNPMNQ (app (appr (appr (appr (appl Q⇒Q'))))) = 
  SNI _ (λ _ → βE-exp' SNM SNN SNP (SNQ _ Q⇒Q') 
    (SNred SNPMNQ (apredl SUB {E = P} R-respects-sub 
      (botsub₃-red ref ref (inc Q⇒Q')))))
βE-exp' SNM SNN SNP SNQ SNPMNQ (app (appr (appr (appr (appr ())))))

βE-exp : ∀ {V} {A} {M N : Term V} {P} {Q} →
         SN M → SN N → SN Q →
         SN (P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧) →
         SN (app* M N (λλλ A P) Q)
βE-exp SNM SNN SNQ SNPQ = SNI _ (λ R PQ⇒R → βE-exp' SNM SNN (SNap' {Ops = SUB} R-respects-sub SNPQ) SNQ SNPQ PQ⇒R)

--REFACTOR Common pattern

private SN' : ∀ {V} {φ : Term V} → ⊥ ⇒ φ → Empty
SN' (redex (βR ()))
SN' (redex (R₀R ()))
SN' (app ())

SN⊥ : ∀ {V} → SN {V} ⊥
SN⊥ {V} = SNI ⊥ (λ _ ⊥⇒F → ⊥-elim (SN' ⊥⇒F))
\end{code}
