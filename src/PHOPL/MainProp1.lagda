\AgdaHide{
\begin{code}
module PHOPL.MainProp1 where
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Rules
open import PHOPL.PathSub
open import PHOPL.Red
open import PHOPL.Neutral
open import PHOPL.Meta
open import PHOPL.Computable
open import PHOPL.SubC
open import PHOPL.SN
open import PHOPL.MainPropFinal
open import PHOPL.KeyRedex

postulate subrepsub : ∀ {U} {V} {W} {X} {K} (M : Expression U K) {σ₁ : Sub U V} {σ₂ : Rep V W} {σ₃ : Sub W X} →
                    M ⟦ σ₃ •SR σ₂ • σ₁ ⟧ ≡ M ⟦ σ₁ ⟧ 〈 σ₂ 〉 ⟦ σ₃ ⟧

postulate subrepbotsub-up : ∀ {U} {V} {W} {K} {L} (M : Expression U K) {N : Expression W (varKind L)} {σ : Sub U V} {ρ : Rep V W} →
                            M ⇑ ⟦ x₀:= N •SR Rep↑ _ ρ • Sub↑ _ σ ⟧ ≡ M ⟦ σ ⟧ 〈 ρ 〉

postulate ΛR' : ∀ {V} {Γ : Context V} {φ} {δ} {ψ} → Γ ,P φ ⊢ δ ∶ ψ ⇑ → Γ ⊢ ΛP φ δ ∶ ψ
\end{code}
}

{-Computable-Proof-Substitution : ∀ U V (σ : Sub U V) Γ Δ δ φ →
  σ ∶ Γ ⇒C Δ → Γ ⊢ δ ∶ φ → valid Δ → EP Δ (φ ⟦ σ ⟧) (δ ⟦ σ ⟧)
Computable-Path-Substitution₁ : ∀ U V (σ : Sub U V) Γ Δ P E →
  σ ∶ Γ ⇒C Δ → Γ ⊢ P ∶ E → valid Δ → EE Δ (E ⟦ σ ⟧) (P ⟦ σ ⟧)

Computable-Proof-Substitution U V σ Γ Δ .(var x) .(typeof x Γ) σ∶Γ⇒CΔ (varR x x₁) validΔ = σ∶Γ⇒CΔ x
Computable-Proof-Substitution U V σ Γ Δ .(appP δ ε) .ψ σ∶Γ⇒CΔ (appPR {δ = δ} {ε} {φ} {ψ} Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) validΔ = appP-EP {V} {Δ} {δ ⟦ σ ⟧} {ε ⟦ σ ⟧} {φ ⟦ σ ⟧} {ψ ⟦ σ ⟧}
  (Computable-Proof-Substitution U V σ Γ Δ δ (φ ⊃ ψ) σ∶Γ⇒CΔ Γ⊢δ∶φ⊃ψ validΔ) 
  (Computable-Proof-Substitution U V σ Γ Δ ε φ σ∶Γ⇒CΔ Γ⊢ε∶φ validΔ)
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒CΔ (ΛPR {δ = δ} {φ} {ψ} Γ,φ⊢δ∶ψ) validΔ = 
  aux-lm1 U V σ Γ Δ φ δ ψ 
    (λ W Θ τ τ∶Γ,φ⇒CΘ validΘ → Computable-Proof-Substitution (U , -Proof) W τ (Γ , φ) Θ δ (ψ ⇑)
                          τ∶Γ,φ⇒CΘ Γ,φ⊢δ∶ψ validΘ) σ∶Γ⇒CΔ Γ,φ⊢δ∶ψ validΔ
Computable-Proof-Substitution U V σ Γ Δ δ φ σ∶Γ⇒CΔ (convR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ) validΔ = 
  conv-EP (respects-conv (respects-osr substitution R-respects-sub) φ≃ψ) 
  (Computable-Proof-Substitution U V σ Γ Δ δ _ σ∶Γ⇒CΔ Γ⊢δ∶φ validΔ)
  (Substitution Γ⊢ψ∶Ω validΔ (subC-typed σ∶Γ⇒CΔ))
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒CΔ (plusR Γ⊢P∶φ≡ψ) validΔ = 
  plus-EP (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢P∶φ≡ψ validΔ)
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒CΔ (minusR Γ⊢P∶φ≡ψ) validΔ = 
  minus-EP (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢P∶φ≡ψ validΔ)

Computable-Path-Substitution₁ U V σ Γ Δ .(var x) .(typeof x Γ) σ∶Γ⇒CΔ (varR x x₁) validΔ = σ∶Γ⇒CΔ x
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ (refR {M = M} {A} Γ⊢M∶A) validΔ = ref-EE (Computable-Substitution U V σ Γ Δ M A σ∶Γ⇒CΔ Γ⊢M∶A refl validΔ)
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ (⊃*R Γ⊢P∶φ≡φ' Γ⊢Q∶ψ≡ψ') validΔ = 
  imp*-EE 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢P∶φ≡φ' validΔ) 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢Q∶ψ≡ψ' validΔ)
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) validΔ = 
  univ-EE 
  (Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢δ∶φ⊃ψ validΔ) 
  (Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢ε∶ψ⊃φ validΔ)
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ (lllR .{U} .{Γ} {A} {B} {M} {M'} {P} Γ+⊢P∶Mx≡M'y) validΔ = 
  aux-lm2 U V σ Γ Δ A B M M' P σ∶Γ⇒CΔ Γ+⊢P∶Mx≡M'y validΔ 
  (λ W Θ τ τ∶Γ+⇒Θ validΘ → Computable-Path-Substitution₁ (U , -Term , -Term , -Path) W τ (addpath Γ A) Θ P _ τ∶Γ+⇒Θ Γ+⊢P∶Mx≡M'y validΘ)
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ (app*R {N = N} {N'} {A} Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') validΔ = 
  app*-EE 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢P∶M≡M' validΔ) 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢Q∶N≡N' validΔ)
    (Computable-Substitution U V σ Γ Δ N A σ∶Γ⇒CΔ Γ⊢N∶A refl validΔ)
    (Computable-Substitution U V σ Γ Δ N' A σ∶Γ⇒CΔ Γ⊢N'∶A refl validΔ)
Computable-Path-Substitution₁ U V σ Γ Δ P _ σ∶Γ⇒CΔ (convER {M = M} {M'} {N} {N'} {A} Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') validΔ = 
  conv-EE  (Computable-Path-Substitution₁ U V σ Γ Δ P _ σ∶Γ⇒CΔ Γ⊢P∶M≡N validΔ) (respects-conv (respects-osr substitution R-respects-sub) 
  M≃M') (respects-conv (respects-osr substitution R-respects-sub) N≃N') (Substitution Γ⊢M'∶A validΔ (subC-typed σ∶Γ⇒CΔ)) (Substitution Γ⊢N'∶A validΔ (subC-typed σ∶Γ⇒CΔ)) -}
--REFACTOR Duplication
\end{code}
}