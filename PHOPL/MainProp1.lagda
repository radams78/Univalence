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

Computable-Sub : ∀ {U} {V} {K} (σ : Sub U V) {Γ} {Δ} {M : Expression U (varKind K)} {A} →
  σ ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → E' Δ (A ⟦ σ ⟧) (M ⟦ σ ⟧)
Computable-Sub σ σ∶Γ⇒Δ (varR x validΓ) validΔ = σ∶Γ⇒Δ x
Computable-Sub {V = V} σ {Δ = Δ} σ∶Γ⇒Δ (appR Γ⊢M∶A⇛B Γ⊢N∶A) validΔ = 
  appT-E validΔ (Computable-Sub σ σ∶Γ⇒Δ Γ⊢M∶A⇛B validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢N∶A validΔ)
Computable-Sub σ σ∶Γ⇒Δ (ΛR {M = M} {B} Γ,A⊢M∶B) validΔ = 
  func-E (λ _ Θ ρ N validΘ ρ∶Δ⇒Θ N∈EΘA → 
    let MN∈EΘB = subst (E Θ B) (subrepsub M)
                 (Computable-Sub (x₀:= N •SR Rep↑ _ ρ • Sub↑ -Term σ) 
                 (compC (compSRC (botsubC N∈EΘA) 
                        (Rep↑-typed ρ∶Δ⇒Θ)) 
                 (Sub↑C σ∶Γ⇒Δ)) 
                 Γ,A⊢M∶B validΘ) in
    expand-E MN∈EΘB
      (appR (ΛR (Weakening (Substitution Γ,A⊢M∶B (ctxTR validΔ) (Sub↑-typed (subC-typed σ∶Γ⇒Δ))) 
                                                      (ctxTR validΘ) 
                                         (Rep↑-typed ρ∶Δ⇒Θ))) 
                (E-typed N∈EΘA)) 
      (βTkr (SNap' {Ops = substitution} R-respects-sub (E-SN B MN∈EΘB))))
Computable-Sub σ σ∶Γ⇒Δ (⊥R _) validΔ = ⊥-E validΔ
Computable-Sub σ σ∶Γ⇒Δ (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = ⊃-E 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢φ∶Ω validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ψ∶Ω validΔ)
Computable-Sub σ σ∶Γ⇒Δ (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) validΔ = appP-EP 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢δ∶φ⊃ψ validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ε∶φ validΔ)
Computable-Sub σ σ∶Γ⇒Δ (ΛPR {δ = δ} {φ} {ψ} Γ,φ⊢δ∶ψ) validΔ = 
  func-EP (λ W Θ ρ ε ρ∶Δ⇒Θ ε∈EΔφ → 
    let δε∈EΘψ : EP Θ (ψ ⟦ σ ⟧ 〈 ρ 〉) (δ ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= ε ⟧)
        δε∈EΘψ = {!!} in
    expand-EP 
    {!!} {!!} (βPkr {!!} (EP-SN ε∈EΔφ))) 
  {!!}
Computable-Sub σ σ∶Γ⇒Δ (convR Γ⊢M∶A Γ⊢M∶A₁ x) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒Δ (refR Γ⊢M∶A) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒Δ (⊃*R Γ⊢M∶A Γ⊢M∶A₁) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒Δ (univR Γ⊢M∶A Γ⊢M∶A₁) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒Δ (plusR Γ⊢M∶A) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒Δ (minusR Γ⊢M∶A) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒Δ (lllR Γ⊢M∶A) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒Δ (app*R Γ⊢M∶A Γ⊢M∶A₁ Γ⊢M∶A₂ Γ⊢M∶A₃) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒Δ (convER Γ⊢M∶A Γ⊢M∶A₁ Γ⊢M∶A₂ M≃M' N≃N') validΔ = {!!}

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
