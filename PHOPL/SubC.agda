module PHOPL.SubC where
open import Data.Product hiding (_,_)
open import Prelims
open import PHOPL
open import PHOPL.Close
open import PHOPL.Meta
open import PHOPL.Computable
open import PHOPL.PathSub

_∶_⇒C_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set
σ ∶ Γ ⇒C Δ = (∀ x → E Δ (close (typeof x Γ)) (σ _ x)) × 
             (∀ x → EP Δ (typeof x Γ ⟦ σ ⟧) (σ _ x)) ×
             (∀ x → EE Δ (typeof x Γ ⟦ σ ⟧) (σ _ x))

postulate change-cod : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} →
                     σ ∶ Γ ⇒C Δ → Δ ≡ Δ' → σ ∶ Γ ⇒C Δ'

postulate compC : ∀ {U} {V} {W} {ρ : Sub V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                ρ ∶ Δ ⇒C Θ → σ ∶ Γ ⇒C Δ → ρ • σ ∶ Γ ⇒C Θ

postulate comp₁C : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                 ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒C Δ → ρ •₁ σ ∶ Γ ⇒C Θ

postulate comp₂C : ∀ {U} {V} {W} {σ : Sub V W} {ρ : Rep U V} {Γ} {Δ} {Θ} →
                 σ ∶ Δ ⇒C Θ → ρ ∶ Γ ⇒R Δ → σ •₂ ρ ∶ Γ ⇒C Θ

postulate Sub↑C : ∀ {U} {V} {σ : Sub U V} {K} {Γ} {Δ} {A} →
                    σ ∶ Γ ⇒C Δ → Sub↑ K σ ∶ (Γ , A) ⇒C (Δ , A ⟦ σ ⟧)

postulate botsubC : ∀ {V} {Γ : Context V} {M} {A} →
                    E Γ (close A) M → x₀:= M ∶ (Γ ,T A) ⇒C Γ

postulate botsubCP : ∀ {V} {Γ : Context V} {δ} {φ} →
                     EP Γ φ δ → x₀:= δ ∶ (Γ ,P φ) ⇒C Γ

postulate botsubCE : ∀ {V} {Γ : Context V} {P} {E} →
                     EE Γ E P → x₀:= P ∶ (Γ ,E E) ⇒C Γ

postulate subC-typed : ∀ {U} {V} {σ : Sub U V} {Γ : Context U} {Δ : Context V} →
                     σ ∶ Γ ⇒C Δ → σ ∶ Γ ⇒ Δ

_∶_∼_∶_⇒C_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ = ∀ x → EE Δ (ρ _ x ≡〈 typeof x Γ ⟦ ρ ⟧ 〉 σ _ x) (τ x)

