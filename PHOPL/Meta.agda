module PHOPL.Meta where
open import PHOPL
open import PHOPL.Rules

postulate β-respects-sub : respects' substitution

postulate Prop-Validity : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} → 
                        Γ ⊢ δ ∶ φ → Γ ⊢ φ ∶ Ω

postulate _∶_⇒R_ : ∀ {U} {V} → Rep U V → Context U → Context V → Set

postulate Rep↑-typed : ∀ {U} {V} {ρ : Rep U V} {K} {Γ} {Δ} {A} →
                     ρ ∶ Γ ⇒R Δ → Rep↑ K ρ ∶ (Γ , A) ⇒R (Δ , A 〈 ρ 〉)

postulate Weakening : ∀ {U} {V} {ρ : Rep U V} {K}
                    {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
                    Γ ⊢ M ∶ A → valid Δ → ρ ∶ Γ ⇒R Δ → Δ ⊢ M 〈 ρ 〉 ∶ A 〈 ρ 〉

postulate _∶_⇒_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set

postulate Substitution : ∀ {U} {V} {σ : Sub U V} {K}
                       {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
                       Γ ⊢ M ∶ A → valid Δ → σ ∶ Γ ⇒ Δ → Δ ⊢ M ⟦ σ ⟧ ∶ A ⟦ σ ⟧

postulate comp₁-typed : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                      ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒ Δ → ρ •₁ σ ∶ Γ ⇒ Θ

postulate Sub↑-typed : ∀ {U} {V} {K} {σ : Sub U V} {Γ} {Δ} {A} →
                     σ ∶ Γ ⇒ Δ → Sub↑ K σ ∶ Γ , A ⇒ Δ , A ⟦ σ ⟧
