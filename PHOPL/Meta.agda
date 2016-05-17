module PHOPL.Meta where
open import Prelims
open import PHOPL
open import PHOPL.Rules

postulate β-respects-sub : respects' substitution

postulate Prop-Validity : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} → 
                        Γ ⊢ δ ∶ φ → Γ ⊢ φ ∶ Ω

postulate _∶_⇒R_ : ∀ {U} {V} → Rep U V → Context U → Context V → Set

postulate change-codR : ∀ {U} {V} {ρ : Rep U V} {Γ : Context U} {Δ Δ' : Context V} →
                      ρ ∶ Γ ⇒R Δ → Δ ≡ Δ' → ρ ∶ Γ ⇒R Δ'

postulate upRep-typed : ∀ {V} {Γ : Context V} {K} {A} → upRep ∶ Γ ⇒R _,_ {K = K} Γ A

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

postulate change-type : ∀ {V} {Γ} {K} {M : Expression V (varKind K)} {A} {B} →
                      Γ ⊢ M ∶ A → A ≡ B → Γ ⊢ M ∶ B

postulate botsub-typed : ∀ {V} {K} {Γ} {E : Expression V (varKind K)} {A} → Γ ⊢ E ∶ A → x₀:= E ∶ Γ , A ⇒ Γ

lemma : ∀ {U} {V} {W} {K} (M : Expression U K) Q N' N (ρ : Rep V W) (σ : Sub U V) → M ⇑ ⇑ ⇑ ⟦ x₀:= Q • Sub↑ -Path (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ))) ⟧ ≡ M ⟦ σ ⟧ 〈 ρ 〉 --TODO Rename
lemma {U} {V} {W} M Q N' N ρ σ = let open ≡-Reasoning in 
          begin
            M ⇑ ⇑ ⇑ ⟦ x₀:= Q • Sub↑ -Path (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ))) ⟧
          ≡⟨ sub-comp (M ⇑ ⇑ ⇑) ⟩
            M ⇑ ⇑ ⇑ ⟦ Sub↑ -Path (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ))) ⟧ ⟦ x₀:= Q ⟧
          ≡⟨ sub-congl (Sub↑-upRep (M ⇑ ⇑)) ⟩
            M ⇑ ⇑ ⟦ x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ)) ⟧ ⇑ ⟦ x₀:= Q ⟧
          ≡⟨ botsub-upRep _ ⟩
            M ⇑ ⇑ ⟦ x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ)) ⟧
          ≡⟨ sub-comp (M ⇑ ⇑) ⟩
            M ⇑ ⇑ ⟦ Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ)) ⟧ ⟦ x₀:= N' ⟧
          ≡⟨ sub-congl (Sub↑-upRep (M ⇑)) ⟩
            M ⇑ ⟦ x₀:= N • Sub↑ -Term (ρ •₁ σ) ⟧ ⇑ ⟦ x₀:= N' ⟧
          ≡⟨ botsub-upRep _ ⟩
            M ⇑ ⟦ x₀:= N • Sub↑ -Term (ρ •₁ σ) ⟧
          ≡⟨ sub-comp (M ⇑) ⟩
            M ⇑ ⟦ Sub↑ -Term (ρ •₁ σ) ⟧ ⟦ x₀:= N ⟧
          ≡⟨ sub-congl (Sub↑-upRep M) ⟩
            M ⟦ ρ •₁ σ ⟧ ⇑ ⟦ x₀:= N ⟧
          ≡⟨ botsub-upRep _ ⟩
            M ⟦ ρ •₁ σ ⟧
          ≡⟨ sub-comp₁ M ⟩
            M ⟦ σ ⟧ 〈 ρ 〉
          ∎

postulate change-cod' : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} → σ ∶ Γ ⇒ Δ → Δ ≡ Δ' → σ ∶ Γ ⇒ Δ'
