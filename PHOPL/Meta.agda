module PHOPL.Meta where
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Rules

postulate β-respects-rep : respects' replacement

postulate β-respects-sub : respects' substitution

postulate Context-Validity : ∀ {V} {Γ} {K} {M : Expression V (varKind K)} {A} →
                           Γ ⊢ M ∶ A → valid Γ

postulate Prop-Validity : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} → 
                        Γ ⊢ δ ∶ φ → Γ ⊢ φ ∶ ty Ω

postulate _∶_⇒R_ : ∀ {U} {V} → Rep U V → Context U → Context V → Set

postulate change-codR : ∀ {U} {V} {ρ : Rep U V} {Γ : Context U} {Δ Δ' : Context V} →
                      ρ ∶ Γ ⇒R Δ → Δ ≡ Δ' → ρ ∶ Γ ⇒R Δ'

postulate idRep-typed : ∀ {V} {Γ : Context V} → idRep V ∶ Γ ⇒R Γ

postulate upRep-typed : ∀ {V} {Γ : Context V} {K} {A} → upRep ∶ Γ ⇒R _,_ {K = K} Γ A

postulate Rep↑-typed : ∀ {U} {V} {ρ : Rep U V} {K} {Γ} {Δ} {A} →
                     ρ ∶ Γ ⇒R Δ → Rep↑ K ρ ∶ (Γ , A) ⇒R (Δ , A 〈 ρ 〉)

postulate compR-typed : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Rep U V} {Γ} {Δ} {Θ : Context W} →
                        ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒R Δ → ρ •R σ ∶ Γ ⇒R Θ

postulate Weakening : ∀ {U} {V} {ρ : Rep U V} {K}
                    {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
                    Γ ⊢ M ∶ A → valid Δ → ρ ∶ Γ ⇒R Δ → Δ ⊢ M 〈 ρ 〉 ∶ A 〈 ρ 〉

postulate _∶_⇒_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set

postulate Substitution : ∀ {U} {V} {σ : Sub U V} {K}
                       {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
                       Γ ⊢ M ∶ A → valid Δ → σ ∶ Γ ⇒ Δ → Δ ⊢ M ⟦ σ ⟧ ∶ A ⟦ σ ⟧

postulate comp-typed : ∀ {U} {V} {W} {σ : Sub V W} {ρ : Sub U V} {Γ} {Δ} {Θ} →
                         σ ∶ Δ ⇒ Θ → ρ ∶ Γ ⇒ Δ → σ • ρ ∶ Γ ⇒ Θ

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

extendSub : ∀ {U} {V} → Sub U V → Term V → Sub (U , -Term) V
extendSub σ M _ x₀ = M
extendSub σ M _ (↑ x) = σ _ x

postulate ⊃-gen₁ : ∀ {V} {Γ : Context V} {φ} {ψ} → Γ ⊢ φ ⊃ ψ ∶ ty Ω → Γ ⊢ φ ∶ ty Ω

postulate ⊃-gen₂ : ∀ {V} {Γ : Context V} {φ} {ψ} → Γ ⊢ φ ⊃ ψ ∶ ty Ω → Γ ⊢ ψ ∶ ty Ω

postulate Type-Reduction : ∀ {V} {Γ : Context V} {K} {M : Expression V (varKind K)} {A} {B} →
                         Γ ⊢ M ∶ A → A ↠ B → Γ ⊢ M ∶ B

postulate change-cod : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} → σ ∶ Γ ⇒ Δ → Δ ≡ Δ' → σ ∶ Γ ⇒ Δ'

sub↖ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (V , -Term , -Term , -Path)
sub↖ σ _ x₀ = var x₂
sub↖ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

postulate sub↖-typed : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {A} → σ ∶ Γ ⇒ Δ → sub↖ σ ∶ Γ ,T A ⇒ Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀

postulate β↖ : ∀ {U} {V} {A} (M : Term (U , -Term)) {σ : Sub U V} → β -appTerm ((ΛT A M) ⟦ σ ⟧ ⇑ ⇑ ⇑ ,, var x₂ ,, out) (M ⟦ sub↖ σ ⟧)

sub↗ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (V , -Term , -Term , -Path)
sub↗ σ _ x₀ = var x₁
sub↗ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

postulate sub↗-typed : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {A} → σ ∶ Γ ⇒ Δ → sub↗ σ ∶ Γ ,T A ⇒ Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀

postulate β↗ : ∀ {U} {V} {A} (M : Term (U , -Term)) {σ : Sub U V} → β -appTerm ((ΛT A M) ⟦ σ ⟧ ⇑ ⇑ ⇑ ,, var x₁ ,, out) (M ⟦ sub↗ σ ⟧)

--REFACTOR Duplication

postulate sub↖-comp₁ : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
                     sub↖ (ρ •₁ σ) ∼ Rep↑ -Path (Rep↑ -Term (Rep↑ -Term ρ)) •₁ sub↖ σ

postulate sub↗-comp₁ : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
                     sub↗ (ρ •₁ σ) ∼ Rep↑ -Path (Rep↑ -Term (Rep↑ -Term ρ)) •₁ sub↗ σ

