\begin{code}
module PHOPL.MainPropFinal where
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
open import PHOPL.KeyRedex

Computable-Substitution : ∀ U V (σ : Sub U V) Γ Δ M A {A'} → 
                                  σ ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A' → A' ≡ ty A → valid Δ → E Δ A (M ⟦ σ ⟧)
Computable-Substitution _ V σ _ Δ _ A σ∶Γ⇒Δ (varR x _) A'≡A _ = subst (λ a → E' Δ a _) (sub-congl A'≡A) (σ∶Γ⇒Δ x)
Computable-Substitution _ V _ _ Δ .⊥ _ _ (⊥R _) A'≡A validΔ = subst (λ a → E Δ a _) (cong yt A'≡A) (E'I (⊥R validΔ) SN⊥)
Computable-Substitution U V σ Γ Δ .(φ ⊃ ψ) _ σ∶Γ⇒Δ (⊃R {φ = φ} {ψ} Γ⊢φ∶Ω Γ⊢ψ∶Ω) A'≡A validΔ = subst (λ x → E Δ x _) (cong yt A'≡A) (⊃-E 
  (Computable-Substitution U V σ Γ Δ φ Ω σ∶Γ⇒Δ Γ⊢φ∶Ω refl validΔ) 
  (Computable-Substitution U V σ Γ Δ ψ Ω σ∶Γ⇒Δ Γ⊢ψ∶Ω refl validΔ))
Computable-Substitution U V σ Γ Δ .(appT M N) _ σ∶Γ⇒Δ (appR {M = M} {N} {A} {B} Γ⊢M∶A⇒B Γ⊢N∶A) A'≡A validΔ = subst (λ x → E Δ x _) (cong yt A'≡A) (appT-E 
  validΔ
  (Computable-Substitution U V σ Γ Δ M (A ⇛ B) σ∶Γ⇒Δ Γ⊢M∶A⇒B refl validΔ) 
  (Computable-Substitution U V σ Γ Δ N A σ∶Γ⇒Δ Γ⊢N∶A refl validΔ))
Computable-Substitution U V σ Γ Δ .(ΛT A M) _ σ∶Γ⇒Δ (ΛR {A = A} {M} {B} Γ,A⊢M∶B) A'≡A validΔ = subst (λ x → E Δ x _) (cong yt A'≡A) (func-E (λ W Θ ρ N validθ ρ∶Δ⇒RΘ N∈EΘA → 
  expand-E ((subst (E Θ B)
  (let open ≡-Reasoning in 
  begin
    M ⟦ x₀:= N •SR Rep↑ -Term ρ • Sub↑ -Term σ ⟧
  ≡⟨ sub-comp M ⟩ 
    M ⟦ Sub↑ -Term σ ⟧ ⟦ x₀:= N •SR Rep↑ -Term ρ ⟧
  ≡⟨ sub-compSR (M ⟦ Sub↑ -Term σ ⟧) ⟩
    M ⟦ Sub↑ -Term σ ⟧ 〈 Rep↑ -Term ρ 〉 ⟦ x₀:= N ⟧
  ∎) (Computable-Substitution (U , -Term) W
        (x₀:= N •SR Rep↑ -Term ρ • Sub↑ -Term σ) (Γ ,T A) Θ M B
        (compC (compSRC (botsubC N∈EΘA) (Rep↑-typed ρ∶Δ⇒RΘ)) (Sub↑C σ∶Γ⇒Δ))
        Γ,A⊢M∶B refl validθ))) 
  (appR (ΛR (Weakening (Substitution Γ,A⊢M∶B (ctxTR validΔ) 
                       (Sub↑-typed (subC-typed σ∶Γ⇒Δ))) (ctxTR validθ) (Rep↑-typed ρ∶Δ⇒RΘ))) 
            (E-typed N∈EΘA))
  (βTkr (SNrep R-creates-rep (E-SN B 
    (Computable-Substitution (U , -Term) (V , -Term) (Sub↑ -Term σ)
       (Γ ,T A) (Δ ,T A) M B (Sub↑C σ∶Γ⇒Δ) Γ,A⊢M∶B refl (ctxTR validΔ)))))))

botsub-comp-upRep : ∀ {U} {V} {K} {L} {σ : Sub U V} (E : Expression U L) {M} → E ⇑ ⟦ x₀:= M • Sub↑ K σ ⟧ ≡ E ⟦ σ ⟧
botsub-comp-upRep {U} {V} {K} {L} {σ} E {M} = let open ≡-Reasoning in 
  begin
    E ⇑ ⟦ x₀:= M • Sub↑ K σ ⟧
  ≡⟨ sub-comp (E ⇑) ⟩
    E ⇑ ⟦ Sub↑ K σ ⟧ ⟦ x₀:= M ⟧
  ≡⟨ sub-congl (Sub↑-upRep E) ⟩
    E ⟦ σ ⟧ ⇑ ⟦ x₀:= M ⟧
  ≡⟨ botsub-upRep _ ⟩
    E ⟦ σ ⟧
  ∎

subrepsublemma : ∀ {U} {V} {W} {D} (E : Expression U D) {A B C : VarKind} {σ : Sub U V} {ρ : Rep V W} {F : Expression W (varKind C)} →
  E ⇑ ⇑ ⇑ ⟦ Sub↑ A (Sub↑ B (Sub↑ C σ)) ⟧ 〈 Rep↑ A (Rep↑ B (Rep↑ C ρ)) 〉 ⟦ Sub↑ A (Sub↑ B (x₀:= F)) ⟧ ≡ E ⇑ ⇑ ⟦ Sub↑ A (Sub↑ B σ) ⟧ 〈 Rep↑ A (Rep↑ B ρ) 〉
subrepsublemma {U} {V} {W} {D} E {A} {B} {C} {σ} {ρ} {F} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ ⇑ ⟦ Sub↑ A (Sub↑ B (Sub↑ C σ)) ⟧ 〈 Rep↑ A (Rep↑ B (Rep↑ C ρ)) 〉 ⟦ Sub↑ A (Sub↑ B (x₀:= F)) ⟧ 
  ≡⟨ sub-congl (rep-congl (Sub↑-upRep₂ (E ⇑))) ⟩
    E ⇑ ⟦ Sub↑ C σ ⟧ ⇑ ⇑ 〈 Rep↑ A (Rep↑ B (Rep↑ C ρ)) 〉 ⟦ Sub↑ A (Sub↑ B (x₀:= F)) ⟧
  ≡⟨ sub-congl (rep-congl (rep-congl (rep-congl (Sub↑-upRep E)))) ⟩
    E ⟦ σ ⟧ ⇑ ⇑ ⇑ 〈 Rep↑ A (Rep↑ B (Rep↑ C ρ)) 〉 ⟦ Sub↑ A (Sub↑ B (x₀:= F)) ⟧
  ≡⟨ sub-congl (Rep↑-upRep₂ (E ⟦ σ ⟧ ⇑)) ⟩
    E ⟦ σ ⟧ ⇑ 〈 Rep↑ C ρ 〉 ⇑ ⇑ ⟦ Sub↑ A (Sub↑ B (x₀:= F)) ⟧
  ≡⟨ sub-congl (rep-congl (rep-congl (Rep↑-upRep (E ⟦ σ ⟧)))) ⟩
    E ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ Sub↑ A (Sub↑ B (x₀:= F)) ⟧
  ≡⟨ Sub↑-upRep₂ (E ⟦ σ ⟧ 〈 ρ 〉 ⇑) ⟩
    E ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⟦ x₀:= F ⟧ ⇑ ⇑
  ≡⟨ rep-congl (rep-congl (botsub-upRep (E ⟦ σ ⟧ 〈 ρ 〉))) ⟩
    E ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑
  ≡⟨⟨ Rep↑-upRep₂ (E ⟦ σ ⟧) ⟩⟩
    E ⟦ σ ⟧  ⇑ ⇑ 〈 Rep↑ A (Rep↑ B ρ) 〉
  ≡⟨⟨ rep-congl (Sub↑-upRep₂ E) ⟩⟩
    E ⇑ ⇑ ⟦ Sub↑ A (Sub↑ B σ) ⟧ 〈 Rep↑ A (Rep↑ B ρ) 〉
  ∎

postulate Context-Validity-Prop : ∀ {V} {Γ : Context V} {φ} → valid (Γ ,P φ) → Γ ⊢ φ ∶ ty Ω

aux-lm1 : ∀ U V (σ : Sub U V) Γ Δ φ δ ψ →
  (∀ W Θ (τ : Sub (U , -Proof) W) → τ ∶ Γ ,P φ ⇒C Θ → valid Θ → EP Θ (ψ ⇑ ⟦ τ ⟧) (δ ⟦ τ ⟧)) →
  σ ∶ Γ ⇒C Δ → Γ ,P φ ⊢ δ ∶ ψ ⇑ → valid Δ → EP Δ  (φ ⟦ σ ⟧ ⊃ ψ ⟦ σ ⟧) (ΛP (φ ⟦ σ ⟧) (δ ⟦ Sub↑ -Proof σ ⟧))
aux-lm1 U V σ Γ Δ φ δ ψ ih σ∶Γ⇒CΔ Γ,φ⊢δ∶ψ validΔ = func-EP (λ W Θ ρ ε ρ∶Δ⇒RΘ ε∈EΘφσρ → 
  let EPδ : EP Θ (ψ ⟦ σ ⟧ 〈 ρ 〉) (δ ⟦ Sub↑ -Proof σ ⟧ 〈 Rep↑ -Proof ρ 〉 ⟦ x₀:= ε ⟧)
      EPδ = subst₂ (EP Θ) 
        (let open ≡-Reasoning in 
        begin
          ψ ⇑ ⟦ x₀:= ε •SR Rep↑ -Proof ρ • Sub↑ -Proof σ ⟧
        ≡⟨ sub-comp (ψ ⇑) ⟩
          ψ ⇑ ⟦ Sub↑ -Proof σ ⟧ ⟦ x₀:= ε •SR Rep↑ -Proof ρ ⟧
        ≡⟨ sub-compSR (ψ ⇑ ⟦ Sub↑ -Proof σ ⟧) ⟩
          ψ ⇑ ⟦ Sub↑ -Proof σ ⟧ 〈 Rep↑ -Proof ρ 〉 ⟦ x₀:= ε ⟧
        ≡⟨ cong (λ x → (x 〈 Rep↑ -Proof ρ 〉) ⟦ x₀:= ε ⟧) (Sub↑-upRep ψ) ⟩
          ψ ⟦ σ ⟧ ⇑ 〈 Rep↑ -Proof ρ 〉 ⟦ x₀:= ε ⟧
        ≡⟨ sub-congl (Rep↑-upRep (ψ ⟦ σ ⟧)) ⟩
          ψ ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⟦ x₀:= ε ⟧
        ≡⟨ botsub-upRep _ ⟩
          ψ ⟦ σ ⟧ 〈 ρ 〉
        ∎)
       (let open ≡-Reasoning in 
         begin
           δ ⟦ x₀:= ε •SR Rep↑ -Proof ρ • Sub↑ -Proof σ ⟧
         ≡⟨ sub-comp δ ⟩
           δ ⟦ Sub↑ -Proof σ ⟧ ⟦ x₀:= ε •SR Rep↑ -Proof ρ ⟧
         ≡⟨ sub-compSR (δ ⟦ Sub↑ -Proof σ ⟧) ⟩
           δ ⟦ Sub↑ -Proof σ ⟧ 〈 Rep↑ -Proof ρ 〉 ⟦ x₀:= ε ⟧
         ∎) 
        (ih W Θ (x₀:= ε •SR Rep↑ -Proof ρ • Sub↑ -Proof σ) (compC (compSRC (botsubCP ε∈EΘφσρ) (Rep↑-typed ρ∶Δ⇒RΘ)) (Sub↑C σ∶Γ⇒CΔ)) (Context-Validity (EP-typed ε∈EΘφσρ)))
 in
  expand-EP EPδ
    (appPR (ΛPR (Weakening (Substitution (Context-Validity-Prop (Context-Validity Γ,φ⊢δ∶ψ)) validΔ (subC-typed σ∶Γ⇒CΔ)) (Context-Validity (EP-typed ε∈EΘφσρ)) 
                ρ∶Δ⇒RΘ) 
           (subst₂ (λ M A → (Θ ,P ((φ ⟦ σ ⟧) 〈 ρ 〉)) ⊢ M ∶ A) 
      (sub-compRS δ)
      (let open ≡-Reasoning in 
      begin
        ψ ⇑ ⟦ Rep↑ -Proof ρ •RS Sub↑ -Proof σ ⟧
      ≡⟨ sub-compRS (ψ ⇑) ⟩
        ψ ⇑ ⟦ Sub↑ -Proof σ ⟧ 〈 Rep↑ -Proof ρ 〉
      ≡⟨ rep-congl (Sub↑-upRep ψ) ⟩
        ψ ⟦ σ ⟧ ⇑ 〈 Rep↑ -Proof ρ 〉
      ≡⟨ Rep↑-upRep (ψ ⟦ σ ⟧) ⟩
        ψ ⟦ σ ⟧ 〈 ρ 〉 ⇑
      ∎) 
      (Substitution Γ,φ⊢δ∶ψ (ctxPR (Prop-Validity (EP-typed ε∈EΘφσρ))) 
        (compRS-typed (Rep↑-typed ρ∶Δ⇒RΘ) (Sub↑-typed (subC-typed σ∶Γ⇒CΔ)))))) 
    (EP-typed ε∈EΘφσρ)) 
    (βPkr (E-SN Ω (subst (E Θ Ω) (sub-compRS φ)
      (Computable-Substitution U W (ρ •RS σ) Γ Θ φ Ω (compRSC ρ∶Δ⇒RΘ σ∶Γ⇒CΔ) (Context-Validity-Prop (Context-Validity Γ,φ⊢δ∶ψ)) 
      refl (Context-Validity (EP-typed ε∈EΘφσρ))))) (EP-SN ε∈EΘφσρ)))
-- TODO Common pattern with Computable-Substitution
 (ΛPR (Substitution (Context-Validity-Prop (Context-Validity Γ,φ⊢δ∶ψ)) validΔ (subC-typed σ∶Γ⇒CΔ)) 
   (change-type (Substitution Γ,φ⊢δ∶ψ (ctxPR (Substitution Γ⊢φ∶Ω validΔ (subC-typed σ∶Γ⇒CΔ))) (Sub↑-typed (subC-typed σ∶Γ⇒CΔ))) (Sub↑-upRep ψ))) where
 Γ⊢φ∶Ω : Γ ⊢ φ ∶ ty Ω
 Γ⊢φ∶Ω with (Context-Validity Γ,φ⊢δ∶ψ)
 Γ⊢φ∶Ω | ctxPR p = p

aux-lm1-5 : ∀ {U} {V} {W} {K1} {K2} {K3} {K4} (M : Expression U K1) (N : Expression W (varKind K2)) (N' : Expression W (varKind K3)) (Q : Expression W (varKind K4)) 
  {ρ : Rep V W} {σ : Sub U V} →
  M ⇑ ⇑ ⇑ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •SR Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) • Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ ≡ M ⟦ σ ⟧ 〈 ρ 〉
aux-lm1-5 {U} {V} {W} {K1} {K2} {K3} {K4} M N N' Q {ρ} {σ} = let open ≡-Reasoning in
                  begin
                    M ⇑ ⇑ ⇑ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •SR Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) • Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧
                  ≡⟨ sub-comp (M ⇑ ⇑ ⇑) ⟩
                    M ⇑ ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •SR Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) ⟧
                  ≡⟨ sub-congl (Sub↑-upRep₃ M) ⟩
                    M ⟦ σ ⟧ ⇑ ⇑ ⇑ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •SR Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) ⟧
                  ≡⟨ sub-compSR (M ⟦ σ ⟧ ⇑ ⇑ ⇑) ⟩
                    M ⟦ σ ⟧ ⇑ ⇑ ⇑ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
                  ≡⟨ sub-congl (Rep↑-upRep₃ (M ⟦ σ ⟧)) ⟩
                    M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
                  ≡⟨ sub-comp (M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
                    M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₀:= (Q ⇑ ⇑) ⟧ ⟦ x₀:= N • x₀:= (N' ⇑) ⟧
                  ≡⟨ sub-congl (botsub-upRep (M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑)) ⟩
                    M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⟦ x₀:= N • x₀:= (N' ⇑) ⟧
                  ≡⟨ sub-comp (M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑) ⟩
                    M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⟦ x₀:= (N' ⇑) ⟧ ⟦ x₀:= N ⟧
                  ≡⟨ sub-congl (botsub-upRep (M ⟦ σ ⟧ 〈 ρ 〉 ⇑)) ⟩
                    M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⟦ x₀:= N ⟧
                  ≡⟨ botsub-upRep (M ⟦ σ ⟧ 〈 ρ 〉) ⟩
                    M ⟦ σ ⟧ 〈 ρ 〉
                  ∎

postulate botsub₂-decomp : ∀ {V} {K1} {K2} {K3} {N : Expression V (varKind K1)} {N' : Expression V (varKind K2)} {Q : Expression V (varKind K3)} →
                         (x₂:= N ,x₁:= N' ,x₀:= Q) ∼ (x₀:= N • x₀:= N' ⇑ • x₀:= Q ⇑ ⇑)

--REFACTOR Definition for Γ ,T A ,T A ,T x₁ ≡ x₀
aux-lm2 : ∀ (U V : Alphabet) (σ : Sub U V) (Γ : Context U) (Δ : Context V) (A : Type) B M M' P →
  σ ∶ Γ ⇒C Δ → 
  addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT (M' ⇑ ⇑ ⇑) (var x₁) →
  valid Δ →
  (∀ W (Θ : Context W) τ → τ ∶ addpath Γ A ⇒C Θ → valid Θ → 
    EE Θ ((appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT (M' ⇑ ⇑ ⇑) (var x₁)) ⟦ τ ⟧) (P ⟦ τ ⟧)) →
  EE Δ (M ⟦ σ ⟧ ≡〈 A ⇛ B 〉 M' ⟦ σ ⟧) ((λλλ A P) ⟦ σ ⟧)
aux-lm2 U V σ Γ Δ A B M M' P σ∶Γ⇒Δ Γ+⊢P∶Mx≡M'y validΔ hyp = 
  func-EE (lllR (change-type (Substitution Γ+⊢P∶Mx≡M'y (ctxER (varR (↑ x₀) (ctxTR (ctxTR validΔ))) (varR x₀ (ctxTR (ctxTR validΔ)))) 
    (Sub↑-typed (Sub↑-typed (Sub↑-typed (subC-typed σ∶Γ⇒Δ))))) 
    (cong₂ (λ a b → appT a (var x₂) ≡〈 B 〉 appT b (var x₁)) 
      (Sub↑-upRep₃ M) (Sub↑-upRep₃ M'))))
  (λ W Θ N N' Q ρ ρ∶Δ⇒Θ N∈EΘA N'∈EΘA Q∈EΘN≡N' → 
  let σ' = Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) in
  let ρ' = Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) in
  let ih : EE Θ (appT (M ⟦ σ ⟧ 〈 ρ 〉) N ≡〈 B 〉 appT (M' ⟦ σ ⟧ 〈 ρ 〉) N') (P ⟦ σ' ⟧ 〈 ρ' 〉 ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧)
      ih = subst₂ (EE Θ) 
                  (cong₃ (λ a b c → appT a N ≡〈 B 〉 appT b c)
                    (aux-lm1-5 M N N' Q)
                    (aux-lm1-5 M' N N' Q) 
                    (botsub-upRep N'))
                  (let open ≡-Reasoning in 
                  begin
                    P ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •SR ρ' • σ' ⟧
                  ≡⟨ sub-comp P ⟩
                    P ⟦ σ' ⟧ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •SR ρ' ⟧
                  ≡⟨ sub-compSR (P ⟦ σ' ⟧) ⟩
                    P ⟦ σ' ⟧ 〈 ρ' 〉 ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
                  ∎) 
                  (hyp W Θ (x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •SR ρ' • σ') 
                  (compC (compSRC {σ = x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑)} 
                    (subC-cong {σ = x₀:= Q • Sub↑ _ (x₀:= N') • Sub↑ _ (Sub↑ _ (x₀:= N))} 
                      (compC (compC (botsubCE 
                        (subst (λ a → EE Θ a Q) 
                          (cong (λ a → a ≡〈 A 〉 N')
                            (sym (botsub-upRep N)))
                          Q∈EΘN≡N')) 
                        (Sub↑C (botsubC N'∈EΘA))) 
                        (Sub↑C (Sub↑C (botsubC N∈EΘA)))) 
                      (aux Q N' N))
                    (Rep↑-typed (Rep↑-typed (Rep↑-typed ρ∶Δ⇒Θ)))) 
                    (Sub↑C (Sub↑C (Sub↑C σ∶Γ⇒Δ))))
                  (Context-Validity (E-typed N∈EΘA))) 
  in (expand-EE ih
       (let step1 : addpath Δ A ⊢
                  P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ ∶ appT (M ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT (M' ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₁)
            step1 = change-type (Substitution Γ+⊢P∶Mx≡M'y (ctxER (varR x₁ (ctxTR (ctxTR validΔ))) (varR x₀ (ctxTR (ctxTR validΔ))))
                    (Sub↑-typed (Sub↑-typed (Sub↑-typed (subC-typed σ∶Γ⇒Δ)))))
                    (cong₂ (λ a b → appT a (var x₂) ≡〈 B 〉 appT b (var x₁)) 
                      (Sub↑-upRep₃ M) (Sub↑-upRep₃ M')) 
       in app*R 
          (E-typed N∈EΘA) (E-typed N'∈EΘA) 
            (lllR 
              (change-type
                (Weakening (Substitution Γ+⊢P∶Mx≡M'y 
                                           (valid-addpath validΔ)
                                           (Sub↑-typed (Sub↑-typed (Sub↑-typed (subC-typed σ∶Γ⇒Δ))))) 
                             (valid-addpath (Context-Validity (E-typed N∈EΘA)))
                             (Rep↑-typed (Rep↑-typed (Rep↑-typed ρ∶Δ⇒Θ))))
                (cong₂ (λ a b → appT a (var x₂) ≡〈 B 〉 appT b (var x₁)) 
                  (Rep↑-Sub↑-upRep₃ M σ ρ) (Rep↑-Sub↑-upRep₃ M' σ ρ))))
            (EE-typed Q∈EΘN≡N')) 
     (subst (key-redex _) (sub-congr (P ⟦ Sub↑ -Path (Sub↑ -Term (Sub↑ -Term σ)) ⟧ 〈 Rep↑ -Path (Rep↑ -Term (Rep↑ -Term ρ)) 〉) 
                          botsub₂-decomp) (βEkr (E-SN A N∈EΘA) (E-SN A N'∈EΘA) (EE-SN (N ≡〈 A 〉 N') Q∈EΘN≡N')))))
         where
                  aux : ∀ {V} (Q : Path V) N' (N : Term V) → (x₀:= Q • Sub↑ -Path (x₀:= N') •
                          Sub↑ -Path (Sub↑ -Term (x₀:= N)))
                            ∼ (x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑))
                  aux Q N' N x₀ = let open ≡-Reasoning in 
                    begin
                      Q
                    ≡⟨⟨ botsub-upRep Q ⟩⟩
                      Q ⇑ ⟦ x₀:= N ⟧
                    ≡⟨⟨ sub-congl (botsub-upRep (Q ⇑)) ⟩⟩
                      Q ⇑ ⇑ ⟦ x₀:= (N' ⇑) ⟧ ⟦ x₀:= N ⟧
                    ≡⟨⟨ sub-comp (Q ⇑ ⇑) ⟩⟩
                      Q ⇑ ⇑ ⟦ x₀:= N • x₀:= (N' ⇑) ⟧
                    ∎
                  aux Q N' N (↑ x₀) = let open ≡-Reasoning in 
                    begin
                      N' ⇑ ⟦ x₀:= Q ⟧
                    ≡⟨ botsub-upRep N' ⟩
                      N'
                    ≡⟨⟨ botsub-upRep N' ⟩⟩
                      N' ⇑ ⟦ x₀:= N ⟧
                    ∎
                  aux Q N' N (↑ (↑ x₀)) = let open ≡-Reasoning in 
                    begin
                      N ⇑ ⇑ ⟦ x₀:= Q • Sub↑ _ (x₀:= N') ⟧
                    ≡⟨ botsub-comp-upRep (N ⇑) ⟩
                      N ⇑ ⟦ x₀:= N' ⟧
                    ≡⟨ botsub-upRep N ⟩
                      N
                    ∎
                  aux Q N' N (↑ (↑ (↑ x))) = refl
\end{code}
