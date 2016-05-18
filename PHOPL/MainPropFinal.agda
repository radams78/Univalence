module PHOPL.MainPropFinal where
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import Prelims
open import PHOPL
open import PHOPL.Rules
open import PHOPL.PathSub
open import PHOPL.Close
open import PHOPL.Red
open import PHOPL.Neutral
open import PHOPL.Meta
open import PHOPL.Computable
open import PHOPL.SubC
open import PHOPL.SN

Eclose-lm : ∀ {U} {V} {W} (Θ : Context U) (A : Type V) N (ρ : Rep V W)
  → E Θ (close A) N → E Θ (close (A 〈 ρ 〉)) N
Eclose-lm Θ A N ρ = subst (λ x → E Θ x N) (sym (close-rep A))

Sub↑-lm₁ : ∀ {U} {V} {K} (σ : Sub U V) (Γ : Context U) (A : Expression U (parent K)) (Δ : Context V) B → 
  σ ∶ Γ ⇒C Δ → A ⟦ σ ⟧ ≡ B → Sub↑ K σ ∶ Γ , A ⇒C Δ , B
Sub↑-lm₁ {U} {V} σ Γ A Δ B σ∶Γ⇒CΔ Aσ≡B = change-cod (Sub↑C σ∶Γ⇒CΔ) (cong (λ x → Δ , x) Aσ≡B)

Sub↑-lm : ∀ {U} {V} {W} {L} (σ : Sub U (V , -Term)) (ρ : Rep W V) Γ Δ N A B C → σ ∶ Γ ⇒C Δ , A 〈 ρ 〉 → E Δ (close A) N → B ⟦ x₀:= N • σ ⟧ ≡ C → 
  Sub↑ L (x₀:= N • σ) ∶ _,_ {K = L} Γ B ⇒C Δ , C
Sub↑-lm {U} {V} {L} σ ρ Γ Δ N A B C σ∶Γ⇒Δ,A N∈EΔA = Sub↑-lm₁ {U} {V} (x₀:= N • σ) Γ B Δ C 
  (compC (botsubC (Eclose-lm Δ A N ρ N∈EΔA)) σ∶Γ⇒Δ,A)

Computable-Substitution : ∀ U V (σ : Sub U V) Γ Δ M A → 
  σ ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → E Δ (close A) (M ⟦ σ ⟧)
Computable-Substitution _ _ _ _ _ _ _ σ∶Γ⇒Δ (varR x _) _ = proj₁ σ∶Γ⇒Δ x
Computable-Substitution _ V _ _ Δ .⊥ .Ω _ (⊥R _) Δvalid = ⊥-E {V} {Δ} Δvalid
Computable-Substitution U V σ Γ Δ .(φ ⊃ ψ) .Ω σ∶Γ⇒Δ (impR {φ = φ} {ψ} Γ⊢φ∶Ω Γ⊢ψ∶Ω) Δvalid = ⊃-E 
  (Computable-Substitution U V σ Γ Δ φ Ω σ∶Γ⇒Δ Γ⊢φ∶Ω Δvalid) 
  (Computable-Substitution U V σ Γ Δ ψ Ω σ∶Γ⇒Δ Γ⊢ψ∶Ω Δvalid)
Computable-Substitution U V σ Γ Δ .(appT M N) .B σ∶Γ⇒Δ (appR {M = M} {N} {A} {B} Γ⊢M∶A⇒B Γ⊢N∶A) Δvalid = appT-E 
  Δvalid
  (Computable-Substitution U V σ Γ Δ M (A ⇛ B) σ∶Γ⇒Δ Γ⊢M∶A⇒B Δvalid) 
  (Computable-Substitution U V σ Γ Δ N A σ∶Γ⇒Δ Γ⊢N∶A Δvalid)
Computable-Substitution U V σ Γ Δ .(ΛT A M) .(A ⇛ B) σ∶Γ⇒Δ (ΛR {A = A} {M} {B} Γ,A⊢M∶B) Δvalid = func-E (λ W Θ ρ N Θvalid ρ∶Δ⇒RΘ N∈EΘA → 
  expand-E (subst₂ (E Θ) (close-rep B) 
  (let open ≡-Reasoning in 
  begin
    M ⟦ x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ ⟧
  ≡⟨ sub-comp M ⟩ 
    M ⟦ Sub↑ -Term σ ⟧ ⟦ x₀:= N •₂ Rep↑ -Term ρ ⟧
  ≡⟨ sub-comp₂ (M ⟦ Sub↑ -Term σ ⟧) ⟩
    M ⟦ Sub↑ -Term σ ⟧ 〈 Rep↑ -Term ρ 〉 ⟦ x₀:= N ⟧
  ∎) 
  (Computable-Substitution (U , -Term) W 
    (x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ) (Γ ,T A) Θ M (B ⇑) 
    (compC (comp₂C (botsubC (subst (λ T → E Θ T N) 
      (let open ≡-Reasoning in 
      begin
        close A
      ≡⟨⟨ close-sub A ⟩⟩
        close (A ⟦ σ ⟧)
      ≡⟨⟨ close-rep (A ⟦ σ ⟧) ⟩⟩
        close (A ⟦ σ ⟧ 〈 ρ 〉)
      ∎) 
      N∈EΘA)) (Rep↑-typed ρ∶Δ⇒RΘ)) (Sub↑C σ∶Γ⇒Δ)) Γ,A⊢M∶B Θvalid)))

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

aux-lm1 : ∀ U V (σ : Sub U V) Γ Δ φ δ ψ →
  (∀ W Θ (τ : Sub (U , -Proof) W) → τ ∶ Γ ,P φ ⇒C Θ → valid Θ → EP Θ (ψ ⇑ ⟦ τ ⟧) (δ ⟦ τ ⟧)) →
  σ ∶ Γ ⇒C Δ → Γ ,P φ ⊢ δ ∶ ψ ⇑ → valid Δ → EP Δ  (φ ⟦ σ ⟧ ⊃ ψ ⟦ σ ⟧) (ΛP (φ ⟦ σ ⟧) (δ ⟦ Sub↑ -Proof σ ⟧))
aux-lm1 U V σ Γ Δ φ δ ψ ih σ∶Γ⇒CΔ Γ,φ⊢δ∶ψ validΔ = func-EP (λ W Θ ρ ε validΘ ρ∶Δ⇒RΘ ε∈EΘφσρ → 
  let EPδ : EP Θ (ψ ⟦ σ ⟧ 〈 ρ 〉) (δ ⟦ Sub↑ -Proof σ ⟧ 〈 Rep↑ -Proof ρ 〉 ⟦ x₀:= ε ⟧)
      EPδ = subst₂ (EP Θ) 
        (let open ≡-Reasoning in 
        begin
          ψ ⇑ ⟦ x₀:= ε •₂ Rep↑ -Proof ρ • Sub↑ -Proof σ ⟧
        ≡⟨ sub-comp (ψ ⇑) ⟩
          ψ ⇑ ⟦ Sub↑ -Proof σ ⟧ ⟦ x₀:= ε •₂ Rep↑ -Proof ρ ⟧
        ≡⟨ sub-comp₂ (ψ ⇑ ⟦ Sub↑ -Proof σ ⟧) ⟩
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
           δ ⟦ x₀:= ε •₂ Rep↑ -Proof ρ • Sub↑ -Proof σ ⟧
         ≡⟨ sub-comp δ ⟩
           δ ⟦ Sub↑ -Proof σ ⟧ ⟦ x₀:= ε •₂ Rep↑ -Proof ρ ⟧
         ≡⟨ sub-comp₂ (δ ⟦ Sub↑ -Proof σ ⟧) ⟩
           δ ⟦ Sub↑ -Proof σ ⟧ 〈 Rep↑ -Proof ρ 〉 ⟦ x₀:= ε ⟧
         ∎) 
        (ih W Θ (x₀:= ε •₂ Rep↑ -Proof ρ • Sub↑ -Proof σ) (compC (comp₂C (botsubCP ε∈EΘφσρ) (Rep↑-typed ρ∶Δ⇒RΘ)) (Sub↑C σ∶Γ⇒CΔ)) validΘ)
 in
  expand-EP EPδ
    (appPR (ΛPR (subst₂ (λ M A → (Θ ,P ((φ ⟦ σ ⟧) 〈 ρ 〉)) ⊢ M ∶ A) 
      (sub-comp₁ δ)
      (let open ≡-Reasoning in 
      begin
        ψ ⇑ ⟦ Rep↑ -Proof ρ •₁ Sub↑ -Proof σ ⟧
      ≡⟨ sub-comp₁ (ψ ⇑) ⟩
        ψ ⇑ ⟦ Sub↑ -Proof σ ⟧ 〈 Rep↑ -Proof ρ 〉
      ≡⟨ rep-congl (Sub↑-upRep ψ) ⟩
        ψ ⟦ σ ⟧ ⇑ 〈 Rep↑ -Proof ρ 〉
      ≡⟨ Rep↑-upRep (ψ ⟦ σ ⟧) ⟩
        ψ ⟦ σ ⟧ 〈 ρ 〉 ⇑
      ∎) 
      (Substitution Γ,φ⊢δ∶ψ (ctxPR (Prop-Validity (EP-typed ε∈EΘφσρ))) 
        (comp₁-typed (Rep↑-typed ρ∶Δ⇒RΘ) (Sub↑-typed (subC-typed σ∶Γ⇒CΔ)))))) 
    (EP-typed ε∈EΘφσρ)) 
    (redexR βR) 
    (SN-βexp (EP-SN ε∈EΘφσρ) (EP-SN EPδ))) -- TODO Common pattern with Computable-Substitution
 (ΛPR (change-type (Substitution Γ,φ⊢δ∶ψ (ctxPR (Substitution Γ⊢φ∶Ω validΔ (subC-typed σ∶Γ⇒CΔ))) (Sub↑-typed (subC-typed σ∶Γ⇒CΔ))) (Sub↑-upRep ψ))) where
 Γ⊢φ∶Ω : Γ ⊢ φ ∶ Ω
 Γ⊢φ∶Ω with (Context-Validity Γ,φ⊢δ∶ψ)
 Γ⊢φ∶Ω | ctxPR p = p

aux-lm1-5 : ∀ {U} {V} {W} {K1} {K2} {K3} {K4} (M : Expression U K1) (N : Expression W (varKind K2)) (N' : Expression W (varKind K3)) (Q : Expression W (varKind K4)) 
  {ρ : Rep V W} {σ : Sub U V} →
  M ⇑ ⇑ ⇑ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •₂ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) • Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ ≡ M ⟦ σ ⟧ 〈 ρ 〉
aux-lm1-5 {U} {V} {W} {K1} {K2} {K3} {K4} M N N' Q {ρ} {σ} = let open ≡-Reasoning in
                  begin
                    M ⇑ ⇑ ⇑ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •₂ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) • Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧
                  ≡⟨ sub-comp (M ⇑ ⇑ ⇑) ⟩
                    M ⇑ ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •₂ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) ⟧
                  ≡⟨ sub-congl (Sub↑-upRep₃ M) ⟩
                    M ⟦ σ ⟧ ⇑ ⇑ ⇑ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •₂ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) ⟧
                  ≡⟨ sub-comp₂ (M ⟦ σ ⟧ ⇑ ⇑ ⇑) ⟩
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

aux-lm2 : ∀ (U V : Alphabet) (σ : Sub U V) (Γ : Context U) (Δ : Context V) (A : Type U) B M M' P →
  σ ∶ Γ ⇒C Δ → 
  Γ , A , A ⇑ , var x₁ ≡〈 A ⇑ ⇑ 〉 var x₀ ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 B ⇑ ⇑ ⇑  〉 appT (M' ⇑ ⇑ ⇑) (var x₁) →
  valid Δ →
  (∀ W (Θ : Context W) τ → τ ∶ Γ , A , A ⇑ , var x₁ ≡〈 A ⇑ ⇑ 〉 var x₀ ⇒C Θ → valid Θ → 
    EE Θ ((appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 B ⇑ ⇑ ⇑  〉 appT (M' ⇑ ⇑ ⇑) (var x₁)) ⟦ τ ⟧) (P ⟦ τ ⟧)) →
  EE Δ (M ⟦ σ ⟧ ≡〈 (A ⟦ σ ⟧) ⇛ (B ⟦ σ ⟧) 〉 M' ⟦ σ ⟧) ((λλλ A P) ⟦ σ ⟧)
aux-lm2 U V σ Γ Δ A B M M' P σ∶Γ⇒Δ Γ+⊢P∶Mx≡M'y validΔ hyp = func-EE (λ W Θ N N' Q ρ ρ∶Δ⇒Θ validΘ N∈EΘA N'∈EΘA Q∈EΘN≡N' → 
  let σ' = Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) in
  let ρ' = Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) in
  let ih : EE Θ (appT (M ⟦ σ ⟧ 〈 ρ 〉) N ≡〈 B ⟦ σ ⟧ 〈 ρ 〉 〉 appT (M' ⟦ σ ⟧ 〈 ρ 〉) N') (P ⟦ σ' ⟧ 〈 ρ' 〉 ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧)
      ih = subst₂ (EE Θ) 
                  (cong₃ _≡〈_〉_ (cong (λ x → appT x N) (aux-lm1-5 M N N' Q))
                  (aux-lm1-5 B N N' Q) (cong₂ appT (aux-lm1-5 M' N N' Q) (botsub-upRep N'))) 
                  (let open ≡-Reasoning in 
                  begin
                    P ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •₂ ρ' • σ' ⟧
                  ≡⟨ sub-comp P ⟩
                    P ⟦ σ' ⟧ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •₂ ρ' ⟧
                  ≡⟨ sub-comp₂ (P ⟦ σ' ⟧) ⟩
                    P ⟦ σ' ⟧ 〈 ρ' 〉 ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
                  ∎) 
                  (hyp W Θ (x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) •₂ ρ' • σ') 
                  (compC (comp₂C {σ = x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑)} 
                    (subC-cong {σ = x₀:= Q • Sub↑ _ (x₀:= N') • Sub↑ _ (Sub↑ _ (x₀:= N))} 
                      (compC (compC (botsubCE 
                        (subst (λ a → EE Θ a Q) 
                          (cong₃ _≡〈_〉_ 
                            (sym (botsub-upRep N))
                            (let open ≡-Reasoning in 
                            begin
                              A ⟦ σ ⟧ 〈 ρ 〉
                            ≡⟨⟨ botsub-upRep (A ⟦ σ ⟧ 〈 ρ 〉) ⟩⟩
                             A ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⟦ x₀:= N ⟧
                            ≡⟨⟨ botsub-upRep _ ⟩⟩
                              A ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⟦ x₀:= N ⟧ ⇑ ⟦ x₀:= N' ⟧
                            ≡⟨⟨ sub-congl (Sub↑-upRep (A ⟦ σ ⟧ 〈 ρ 〉 ⇑)) ⟩⟩
                              A ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⟦ Sub↑ _ (x₀:= N) ⟧ ⟦ x₀:= N' ⟧
                            ≡⟨⟨ sub-congl (sub-congl (Rep↑-upRep₂ (A ⟦ σ ⟧))) ⟩⟩
                              A ⟦ σ ⟧ ⇑ ⇑ 〈 Rep↑ _ (Rep↑ _ ρ) 〉 ⟦ Sub↑ _ (x₀:= N) ⟧ ⟦ x₀:= N' ⟧
                            ≡⟨⟨ sub-congl (sub-congl (rep-congl (Sub↑-upRep₂ A))) ⟩⟩
                              A ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ σ) ⟧ 〈 Rep↑ _ (Rep↑ _ ρ) 〉 ⟦ Sub↑ _ (x₀:= N) ⟧ ⟦ x₀:= N' ⟧
                            ∎) 
                            refl) 
                          Q∈EΘN≡N')) 
                        (Sub↑C (botsubC 
                          (subst (λ a → E Θ a N') 
                          (let open ≡-Reasoning in 
                          begin
                            close (A ⟦ σ ⟧)
                          ≡⟨⟨ close-rep (A ⟦ σ ⟧) ⟩⟩
                            close (A ⟦ σ ⟧ 〈 ρ 〉)
                          ≡⟨⟨ cong close (botsub-upRep (A ⟦ σ ⟧ 〈 ρ 〉)) ⟩⟩
                            close (A ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⟦ x₀:= N ⟧)
                          ≡⟨⟨ cong close (sub-congl (Rep↑-upRep (A ⟦ σ ⟧))) ⟩⟩
                            close (A ⟦ σ ⟧ ⇑ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= N ⟧)
                          ≡⟨⟨ cong close (sub-congl (rep-congl (Sub↑-upRep A))) ⟩⟩
                            close (A ⇑ ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= N ⟧)
                          ∎) 
                          N'∈EΘA)))) 
                        (Sub↑C (Sub↑C (botsubC 
                          (subst (λ a → E Θ a N) (sym (close-rep (A ⟦ σ ⟧))) N∈EΘA))))) 
                      (aux Q N' N))
                    (Rep↑-typed (Rep↑-typed (Rep↑-typed ρ∶Δ⇒Θ)))) 
                    (Sub↑C (Sub↑C (Sub↑C σ∶Γ⇒Δ))))
                  validΘ) 
  in (expand-EE ih
       (let step3 : Δ , A ⟦ σ ⟧ , A ⟦ σ ⟧ ⇑ , var x₁ ≡〈 A ⟦ σ ⟧ ⇑ ⇑ 〉 var x₀ ⊢
                  P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ ∶ appT (M ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₂) ≡〈 B ⟦ σ ⟧ ⇑ ⇑ ⇑ 〉 appT (M' ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₁)
            step3 = change-type (Substitution Γ+⊢P∶Mx≡M'y (ctxER (varR x₁ (ctxTR (ctxTR validΔ))) (varR x₀ (ctxTR (ctxTR validΔ)))) 
                    (change-cod' (Sub↑-typed (Sub↑-typed (Sub↑-typed (subC-typed σ∶Γ⇒Δ)))) 
                      (cong₂ (λ a b → Δ ,T A ⟦ σ ⟧ ,T a ,E b) 
                        (Sub↑-upRep A) 
                        (cong (λ a → var x₁ ≡〈 a 〉 var x₀) (Sub↑-upRep₂ A))))) 
                        (cong₃ _≡〈_〉_ (cong₂ appT (Sub↑-upRep₃ M) refl) (Sub↑-upRep₃ B) (cong (λ a → appT a (var x₁)) (Sub↑-upRep₃ M'))) in
       let step2 : Θ , A ⟦ σ ⟧ 〈 ρ 〉 , A ⟦ σ ⟧ 〈 ρ 〉 ⇑ , var x₁ ≡〈 A ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ 〉 var x₀ ⊢
                 P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 ∶ 
                 appT (M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x₂) ≡〈 B ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑ 〉 appT (M' ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x₁)
           step2 = change-type (Weakening step3 (ctxER (varR x₁ (ctxTR (ctxTR validΘ))) (varR x₀ (ctxTR (ctxTR validΘ)))) 
                               (change-codR (Rep↑-typed (Rep↑-typed (Rep↑-typed ρ∶Δ⇒Θ))) 
                                 (cong₂ (λ a b → Θ ,T A ⟦ σ ⟧ 〈 ρ 〉 ,T a ,E b) 
                                   (Rep↑-upRep (A ⟦ σ ⟧)) 
                                   (cong (λ a → var x₁ ≡〈 a 〉 var x₀) 
                                     (Rep↑-upRep₂ (A ⟦ σ ⟧)))))) 
                               (cong₃ _≡〈_〉_ (cong (λ x → appT x (var x₂)) (Rep↑-upRep₃ (M ⟦ σ ⟧))) 
                                 (Rep↑-upRep₃ (B ⟦ σ ⟧)) 
                                 (cong (λ x → appT x (var x₁)) (Rep↑-upRep₃ (M' ⟦ σ ⟧)))) in
       let step1 : Θ ⊢ λλλ (A ⟦ σ ⟧ 〈 ρ 〉) (P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉) ∶ (M ⟦ σ ⟧ 〈 ρ 〉) ≡〈 (A ⟦ σ ⟧ 〈 ρ 〉) ⇛ (B ⟦ σ ⟧ 〈 ρ 〉) 〉 (M' ⟦ σ ⟧ 〈 ρ 〉)
           step1 = lllR step2 in
       let target : Θ ⊢ app* N N' (λλλ (A ⟦ σ ⟧ 〈 ρ 〉) (P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉)) Q ∶ appT (M ⟦ σ ⟧ 〈 ρ 〉) N ≡〈 B ⟦ σ ⟧ 〈 ρ 〉 〉 appT (M' ⟦ σ ⟧ 〈 ρ 〉) N'
           target = app*R step1 (EE-typed Q∈EΘN≡N') in
       target)
    (redexR βE) 
    (βE-exp (E-SN (close (A ⟦ σ ⟧)) N∈EΘA) (E-SN (close (A ⟦ σ ⟧)) N'∈EΘA) 
      (EE-SN (N ≡〈 A ⟦ σ ⟧ 〈 ρ 〉 〉 N') Q∈EΘN≡N') 
      (EE-SN (appT (M ⟦ σ ⟧ 〈 ρ 〉) N ≡〈 B ⟦ σ ⟧ 〈 ρ 〉 〉 appT (M' ⟦ σ ⟧ 〈 ρ 〉) N') ih))))
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
