\begin{code}
module PHOPL.MainProp where
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
open import PHOPL.MainPropFinal

--TODO Rename
Computable-Proof-Substitution : ∀ U V (σ : Sub U V) Γ Δ δ φ →
  σ ∶ Γ ⇒C Δ → Γ ⊢ δ ∶ φ → valid Δ → EP Δ (φ ⟦ σ ⟧) (δ ⟦ σ ⟧)
Computable-Path-Substitution₁ : ∀ U V (σ : Sub U V) Γ Δ P E →
  σ ∶ Γ ⇒C Δ → Γ ⊢ P ∶ E → valid Δ → EE Δ (E ⟦ σ ⟧) (P ⟦ σ ⟧)

Computable-Proof-Substitution U V σ Γ Δ .(var x) .(typeof x Γ) σ∶Γ⇒Δ (varR x x₁) Δvalid = proj₁ (proj₂ σ∶Γ⇒Δ) x
Computable-Proof-Substitution U V σ Γ Δ .(appP δ ε) .ψ σ∶Γ⇒Δ (appPR {δ = δ} {ε} {φ} {ψ} Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) Δvalid = appP-EP {V} {Δ} {δ ⟦ σ ⟧} {ε ⟦ σ ⟧} {φ ⟦ σ ⟧} {ψ ⟦ σ ⟧}
  (Computable-Proof-Substitution U V σ Γ Δ δ (φ ⊃ ψ) σ∶Γ⇒Δ Γ⊢δ∶φ⊃ψ Δvalid) 
  (Computable-Proof-Substitution U V σ Γ Δ ε φ σ∶Γ⇒Δ Γ⊢ε∶φ Δvalid)
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒CΔ (ΛPR {δ = δ} {φ} {ψ} Γ,φ⊢δ∶ψ) Δvalid = 
  func-EP (λ W Θ ρ ε validΘ ρ∶Δ⇒RΘ ε∈EΘφσρ → 
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
       (Computable-Proof-Substitution (U , -Proof) W (x₀:= ε •₂ Rep↑ -Proof ρ • Sub↑ -Proof σ) (Γ ,P φ) Θ δ (ψ ⇑) (compC (comp₂C (botsubCP ε∈EΘφσρ) (Rep↑-typed ρ∶Δ⇒RΘ)) (Sub↑C σ∶Γ⇒CΔ)) Γ,φ⊢δ∶ψ validΘ)
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
Computable-Proof-Substitution U V σ Γ Δ δ φ σ∶Γ⇒Δ (convR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ) Δvalid = 
  conv-EP (respects-conv (respects-osr substitution β-respects-sub) φ≃ψ) 
  (Computable-Proof-Substitution U V σ Γ Δ δ _ σ∶Γ⇒Δ Γ⊢δ∶φ Δvalid)
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒Δ (plusR Γ⊢P∶φ≡ψ) Δvalid = 
  plus-EP (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢P∶φ≡ψ Δvalid)
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒Δ (minusR Γ⊢P∶φ≡ψ) Δvalid = 
  minus-EP (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢P∶φ≡ψ Δvalid)

Computable-Path-Substitution₁ U V σ Γ Δ .(var x) .(typeof x Γ) σ∶Γ⇒Δ (varR x x₁) validΔ = proj₂ (proj₂ σ∶Γ⇒Δ) x
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ (refR {M = M} {A} Γ⊢M∶A) validΔ = ref-EE
  (subst (λ x → E Δ x (M ⟦ σ ⟧)) (sym (close-sub A)) 
  (Computable-Substitution U V σ Γ Δ M A σ∶Γ⇒Δ Γ⊢M∶A validΔ))
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ (imp*R Γ⊢P∶φ≡φ' Γ⊢Q∶ψ≡ψ') validΔ = 
  imp*-EE 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢P∶φ≡φ' validΔ) 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢Q∶ψ≡ψ' validΔ)
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) validΔ = 
  univ-EE 
  (Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢δ∶φ⊃ψ validΔ) 
  (Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢ε∶ψ⊃φ validΔ)
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ (lllR .{U} .{Γ} {A} {B} {M} {M'} {P} Γ+⊢P∶Mx≡M'y) validΔ = 
  func-EE (λ W Θ N N' Q ρ ρ∶Δ⇒Θ validΘ N∈EΘA N'∈EΘA Q∈EΘN≡N' → 
    expand-EE 
    (subst₂ (EE Θ) (cong₃ _≡〈_〉_ 
      (cong₂ appT 
        (lemma M Q N' N ρ σ)
        (let open ≡-Reasoning in 
          begin
            N ⇑ ⟦ x₀:= N' ⟧ ⇑ ⟦ x₀:= Q ⟧
          ≡⟨ botsub-upRep _ ⟩
            N ⇑ ⟦ x₀:= N' ⟧
          ≡⟨ botsub-upRep N ⟩
            N
          ∎)) 
        (lemma B Q N' N ρ σ)
        (cong₂ appT 
        (let open ≡-Reasoning in 
          begin
            M' ⇑ ⇑ ⇑ ⟦ x₀:= Q • Sub↑ -Path (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ))) ⟧
          ≡⟨ botsub-comp-upRep (M' ⇑ ⇑) ⟩
            M' ⇑ ⇑ ⟦ x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ)) ⟧
          ≡⟨ botsub-comp-upRep (M' ⇑) ⟩
            M' ⇑ ⟦ x₀:= N • Sub↑ -Term (ρ •₁ σ) ⟧
          ≡⟨ botsub-comp-upRep M' ⟩
            M' ⟦ ρ •₁ σ ⟧
          ≡⟨ sub-comp₁ M' ⟩
            M' ⟦ σ ⟧ 〈 ρ 〉
          ∎) 
        (botsub-upRep _))) 
      (let open ≡-Reasoning in 
      begin
        P ⟦ x₀:= Q • Sub↑ -Path (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ))) ⟧
      ≡⟨ sub-comp P ⟩
        P ⟦ Sub↑ _ (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ))) ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ sub-congl (sub-congr P Sub↑-comp) ⟩
        P ⟦ Sub↑ _ (x₀:= N') • Sub↑ _ (Sub↑ _ (x₀:= N • Sub↑ _ (ρ •₁ σ))) ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ sub-congl (sub-comp P) ⟩
        P ⟦ Sub↑ _ (Sub↑ _ (x₀:= N • Sub↑ _ (ρ •₁ σ))) ⟧ ⟦ Sub↑ _ (x₀:= N') ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ sub-congl (sub-congl (sub-congr P (Sub↑-cong Sub↑-comp))) ⟩
        P ⟦ Sub↑ _ (Sub↑ _ (x₀:= N) • Sub↑ _ (Sub↑ _ (ρ •₁ σ))) ⟧ ⟦ Sub↑ _ (x₀:= N') ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ sub-congl (sub-congl (sub-congr P Sub↑-comp)) ⟩
        P ⟦ Sub↑ _ (Sub↑ _ (x₀:= N)) • Sub↑ _ (Sub↑ _ (Sub↑ _ (ρ •₁ σ))) ⟧ ⟦ Sub↑ _ (x₀:= N') ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ sub-congl (sub-congl (sub-comp P)) ⟩
        P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ (ρ •₁ σ))) ⟧ ⟦ Sub↑ _ (Sub↑ _ (x₀:= N)) ⟧ ⟦ Sub↑ _ (x₀:= N') ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ sub-congl (sub-congl (sub-congl (sub-congr P (Sub↑-cong (Sub↑-cong Sub↑-comp₁))))) ⟩
        P ⟦ Sub↑ _ (Sub↑ _ (Rep↑ _ ρ •₁ Sub↑ _ σ)) ⟧ ⟦ Sub↑ _ (Sub↑ _ (x₀:= N)) ⟧ ⟦ Sub↑ _ (x₀:= N') ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ sub-congl (sub-congl (sub-congl (sub-congr P (Sub↑-cong Sub↑-comp₁)))) ⟩
        P ⟦ Sub↑ _ (Rep↑ _ (Rep↑ _ ρ) •₁ Sub↑ _ (Sub↑ _ σ)) ⟧ ⟦ Sub↑ _ (Sub↑ _ (x₀:= N)) ⟧ ⟦ Sub↑ _ (x₀:= N') ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ sub-congl (sub-congl (sub-congl (sub-congr P Sub↑-comp₁))) ⟩
        P ⟦ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) •₁ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ ⟦ Sub↑ _ (Sub↑ _ (x₀:= N)) ⟧ ⟦ Sub↑ _ (x₀:= N') ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ sub-congl (sub-congl (sub-congl (sub-comp₁ P))) ⟩
        P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 ⟦ Sub↑ _ (Sub↑ _ (x₀:= N)) ⟧ ⟦ Sub↑ _ (x₀:= N') ⟧ ⟦ x₀:= Q ⟧
      ≡⟨⟨ sub-congl (sub-comp (P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉)) ⟩⟩
        P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 ⟦ Sub↑ _ (x₀:= N') • Sub↑ _ (Sub↑ _ (x₀:= N)) ⟧ ⟦ x₀:= Q ⟧
      ≡⟨⟨ sub-congl (sub-congr (P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉) Sub↑-comp) ⟩⟩
        P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 ⟦ Sub↑ _ (x₀:= N' • Sub↑ _ (x₀:= N)) ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ sub-congl (sub-congr (P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉) (Sub↑-cong (botsub-botsub' N N'))) ⟩
        P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 ⟦ Sub↑ _ (x₀:= N • x₀:= (N' ⇑)) ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ sub-congl (sub-congr (P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉) Sub↑-comp) ⟩
        P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 ⟦ Sub↑ _ (x₀:= N) • Sub↑ _ (x₀:= (N' ⇑)) ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ sub-congl (sub-comp (P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉)) ⟩
        P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 ⟦ Sub↑ _ (x₀:= (N' ⇑)) ⟧ ⟦ Sub↑ _ (x₀:= N) ⟧ ⟦ x₀:= Q ⟧
      ≡⟨ botsub-botsub (P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 ⟦ Sub↑ _ (x₀:= (N' ⇑)) ⟧) N Q ⟩
        P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 ⟦ Sub↑ _ (x₀:= (N' ⇑)) ⟧ ⟦ x₀:= (Q ⇑) ⟧ ⟦ x₀:= N ⟧
      ≡⟨ sub-congl (botsub-botsub ( P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉) (N' ⇑) (Q ⇑)) ⟩
        P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉  ⟦ x₀:= (Q ⇑ ⇑) ⟧ ⟦ x₀:= (N' ⇑) ⟧ ⟦ x₀:= N ⟧
      ≡⟨⟨ sub-comp (P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉  ⟦ x₀:= (Q ⇑ ⇑) ⟧ ) ⟩⟩
        P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉  ⟦ x₀:= (Q ⇑ ⇑) ⟧ ⟦ x₀:= N • x₀:= (N' ⇑) ⟧
      ≡⟨⟨ sub-comp (P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉) ⟩⟩
        P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉  ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
      ∎)
    (Computable-Path-Substitution₁ (U , -Term , -Term , -Path) W 
      (x₀:= Q • (Sub↑ -Path (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ)))))
       (Γ ,T A ,T A ⇑ ,E var x₁ ≡〈 A ⇑ ⇑ 〉 var x₀) Θ P
       (appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 B ⇑ ⇑ ⇑ 〉 appT (M' ⇑ ⇑ ⇑) (var x₁)) 
       (compC {σ = Sub↑ -Path (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ)))} (botsubCE Q∈EΘN≡N') 
         (Sub↑-lm {U , -Term , -Term} {W} {V} { -Path} (Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ))) 
           ρ (Γ , A , A ⇑) Θ N' (A ⟦ σ ⟧) (var x₁ ≡〈 A ⇑ ⇑ 〉 var x₀) (N ≡〈 A ⟦ σ ⟧ 〈 ρ 〉 〉 N') 
           (Sub↑-lm {U , -Term} {W} {V} { -Term} (Sub↑ -Term (ρ •₁ σ)) ρ (Γ , A) Θ N (A ⟦ σ ⟧) (A ⇑) (A ⟦ σ ⟧ 〈 ρ 〉) 
             (Sub↑-lm₁ (ρ •₁ σ) Γ A Θ (A ⟦ σ ⟧ 〈 ρ 〉) 
               (comp₁C ρ∶Δ⇒Θ σ∶Γ⇒Δ) 
               (sub-comp₁ A)) 
             N∈EΘA 
             (let open ≡-Reasoning in 
                 begin
                   A ⇑ ⟦ x₀:= N • Sub↑ -Term (ρ •₁ σ) ⟧
                 ≡⟨ botsub-comp-upRep A ⟩
                   A ⟦ ρ •₁ σ ⟧
                 ≡⟨ sub-comp₁ A ⟩
                   A ⟦ σ ⟧ 〈 ρ 〉
                 ∎)) 
           N'∈EΘA (cong₂ (λ a b → a ≡〈 b 〉 N')
             (botsub-upRep _)
             (let open ≡-Reasoning in 
             begin
               A ⇑ ⇑ ⟦ x₀:= N' • Sub↑ _ (x₀:= N • Sub↑ _ (ρ •₁ σ)) ⟧
             ≡⟨ botsub-comp-upRep (A ⇑) ⟩
               A ⇑ ⟦ x₀:= N • Sub↑ _ (ρ •₁ σ) ⟧
             ≡⟨ botsub-comp-upRep A ⟩
               A ⟦ ρ •₁ σ ⟧
             ≡⟨ sub-comp₁ A ⟩
               A ⟦ σ ⟧ 〈 ρ 〉
             ∎))))
       Γ+⊢P∶Mx≡M'y
       validΘ) )
       (let step1 : Δ , A ⟦ σ ⟧ , A ⇑ ⟦ Sub↑ _ σ ⟧ , var x₁ ≡〈 A ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ σ) ⟧ 〉 var x₀ ⊢ P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ ∶ appT (M ⇑ ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧) (var x₂) ≡〈 B ⇑ ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〉 appT (M' ⇑ ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧) (var x₁)
            step1 = Substitution Γ+⊢P∶Mx≡M'y (ctxER 
              (change-type (varR x₁ (ctxTR (ctxTR validΔ))) 
               (let open ≡-Reasoning in 
               begin
                 A ⟦ σ ⟧ ⇑ ⇑
               ≡⟨⟨ Sub↑-upRep₂ A ⟩⟩
                 A ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ σ) ⟧
               ∎)) 
              (change-type (varR x₀ (ctxTR (ctxTR validΔ))) (sym (Sub↑-upRep (A ⇑))))) 
              (Sub↑-typed (Sub↑-typed (Sub↑-typed (subC-typed σ∶Γ⇒Δ)))) in
       let step2 : Θ , A ⟦ σ ⟧ 〈 ρ 〉 , A ⇑ ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 , var x₁ ≡〈 A ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ σ) ⟧ 〈 Rep↑ _ (Rep↑ _ ρ) 〉 〉 var x₀ ⊢ P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 ∶ appT (M ⇑ ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉) (var x₂) ≡〈 B ⇑ ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 〉 appT (M' ⇑ ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉) (var x₁)
           step2 = Weakening step1 (ctxER 
             (change-type (varR x₁ (ctxTR (ctxTR validΘ))) 
               (let open ≡-Reasoning in 
               begin
                 A ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑
               ≡⟨⟨ Rep↑-upRep₂ (A ⟦ σ ⟧) ⟩⟩
                 A ⟦ σ ⟧ ⇑ ⇑ 〈 Rep↑ _ (Rep↑ _ ρ) 〉
               ≡⟨⟨ rep-congl (Sub↑-upRep₂ A) ⟩⟩
                 A ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ σ) ⟧ 〈 Rep↑ _ (Rep↑ _ ρ) 〉
               ∎)) 
             (change-type (varR x₀ (ctxTR (ctxTR validΘ))) 
             (let open ≡-Reasoning in 
             begin
               A ⇑ ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 ⇑
             ≡⟨⟨ Rep↑-upRep (A ⇑ ⟦ Sub↑ _ σ ⟧) ⟩⟩
               A ⇑ ⟦ Sub↑ _ σ ⟧ ⇑ 〈 Rep↑ _ (Rep↑ _ ρ) 〉
             ≡⟨⟨ rep-congl (Sub↑-upRep (A ⇑)) ⟩⟩
               A ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ σ) ⟧ 〈 Rep↑ _ (Rep↑ _ ρ) 〉
             ∎))) 
             (Rep↑-typed (Rep↑-typed (Rep↑-typed ρ∶Δ⇒Θ))) in
       let step3 : Θ , A ⟦ σ ⟧ 〈 ρ 〉 , N ⇑ ≡〈 A ⇑ ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〉 var x₀ ⊢ P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉 ⟦ Sub↑ _ (Sub↑ _ (x₀:= N)) ⟧ ∶ appT (M ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ σ) ⟧ 〈 Rep↑ _ (Rep↑ _ ρ) 〉) (N ⇑ ⇑) ≡〈 B ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ σ) ⟧ 〈 Rep↑ _ (Rep↑ _ ρ) 〉 〉 appT (M' ⇑ ⇑ ⟦ Sub↑ _ (Sub↑ _ σ) ⟧ 〈 Rep↑ _ (Rep↑ _ ρ) 〉) (var x₁)
           step3 = change-type (Substitution step2 
             (ctxER (change-type (Weakening (E-typed N∈EΘA) (ctxTR validΘ) 
             upRep-typed) 
             (let open ≡-Reasoning in 
             begin
               close (A ⟦ σ ⟧) 〈 magic 〉 ⇑
             ≡⟨ magic-unique' (close (A ⟦ σ ⟧)) ⟩
               close (A ⟦ σ ⟧) 〈 magic 〉
             ≡⟨ rep-congl (close-sub A) ⟩
               close A 〈 magic 〉
             ≡⟨⟨ rep-congl (close-rep A) ⟩⟩
               close (A ⇑) 〈 magic 〉
             ≡⟨⟨ rep-congl (close-sub (A ⇑)) ⟩⟩
               close (A ⇑ ⟦ Sub↑ _ σ ⟧) 〈 magic 〉
             ≡⟨⟨ rep-congl (close-rep (A ⇑ ⟦ Sub↑ _ σ ⟧)) ⟩⟩
               close (A ⇑ ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉) 〈 magic 〉
             ≡⟨ close-magic ⟩
               A ⇑ ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉
             ∎)) 
             (change-type (varR x₀ (ctxTR validΘ)) 
               (let open ≡-Reasoning in 
               begin
                 A ⟦ σ ⟧ 〈 ρ 〉 ⇑
               ≡⟨⟨ Rep↑-upRep (A ⟦ σ ⟧) ⟩⟩
                 A ⟦ σ ⟧ ⇑ 〈 Rep↑ -Term ρ 〉
               ≡⟨⟨ rep-congl (Sub↑-upRep A) ⟩⟩
                 A ⇑ ⟦ Sub↑ -Term σ ⟧ 〈 Rep↑ -Term ρ 〉
               ∎))) 
               (change-cod' (Sub↑-typed (Sub↑-typed (botsub-typed (change-type (E-typed N∈EΘA) 
               (let open ≡-Reasoning in 
               begin
                 close (A ⟦ σ ⟧) 〈 magic 〉
               ≡⟨⟨ rep-congl (close-rep (A ⟦ σ ⟧)) ⟩⟩
                 close (A ⟦ σ ⟧ 〈 ρ 〉) 〈 magic 〉
               ≡⟨ close-magic ⟩
                 A ⟦ σ ⟧ 〈 ρ 〉
               ∎))))) --TODO Common pattern with Sub↑-lm₁ ?
               (cong₂ (λ a b → Θ ,T a ,E N ⇑ ≡〈 b 〉 var x₀) 
                 (let open ≡-Reasoning in 
                 begin
                   A ⇑ ⟦ Sub↑ -Term σ ⟧ 〈 Rep↑ -Term ρ 〉 ⟦ x₀:= N ⟧
                 ≡⟨ sub-congl (rep-congl (Sub↑-upRep A)) ⟩
                   A ⟦ σ ⟧ ⇑ 〈 Rep↑ -Term ρ 〉 ⟦ x₀:= N ⟧
                 ≡⟨ sub-congl (Rep↑-upRep (A ⟦ σ ⟧)) ⟩
                   A ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⟦ x₀:= N ⟧
                 ≡⟨ botsub-upRep _ ⟩
                   A ⟦ σ ⟧ 〈 ρ 〉
                 ∎) 
                 (let open ≡-Reasoning in 
                 begin
                   A ⇑ ⇑ ⟦ Sub↑ -Term (Sub↑ -Term σ) ⟧ 〈 Rep↑ -Term (Rep↑ -Term ρ) 〉 ⟦ Sub↑ -Term (x₀:= N) ⟧
                 ≡⟨ sub-congl (rep-congl (Sub↑-upRep₂ A)) ⟩
                   A ⟦ σ ⟧ ⇑ ⇑ 〈 Rep↑ -Term (Rep↑ -Term ρ) 〉 ⟦ Sub↑ -Term (x₀:= N) ⟧
                 ≡⟨ sub-congl (Rep↑-upRep₂ (A ⟦ σ ⟧)) ⟩
                   A ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⟦ Sub↑ -Term (x₀:= N) ⟧
                 ≡⟨ Sub↑-upRep (A ⟦ σ ⟧ 〈 ρ 〉 ⇑) ⟩
                   A ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⟦ x₀:= N ⟧ ⇑
                 ≡⟨ rep-congl (botsub-upRep (A ⟦ σ ⟧ 〈 ρ 〉)) ⟩
                   A ⟦ σ ⟧ 〈 ρ 〉 ⇑
                 ≡⟨⟨ Rep↑-upRep (A ⟦ σ ⟧) ⟩⟩
                   A ⟦ σ ⟧ ⇑ 〈 Rep↑ -Term ρ 〉
                 ≡⟨⟨ rep-congl (Sub↑-upRep A) ⟩⟩
                   A ⇑ ⟦ Sub↑ -Term σ ⟧ 〈 Rep↑ -Term ρ 〉
                 ∎)))) 
               (cong₃ _≡〈_〉_ (cong (λ x → appT x (N ⇑ ⇑))
                 (subrepsublemma M)) 
               (subrepsublemma B) (cong (λ y → appT y (var x₁)) (subrepsublemma M'))) in
       let target : Θ ⊢ app* N N' (λλλ (A ⟦ σ ⟧ 〈 ρ 〉) (P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉)) Q ∶ appT (M ⟦ σ ⟧ 〈 ρ 〉) N ≡〈 B ⟦ σ ⟧ 〈 ρ 〉 〉 appT (M' ⟦ σ ⟧ 〈 ρ 〉) N'
           target = {!!} in
       target)
    (redexR βE) {!!})
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ (app*R Γ⊢P∶M≡M' Γ⊢Q∶N≡N') validΔ = 
  app*-EE 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢P∶M≡M' validΔ) 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢Q∶N≡N' validΔ)
Computable-Path-Substitution₁ U V σ Γ Δ P _ σ∶Γ⇒Δ (convER Γ⊢P∶E Γ⊢P∶E₁ Γ⊢P∶E₂ x x₁) validΔ = {!!}

Computable-Path-Substitution : ∀ U V (τ : PathSub U V) σ σ' Γ Δ M A → τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → 
  EE Δ (M ⟦ σ ⟧ ≡〈 A ⟦ σ ⟧ 〉 M ⟦ σ' ⟧) (M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧) 
Computable-Path-Substitution U V τ σ σ' Γ Δ .(var x) .(typeof x Γ) τ∶σ∼σ' (varR x x₁) _ = 
  τ∶σ∼σ' x
Computable-Path-Substitution U V τ σ σ' Γ Δ .(app -bot out) .(app -Omega out) τ∶σ∼σ' (⊥R x) validΔ = ref-EE (⊥-E validΔ)
Computable-Path-Substitution U V τ σ σ' Γ Δ _ .(app -Omega out) τ∶σ∼σ' (impR Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = imp*-EE 
  (Computable-Path-Substitution U V τ σ σ' Γ Δ _ Ω τ∶σ∼σ' Γ⊢φ∶Ω validΔ) 
  (Computable-Path-Substitution U V τ σ σ' Γ Δ _ Ω τ∶σ∼σ' Γ⊢ψ∶Ω validΔ) 
Computable-Path-Substitution U V τ σ σ' Γ Δ _ A τ∶σ∼σ' (appR Γ⊢M∶A⇒B Γ⊢N∶A) validΔ = app*-EE 
  (Computable-Path-Substitution U V τ σ σ' Γ Δ _ _ τ∶σ∼σ' Γ⊢M∶A⇒B validΔ) 
  (Computable-Path-Substitution U V τ σ σ' Γ Δ _ _ τ∶σ∼σ' Γ⊢N∶A validΔ)
Computable-Path-Substitution .U V τ σ σ' .Γ Δ _ _ τ∶σ∼σ' (ΛR {U} {Γ} {A} {M} {B} Γ,A⊢M∶B) validΔ = 
  func-EE (λ W Θ N N' Q ρ ρ∶Δ⇒Θ validΘ N∈EΘA N'∈EΘA Q∈EΘN≡N' → 
    expand-EE 
      (conv-EE 
        (subst (EE Θ (M ⟦ x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ ⟧ ≡〈 B ⇑ ⟦ x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ ⟧ 〉 M ⟦ x₀:= N' •₂ Rep↑ -Term ρ • Sub↑ -Term σ' ⟧)) 
          {!!} 
          (Computable-Path-Substitution (U , -Term) W {!!} (x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ) (x₀:= N' •₂ Rep↑ -Term ρ • Sub↑ -Term σ') (Γ ,T A) Θ _ _ {!!} Γ,A⊢M∶B validΘ)) 
        {!!}) 
      {!!} 
      (redexR βE) 
      {!!})

Strong-Normalization : ∀ V K (Γ : Context V) (M : Expression V (varKind K)) A → Γ ⊢ M ∶ A → SN M
Strong-Normalization V -Proof Γ δ φ Γ⊢δ∶φ = {!!}
Strong-Normalization V -Term Γ M A Γ⊢M∶A = E-SN V Γ (close A) M 
  (subst (E Γ (close A)) sub-idOp 
  (Computable-Substitution V V (idSub V) Γ Γ M A {!!} Γ⊢M∶A {!!}))
Strong-Normalization V -Path Γ P E Γ⊢P∶E = {!!}
\end{code}
