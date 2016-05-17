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
open import PHOPL.SN
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
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒CΔ (ΛPR {δ = δ} {φ} {ψ} Γ,φ⊢δ∶ψ) validΔ = 
  aux-lm1 U V σ Γ Δ φ δ ψ 
    (λ W Θ τ τ∶Γ,φ⇒CΘ validΘ → Computable-Proof-Substitution (U , -Proof) W τ (Γ , φ) Θ δ (ψ ⇑)
                          τ∶Γ,φ⇒CΘ Γ,φ⊢δ∶ψ validΘ) σ∶Γ⇒CΔ Γ,φ⊢δ∶ψ validΔ
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
       (let step3 : Δ , A ⟦ σ ⟧ , A ⟦ σ ⟧ ⇑ , var x₁ ≡〈 A ⟦ σ ⟧ ⇑ ⇑ 〉 var x₀ ⊢
                  P ⟦ Sub↑ _ (Sub↑ _ (Sub↑ _ σ)) ⟧ ∶ appT (M ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₂) ≡〈 B ⟦ σ ⟧ ⇑ ⇑ ⇑ 〉 appT (M' ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₁)
            step3 = change-type (Substitution Γ+⊢P∶Mx≡M'y (ctxER (varR x₁ (ctxTR (ctxTR validΔ))) (varR x₀ (ctxTR (ctxTR validΔ)))) 
                                             (change-cod' (Sub↑-typed (Sub↑-typed (Sub↑-typed (subC-typed σ∶Γ⇒Δ)))) 
                                               (cong₂ (λ a b → Δ ,T A ⟦ σ ⟧ ,T a ,E b) 
                                                 (Sub↑-upRep A) 
                                                 (cong (λ a → var x₁ ≡〈 a 〉 var x₀) (Sub↑-upRep₂ A))))) 
                               (cong₃ (λ a b c → appT a (var x₂) ≡〈 b 〉 appT c (var x₁)) 
                                 (Sub↑-upRep₃ M) (Sub↑-upRep₃ B) (Sub↑-upRep₃ M')) in
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
      {!!}))
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
Strong-Normalization V -Term Γ M A Γ⊢M∶A = E-SN (close A)
  (subst (E Γ (close A)) sub-idOp 
  (Computable-Substitution V V (idSub V) Γ Γ M A {!!} Γ⊢M∶A {!!}))
Strong-Normalization V -Path Γ P E Γ⊢P∶E = {!!}
\end{code}
