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

Computable-Proof-Substitution U V σ Γ Δ .(var x) .(typeof x Γ) σ∶Γ⇒CΔ (varR x x₁) validΔ = proj₁ (proj₂ σ∶Γ⇒CΔ) x
Computable-Proof-Substitution U V σ Γ Δ .(appP δ ε) .ψ σ∶Γ⇒CΔ (appPR {δ = δ} {ε} {φ} {ψ} Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) validΔ = appP-EP {V} {Δ} {δ ⟦ σ ⟧} {ε ⟦ σ ⟧} {φ ⟦ σ ⟧} {ψ ⟦ σ ⟧}
  (Computable-Proof-Substitution U V σ Γ Δ δ (φ ⊃ ψ) σ∶Γ⇒CΔ Γ⊢δ∶φ⊃ψ validΔ) 
  (Computable-Proof-Substitution U V σ Γ Δ ε φ σ∶Γ⇒CΔ Γ⊢ε∶φ validΔ)
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒CΔ (ΛPR {δ = δ} {φ} {ψ} Γ,φ⊢δ∶ψ) validΔ = 
  aux-lm1 U V σ Γ Δ φ δ ψ 
    (λ W Θ τ τ∶Γ,φ⇒CΘ validΘ → Computable-Proof-Substitution (U , -Proof) W τ (Γ , φ) Θ δ (ψ ⇑)
                          τ∶Γ,φ⇒CΘ Γ,φ⊢δ∶ψ validΘ) σ∶Γ⇒CΔ Γ,φ⊢δ∶ψ validΔ
Computable-Proof-Substitution U V σ Γ Δ δ φ σ∶Γ⇒CΔ (convR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ) validΔ = 
  conv-EP (respects-conv (respects-osr substitution β-respects-sub) φ≃ψ) 
  (Computable-Proof-Substitution U V σ Γ Δ δ _ σ∶Γ⇒CΔ Γ⊢δ∶φ validΔ)
  (Substitution Γ⊢ψ∶Ω validΔ (subC-typed σ∶Γ⇒CΔ))
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒CΔ (plusR Γ⊢P∶φ≡ψ) validΔ = 
  plus-EP (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢P∶φ≡ψ validΔ)
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒CΔ (minusR Γ⊢P∶φ≡ψ) validΔ = 
  minus-EP (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢P∶φ≡ψ validΔ)

Computable-Path-Substitution₁ U V σ Γ Δ .(var x) .(typeof x Γ) σ∶Γ⇒CΔ (varR x x₁) validΔ = proj₂ (proj₂ σ∶Γ⇒CΔ) x
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ (refR {M = M} {A} Γ⊢M∶A) validΔ = ref-EE
  (subst (λ x → E Δ x (M ⟦ σ ⟧)) (sym (close-sub A)) 
  (Computable-Substitution U V σ Γ Δ M A σ∶Γ⇒CΔ Γ⊢M∶A validΔ))
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ (imp*R Γ⊢P∶φ≡φ' Γ⊢Q∶ψ≡ψ') validΔ = 
  imp*-EE 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢P∶φ≡φ' validΔ) 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢Q∶ψ≡ψ' validΔ)
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) validΔ = 
  univ-EE 
  (Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢δ∶φ⊃ψ validΔ) 
  (Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢ε∶ψ⊃φ validΔ)
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ (lllR .{U} .{Γ} {A} {B} {M} {M'} {P} Γ+⊢P∶Mx≡M'y) validΔ = 
  aux-lm2 U V σ Γ Δ A B M M' P σ∶Γ⇒CΔ Γ+⊢P∶Mx≡M'y validΔ 
  (λ W Θ τ τ∶Γ+⇒Θ validΘ → Computable-Path-Substitution₁ (U , -Term , -Term , -Path) W τ (Γ , A , A ⇑ , var x₁ ≡〈 A ⇑ ⇑ 〉 var x₀) Θ P
                             _ τ∶Γ+⇒Θ Γ+⊢P∶Mx≡M'y validΘ)
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ (app*R Γ⊢P∶M≡M' Γ⊢Q∶N≡N') validΔ = 
  app*-EE 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢P∶M≡M' validΔ) 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒CΔ Γ⊢Q∶N≡N' validΔ)
Computable-Path-Substitution₁ U V σ Γ Δ P _ σ∶Γ⇒CΔ (convER {M = M} {M'} {N} {N'} {A} Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') validΔ = 
  conv-EE  (Computable-Path-Substitution₁ U V σ Γ Δ P _ σ∶Γ⇒CΔ Γ⊢P∶M≡N validΔ) 
    (trans-conv (respects-conv {f = λ a → a ⟦ σ ⟧ ≡〈 A ⟦ σ ⟧ 〉 N ⟦ σ ⟧} (λ x → app (appl (respects-osr substitution β-respects-sub x))) M≃M') 
      (respects-conv {f = λ a → M' ⟦ σ ⟧ ≡〈 A ⟦ σ ⟧ 〉 a ⟦ σ ⟧} (λ x → app (appr (appl (respects-osr substitution β-respects-sub x)))) N≃N'))

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
    let σ₁ = x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ in
    let σ₂ = x₀:= N' •₂ Rep↑ -Term ρ • Sub↑ -Term σ' in
    let ρ' = Rep↑ -Path (Rep↑ -Term (Rep↑ -Term ρ)) in
    let step1 : x₀:= N • Sub↑ -Term (ρ •₁ σ) ∼ σ₁
        step1 = sub-trans (comp-congr Sub↑-comp₁) 
                  (assoc₁₂ {ρ = x₀:= N} {σ = Rep↑ -Term ρ} {τ = Sub↑ -Term σ}) in
    let step2 : x₀:= N' • Sub↑ -Term (ρ •₁ σ') ∼ σ₂
        step2 = sub-trans (comp-congr Sub↑-comp₁) 
                  (assoc₁₂ {ρ = x₀:= N'} {σ = Rep↑ -Term ρ} {τ = Sub↑ -Term σ'}) in
    let ih : EE Θ (M ⟦ σ₁ ⟧ ≡〈 B ⇑ ⟦ σ₁ ⟧ 〉 M ⟦ σ₂ ⟧) 
                  (M ⟦⟦ extendPS (ρ •RP τ) Q ∶ σ₁ ∼ σ₂ ⟧⟧)
        ih = (Computable-Path-Substitution (U , -Term) W (extendPS (ρ •RP τ) Q) (σ₁) (σ₂) (Γ ,T A) Θ _ _ 
             (change-ends {σ = x₀:= N' • Sub↑ -Term (ρ •₁ σ')} {σ' = σ₂} (extendPS-typedC (compRP-typedC {σ' = σ'} τ∶σ∼σ' ρ∶Δ⇒Θ)
               (subst (λ a → EE Θ (N ≡〈 a 〉 N') Q) (trans (sym (sub-comp₁ A)) (type-sub {A = A})) Q∈EΘN≡N')) 
                 step1 step2) Γ,A⊢M∶B validΘ) in
    expand-EE 
      (conv-EE 
        (subst (EE Θ (M ⟦ σ₁ ⟧ ≡〈 B ⇑ ⟦ σ₁ ⟧ 〉 M ⟦ σ₂ ⟧)) 
          (let open ≡-Reasoning in
          begin
            M ⟦⟦ extendPS (ρ •RP τ) Q ∶ σ₁ ∼
                 σ₂ ⟧⟧
          ≡⟨⟨ pathsub-cong M ∼∼-refl step1 step2 ⟩⟩
            M ⟦⟦ extendPS (ρ •RP τ) Q ∶ x₀:= N • Sub↑ -Term (ρ •₁ σ) ∼
                 x₀:= N' • Sub↑ -Term (ρ •₁ σ') ⟧⟧
          ≡⟨ pathsub-extendPS M ⟩
            M ⟦⟦ pathsub↑ (ρ •RP τ) ∶ sub↖ (ρ •₁ σ) ∼ sub↗ (ρ •₁ σ') ⟧⟧ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
          ≡⟨ sub-congl (pathsub-cong M pathsub↑-compRP sub↖-comp₁ sub↗-comp₁) ⟩
            M ⟦⟦ ρ' •RP pathsub↑ τ ∶ ρ' •₁ sub↖ σ ∼ ρ' •₁ sub↗ σ' ⟧⟧ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
          ≡⟨ sub-congl (Rep↑↑↑-pathsub M) ⟩
            (M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧) 〈 ρ' 〉 ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
          ∎) 
          ih)
          (trans-conv
            {N =
             appT ((ΛT A M ⟦ σ ⟧) 〈 ρ 〉) N ≡〈 (B ⟦ σ ⟧) 〈 ρ 〉 〉
             M ⟦ σ₂ ⟧}
          (subst₂
             (λ a b →
                (a ≡〈 b 〉 M ⟦ σ₂ ⟧) ≃
                (appT ((ΛT A M ⟦ σ ⟧) 〈 ρ 〉) N ≡〈 (B ⟦ σ ⟧) 〈 ρ 〉 〉 M ⟦ σ₂ ⟧))
             (let open ≡-Reasoning in
             begin
               M ⟦ Sub↑ -Term σ ⟧ 〈 Rep↑ -Term ρ 〉 ⟦ x₀:= N ⟧
             ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ -Term σ ⟧) ⟩⟩
               M ⟦ Sub↑ -Term σ ⟧ ⟦ x₀:= N •₂ Rep↑ -Term ρ ⟧
             ≡⟨⟨ sub-comp M ⟩⟩
               M ⟦ x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ ⟧
             ∎)
             (let open ≡-Reasoning in 
             begin
               B ⟦ σ ⟧ 〈 ρ 〉
             ≡⟨⟨ botsub-upRep (B ⟦ σ ⟧ 〈 ρ 〉) ⟩⟩
               B ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⟦ x₀:= N ⟧
             ≡⟨⟨ sub-congl (Rep↑-upRep (B ⟦ σ ⟧)) ⟩⟩
               B ⟦ σ ⟧ ⇑ 〈 Rep↑ -Term ρ 〉 ⟦ x₀:= N ⟧
             ≡⟨⟨ sub-comp₂ (B ⟦ σ ⟧ ⇑) ⟩⟩
               B ⟦ σ ⟧ ⇑ ⟦ x₀:= N •₂ Rep↑ -Term ρ ⟧
             ≡⟨⟨ sub-congl (Sub↑-upRep B) ⟩⟩
               B ⇑ ⟦ Sub↑ -Term σ ⟧ ⟦ x₀:= N •₂ Rep↑ -Term ρ ⟧
             ≡⟨⟨ sub-comp (B ⇑) ⟩⟩
               B ⇑ ⟦ x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ ⟧
             ∎) 
             (respects-conv {f = λ a → a ≡〈 (B ⟦ σ ⟧) 〈 ρ 〉 〉 M ⟦ σ₂ ⟧} 
               (λ x → app (appl x)) 
             (sym-conv (osr-conv (redex βI))))) 
             (respects-conv
                {f = λ a → appT ((ΛT A M ⟦ σ ⟧) 〈 ρ 〉) N ≡〈 (B ⟦ σ ⟧) 〈 ρ 〉 〉 a} 
                (λ x → app (appr (appl x)))
                (subst (λ a → a ≃ appT ((ΛT A M ⟦ σ' ⟧) 〈 ρ 〉) N') 
                  (let open ≡-Reasoning in
             begin
               M ⟦ Sub↑ -Term σ' ⟧ 〈 Rep↑ -Term ρ 〉 ⟦ x₀:= N' ⟧
             ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ -Term σ' ⟧) ⟩⟩
               M ⟦ Sub↑ -Term σ' ⟧ ⟦ x₀:= N' •₂ Rep↑ -Term ρ ⟧
             ≡⟨⟨ sub-comp M ⟩⟩
               M ⟦ x₀:= N' •₂ Rep↑ -Term ρ • Sub↑ -Term σ' ⟧
             ∎) 
                  (sym-conv (osr-conv (redex βI)))))))
             (let step3 : Δ , ty A , ty A , var x₁ ≡〈 ty A 〉 var x₀ ⊢
                         M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧
                         ∶ M ⟦ sub↖ σ ⟧ ≡〈 ty B 〉 M ⟦ sub↗ σ' ⟧
                  step3 = (change-type (Path-Substitution Γ,A⊢M∶B (pathsub↑-typed (pathsubC-typed {τ = τ} {σ} {σ'} {Γ} {Δ} τ∶σ∼σ'))) 
                          (cong (λ a → M ⟦ sub↖ σ ⟧ ≡〈 a 〉 M ⟦ sub↗ σ' ⟧) (ty-rep B))
                          ) in 
             let step4 : Θ , ty A , ty A , var x₁ ≡〈 ty A 〉 var x₀ ⊢
                         M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ 〈 ρ' 〉
                         ∶ M ⟦ sub↖ σ ⟧ 〈 ρ' 〉 ≡〈 ty B 〉 M ⟦ sub↗ σ' ⟧ 〈 ρ' 〉
                 step4 = change-type 
                       (Weakening step3 
                         (ctxER (change-type (varR x₁ (ctxTR (ctxTR validΘ))) (trans (rep-congl (ty-rep' A)) (ty-rep' A))) 
                         (change-type (varR x₀ (ctxTR (ctxTR validΘ))) (ty-rep' A))) 
                         (change-codR (Rep↑-typed (Rep↑-typed (Rep↑-typed ρ∶Δ⇒Θ))) 
                         (cong₃ (λ a b c → Θ , a , b , c) (ty-rep' A) (ty-rep' A) 
                           (cong (λ a → var x₁ ≡〈 a 〉 var x₀) (ty-rep' A))))) 
                       (cong (λ a → (M ⟦ sub↖ σ ⟧) 〈 ρ' 〉 ≡〈 a 〉 (M ⟦ sub↗ σ' ⟧) 〈 ρ' 〉)
                          (ty-rep' B)) in
             let step5 : Θ , ty A , ty A ,E var x₁ ≡〈 ty A 〉 var x₀ ⊢
                       appT ((ΛT A M) ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x₂) ∶ ty B
                 step5 = appR 
                         (change-type {A = (A ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) ⇛ ty B} 
                           (ΛR (subst₂ (λ a b → Θ ,T ty A ,T ty A ,E var x₁ ≡〈 ty A 〉 var x₀ ,T A ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑ ⊢ a ∶ b) 
                           (trans (sub-comp₁ M) (trans (rep-comp (M ⟦ Sub↑ _ σ ⟧))
                           (trans (rep-comp (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉)) 
                             (rep-comp (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉)))))
                         (trans (sym close-magic) (trans (ty-sub (B ⇑)) (trans (ty-rep B) (sym (ty-rep' B))))) 
                         (Substitution {σ = Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ ρ •₁ Sub↑ _ σ} Γ,A⊢M∶B 
                         (ctxTR (ctxER (change-type (varR x₁ (ctxTR (ctxTR validΘ))) 
                           (trans (rep-congl (ty-rep' A)) (ty-rep' A))) 
                           (change-type (varR x₀ (ctxTR (ctxTR validΘ))) (ty-rep' A)))) 
                         (comp₁-typed
                            {ρ = Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ ρ}
                            {σ = Sub↑ _ σ} 
                            (compR-typed {ρ = Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ upRep}
                              {σ = Rep↑ _ ρ}
                              (compR-typed {ρ = Rep↑ _ upRep •R Rep↑ _ upRep} {σ = Rep↑ _ upRep}
                                (compR-typed {ρ = Rep↑ _ upRep} {σ = Rep↑ _ upRep} (Rep↑-typed upRep-typed) (Rep↑-typed upRep-typed)) (Rep↑-typed upRep-typed)) 
                            (Rep↑-typed ρ∶Δ⇒Θ))
                         (Sub↑-typed (pathsub-valid₁ {σ = σ'} 
                           (pathsubC-typed {U} {V} {τ} {σ} {σ'} {Γ = Γ} {Δ = Δ} τ∶σ∼σ'))))))) 
                         (cong (λ a → a ⇛ ty B) 
                           (trans (sym close-magic) (trans (trans (ty-rep (A ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑)) (trans (ty-rep (A ⟦ σ ⟧ 〈 ρ 〉 ⇑)) (trans (ty-rep (A ⟦ σ ⟧ 〈 ρ 〉)) (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A))))) (sym (trans (rep-congl (rep-congl (ty-rep' A))) (trans (rep-congl (ty-rep' A)) (ty-rep' A))))))))
                         (varR x₂ (ctxER (change-type (varR x₁ (ctxTR (ctxTR validΘ))) (trans (rep-congl (ty-rep' A)) (ty-rep' A))) (change-type (varR x₀ (ctxTR (ctxTR validΘ))) (ty-rep' A)))) in
             let step5' : Θ , ty A , ty A ,E var x₁ ≡〈 ty A 〉 var x₀ ⊢
                       appT ((ΛT A M) ⟦ σ' ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x₁) ∶ ty B
                 step5' = appR 
                         (change-type {A = (A ⟦ σ' ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) ⇛ ty B} 
                           (ΛR (subst₂ (λ a b → Θ ,T ty A ,T ty A ,E var x₁ ≡〈 ty A 〉 var x₀ ,T A ⟦ σ' ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑ ⊢ a ∶ b) 
                           (trans (sub-comp₁ M) (trans (rep-comp (M ⟦ Sub↑ _ σ' ⟧))
                           (trans (rep-comp (M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉)) 
                             (rep-comp (M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉)))))
                         (trans (sym close-magic) (trans (ty-sub (B ⇑)) (trans (ty-rep B) (sym (ty-rep' B))))) 
                         (Substitution {σ = Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ ρ •₁ Sub↑ _ σ'} Γ,A⊢M∶B 
                         (ctxTR (ctxER (change-type (varR x₁ (ctxTR (ctxTR validΘ))) 
                           (trans (rep-congl (ty-rep' A)) (ty-rep' A))) 
                           (change-type (varR x₀ (ctxTR (ctxTR validΘ))) (ty-rep' A)))) 
                         (comp₁-typed
                            {ρ = Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ ρ}
                            {σ = Sub↑ _ σ'} 
                            (compR-typed {ρ = Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ upRep}
                              {σ = Rep↑ _ ρ}
                              (compR-typed {ρ = Rep↑ _ upRep •R Rep↑ _ upRep} {σ = Rep↑ _ upRep}
                                (compR-typed {ρ = Rep↑ _ upRep} {σ = Rep↑ _ upRep} (Rep↑-typed upRep-typed) (Rep↑-typed upRep-typed)) (Rep↑-typed upRep-typed)) 
                            (Rep↑-typed ρ∶Δ⇒Θ))
                         (Sub↑-typed (pathsub-valid₂ {σ = σ'} 
                           (pathsubC-typed {U} {V} {τ} {σ} {σ'} {Γ = Γ} {Δ = Δ} τ∶σ∼σ'))))))) 
                         (cong (λ a → a ⇛ ty B) 
                           (trans (sym close-magic) (trans (trans (ty-rep (A ⟦ σ' ⟧ 〈 ρ 〉 ⇑ ⇑)) (trans (ty-rep (A ⟦ σ' ⟧ 〈 ρ 〉 ⇑)) (trans (ty-rep (A ⟦ σ' ⟧ 〈 ρ 〉)) (trans (ty-rep (A ⟦ σ' ⟧)) (ty-sub A))))) refl ))))
                         (change-type (varR x₁ 
                           (ctxER (change-type (varR x₁ (ctxTR (ctxTR validΘ))) 
                           (trans (rep-congl (ty-rep' A)) (ty-rep' A))) 
                           (change-type (varR x₀ (ctxTR (ctxTR validΘ))) 
                             (ty-rep' A)))) 
                           (trans (rep-congl (ty-rep' A)) (ty-rep' A))) in
             let step6 : Θ , ty A , ty A , var x₁ ≡〈 ty A 〉 var x₀ ⊢
                         M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ 〈 ρ' 〉
                         ∶ appT ((ΛT A M) ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x₂) ≡〈 ty B 〉 appT ((ΛT A M) ⟦ σ' ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x₁)
                 step6 = convER step4 step5 step5' 
                         (subst (λ a → a ≃ appT (((ΛT A M ⟦ σ ⟧) 〈 ρ 〉) ⇑ ⇑ ⇑) (var x₂)) 
                         (let open ≡-Reasoning in
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •₂ Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= (var x₂) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ ⟧) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ ⟦ x₀:= (var x₂) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ ρ ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₂) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ ρ • Sub↑ _ σ ⟧
                         ≡⟨ sub-congr M aux ⟩
                           M ⟦ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) •₁ sub↖ σ ⟧
                         ≡⟨ sub-comp₁ M ⟩ 
                           M ⟦ sub↖ σ ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉
                           ∎)
                           (sym-conv (osr-conv (redex βI)))) 
                         (subst (λ a → a ≃ appT (((ΛT A M ⟦ σ' ⟧) 〈 ρ 〉) ⇑ ⇑ ⇑) (var x₁)) 
                           (let open ≡-Reasoning in 
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •₂ Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= (var x₁) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ' ⟧) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ ⟦ x₀:= (var x₁) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ ρ ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₁) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ ρ • Sub↑ _ σ' ⟧
                         ≡⟨ sub-congr M aux₂ ⟩
                           M ⟦ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) •₁ sub↗ σ' ⟧
                         ≡⟨ sub-comp₁ M ⟩ 
                           M ⟦ sub↗ σ' ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉
                           ∎)
                           (sym-conv (osr-conv (redex βI)))) in
      app*R (lllR (subst₄
                     (λ a b c d →
                        Θ , a , b , var x₁ ≡〈 c 〉 var x₀ ⊢
                        (M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧) 〈 ρ' 〉 ∶
                        appT (((ΛT A M ⟦ σ ⟧) 〈 ρ 〉) ⇑ ⇑ ⇑) (var x₂) ≡〈 d 〉
                        appT (((ΛT A M ⟦ σ' ⟧) 〈 ρ 〉) ⇑ ⇑ ⇑) (var x₁))
                     (sym (trans (sym close-magic) (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A)))) 
                     (sym (trans (sym close-magic) (trans (ty-rep (A ⟦ σ ⟧ 〈 ρ 〉)) (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A))))) 
                     (sym (trans (sym close-magic) (trans (ty-rep (A ⟦ σ ⟧ 〈 ρ 〉 ⇑)) (trans (ty-rep (A ⟦ σ ⟧ 〈 ρ 〉)) (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A)))))) 
                     (sym (trans (sym close-magic) (trans (ty-rep (B ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑)) (trans (ty-rep (B ⟦ σ ⟧ 〈 ρ 〉 ⇑)) (trans (ty-rep (B ⟦ σ ⟧ 〈 ρ 〉)) (trans (ty-rep (B ⟦ σ ⟧)) (ty-sub B))))))) 
                     step6)) 
      (EE-typed Q∈EΘN≡N'))
      (redexR βE) 
      (βE-exp (E-SN _ N∈EΘA) (E-SN _ N'∈EΘA) (EE-SN _ Q∈EΘN≡N') 
      (subst SN (let open ≡-Reasoning in 
      begin
         M ⟦⟦ extendPS (ρ •RP τ) Q ∶
      x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ ∼
      x₀:= N' •₂ Rep↑ -Term ρ • Sub↑ -Term σ' ⟧⟧
      ≡⟨ pathsub-cong M ∼∼-refl (sub-sym step1) (sub-sym step2) ⟩
         M ⟦⟦ extendPS (ρ •RP τ) Q ∶
      x₀:= N • Sub↑ _ (ρ •₁ σ) ∼ x₀:= N' • Sub↑ _ (ρ •₁ σ') ⟧⟧
      ≡⟨ pathsub-extendPS M ⟩
        M ⟦⟦ pathsub↑ (ρ •RP τ) ∶ sub↖ (ρ •₁ σ) ∼ sub↗ (ρ •₁ σ') ⟧⟧
        ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
      ≡⟨ sub-congl (pathsub-cong M pathsub↑-compRP sub↖-comp₁ sub↗-comp₁) ⟩
        M ⟦⟦ ρ' •RP pathsub↑ τ ∶ ρ' •₁ sub↖ σ ∼ ρ' •₁ sub↗ σ' ⟧⟧
        ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
      ≡⟨ sub-congl (Rep↑↑↑-pathsub M) ⟩
        M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ 
        〈 ρ' 〉
        ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
      ∎) 
      (EE-SN _ ih)))) where
    aux : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} → 
        x₀:= (var x₂) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ ρ • Sub↑ _ σ ∼ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) •₁ sub↖ σ
    aux x₀ = refl
    aux {ρ = ρ} {σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₂) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep •₂
       Rep↑ -Term upRep
       •₂ Rep↑ -Term ρ ⟧
      ≡⟨ sub-comp₂ (σ _ x ⇑) ⟩
        σ _ x ⇑ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= (var x₂) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⟦ x₀:= (var x₂) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-comp₂ (σ _ x 〈 ρ 〉 ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x 〈 ρ 〉)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⟦ x₀:= (var x₂) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-comp₂ (σ _ x 〈 ρ 〉 ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x 〈 ρ 〉 ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-comp₂ (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ 〈 Rep↑ -Term upRep 〉 ⟦ x₀:= (var x₂) ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) ⟧
      ≡⟨ botsub-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑
      ≡⟨⟨ Rep↑-upRep₃ (σ _ x) ⟩⟩
        σ _ x ⇑ ⇑ ⇑ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉
      ∎
    aux₂ : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} → 
        x₀:= (var x₁) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ ρ • Sub↑ _ σ ∼ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) •₁ sub↗ σ
    aux₂ x₀ = refl
    aux₂ {ρ = ρ} {σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₁) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep •₂
       Rep↑ -Term upRep
       •₂ Rep↑ -Term ρ ⟧
      ≡⟨ sub-comp₂ (σ _ x ⇑) ⟩
        σ _ x ⇑ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= (var x₁) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⟦ x₀:= (var x₁) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-comp₂ (σ _ x 〈 ρ 〉 ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x 〈 ρ 〉)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⟦ x₀:= (var x₁) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-comp₂ (σ _ x 〈 ρ 〉 ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x 〈 ρ 〉 ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-comp₂ (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ 〈 Rep↑ -Term upRep 〉 ⟦ x₀:= (var x₁) ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) ⟧
      ≡⟨ botsub-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑
      ≡⟨⟨ Rep↑-upRep₃ (σ _ x) ⟩⟩
        σ _ x ⇑ ⇑ ⇑ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉
      ∎


Strong-Normalization : ∀ V K (Γ : Context V) (M : Expression V (varKind K)) A → Γ ⊢ M ∶ A → SN M
Strong-Normalization V -Proof Γ δ φ Γ⊢δ∶φ = EP-SN 
  (subst (EP Γ _) sub-idOp
  (Computable-Proof-Substitution V V (idSub V) Γ Γ δ φ idSubC Γ⊢δ∶φ (Context-Validity Γ⊢δ∶φ)))
Strong-Normalization V -Term Γ M A Γ⊢M∶A = E-SN (close A)
  (subst (E Γ (close A)) sub-idOp 
  (Computable-Substitution V V (idSub V) Γ Γ M A idSubC Γ⊢M∶A (Context-Validity Γ⊢M∶A)))
Strong-Normalization V -Path Γ P E Γ⊢P∶E = EE-SN E 
  (subst₂ (EE Γ) sub-idOp sub-idOp
  (Computable-Path-Substitution₁ V V (idSub V) Γ Γ P E idSubC Γ⊢P∶E (Context-Validity Γ⊢P∶E)))
\end{code}
