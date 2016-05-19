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
open import PHOPL.MainProp1

--TODO Rename
Computable-Path-Substitution : ∀ U V (τ : PathSub U V) σ σ' Γ Δ M A → τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → 
  EE Δ (M ⟦ σ ⟧ ≡〈 A ⟦ σ ⟧ 〉 M ⟦ σ' ⟧) (M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧) 
Computable-Path-Substitution U V τ σ σ' Γ Δ .(var x) .(typeof x Γ) τ∶σ∼σ' (varR x x₁) _ = 
  τ∶σ∼σ' x
Computable-Path-Substitution U V τ σ σ' Γ Δ .(app -bot out) .(app -Omega out) τ∶σ∼σ' (⊥R x) validΔ = ref-EE (⊥-E validΔ)
Computable-Path-Substitution U V τ σ σ' Γ Δ _ .(app -Omega out) τ∶σ∼σ' (impR Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = imp*-EE 
  (Computable-Path-Substitution U V τ σ σ' Γ Δ _ Ω τ∶σ∼σ' Γ⊢φ∶Ω validΔ) 
  (Computable-Path-Substitution U V τ σ σ' Γ Δ _ Ω τ∶σ∼σ' Γ⊢ψ∶Ω validΔ) 
Computable-Path-Substitution U V τ σ σ' Γ Δ _ .B τ∶σ∼σ' (appR {N = N} {A} {B} Γ⊢M∶A⇒B Γ⊢N∶A) validΔ = 
  app*-EE 
  (Computable-Path-Substitution U V τ σ σ' Γ Δ _ _ τ∶σ∼σ' Γ⊢M∶A⇒B validΔ) 
  (Computable-Path-Substitution U V τ σ σ' Γ Δ _ _ τ∶σ∼σ' Γ⊢N∶A validΔ)
  (subst (λ a → E Δ a (N ⟦ σ ⟧)) (sym (close-sub A)) 
    (Computable-Substitution U V σ Γ Δ N A (pathsubC-valid₁ {U} {V} {τ} {σ} {σ'} τ∶σ∼σ') Γ⊢N∶A validΔ)) 
  (subst (λ a → E Δ a (N ⟦ σ' ⟧)) (sym (close-sub A)) 
    (Computable-Substitution U V σ' Γ Δ N A (pathsubC-valid₂ {σ = σ'} τ∶σ∼σ') Γ⊢N∶A validΔ))
Computable-Path-Substitution .U V τ σ σ' .Γ Δ _ _ τ∶σ∼σ' (ΛR {U} {Γ} {A} {M} {B} Γ,A⊢M∶B) validΔ = 
  let validΔAA : valid (Δ ,T ty A ,T ty A)
      validΔAA = ctxTR (ctxTR validΔ) in
  let validΔAAE : valid (Δ ,T ty A ,T ty A ,E var x₁ ≡〈 ty A 〉 var x₀)
      validΔAAE = ctxER (change-type (varR x₁ validΔAA) 
                                        (trans (rep-congl (ty-rep' A)) (ty-rep' A))) 
                                      (change-type (varR x₀ validΔAA) (ty-rep' A)) in
  let Blm : ∀ (σ : Sub U V) → B ⇑ ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ≡ B ⟦ σ ⟧ ⇑ ⇑ ⇑ ⇑
      Blm σ = let open ≡-Reasoning in 
                           begin
                             B ⇑ ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉
                           ≡⟨ rep-congl (rep-congl (rep-congl (Sub↑-upRep B))) ⟩
                             B ⟦ σ ⟧ ⇑ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉
                           ≡⟨ rep-congl (rep-congl (Rep↑-upRep (B ⟦ σ ⟧))) ⟩
                             B ⟦ σ ⟧ ⇑ ⇑ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉
                           ≡⟨ rep-congl (Rep↑-upRep (B ⟦ σ ⟧ ⇑)) ⟩
                             B ⟦ σ ⟧ ⇑ ⇑ ⇑ 〈 Rep↑ _ upRep 〉
                           ≡⟨ Rep↑-upRep (B ⟦ σ ⟧ ⇑ ⇑) ⟩
                             B ⟦ σ ⟧ ⇑ ⇑ ⇑ ⇑
                           ∎ in
  func-EE (lllR (convER (change-type
                           (Path-Substitution Γ,A⊢M∶B
                            (subst₃
                             (λ a b c →
                                pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ∶ Γ , A ⇒
                                (Δ , a , b , var x₁ ≡〈 c 〉 var x₀))
                             (trans (sym (ty-sub A)) close-magic)
                             (trans (sym (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A))) close-magic)
                             (trans
                              (sym
                               (trans (ty-rep ((A ⟦ σ ⟧) ⇑))
                                (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A))))
                              close-magic)
                             (pathsub↑-typed (pathsubC-typed {σ = σ'} τ∶σ∼σ'))))
                           (cong (λ a → M ⟦ sub↖ σ ⟧ ≡〈 a 〉 M ⟦ sub↗ σ' ⟧) 
                             (trans (trans (ty-rep B) (sym (trans (ty-rep (B ⟦ σ ⟧ ⇑ ⇑)) (trans (ty-rep (B ⟦ σ ⟧ ⇑)) (trans (ty-rep (B ⟦ σ ⟧)) (ty-sub B)))))) close-magic))) 
                             (appR (ΛR (change-type 
                                        (Weakening {ρ = Rep↑ _ upRep}
                                           {M = ((M ⟦ Sub↑ _ σ ⟧) 〈 Rep↑ _ upRep 〉) 〈 Rep↑ _ upRep 〉} 
                                        (Weakening {ρ = Rep↑ _ upRep}
                                           {M = (M ⟦ Sub↑ _ σ ⟧) 〈 Rep↑ _ upRep 〉} 
                                        (Weakening {ρ = Rep↑ _ upRep} {M = M ⟦ Sub↑ _ σ ⟧} 
                                        (Substitution {σ = Sub↑ -Term σ} {M = M} Γ,A⊢M∶B (ctxTR validΔ) 
                                          (Sub↑-typed (pathsub-valid₁ {τ = τ} {σ} {σ'} {Γ} {Δ} (pathsubC-typed {τ = τ} {ρ = σ} {σ = σ'} {Γ} {Δ} τ∶σ∼σ')))) (ctxTR (ctxTR validΔ)) (Rep↑-typed upRep-typed)) 
                                        (ctxTR (ctxTR (ctxTR validΔ))) 
                                        (Rep↑-typed upRep-typed)) 
                           (ctxTR (ctxER (varR (↑ x₀) (ctxTR (ctxTR validΔ))) (varR x₀ (ctxTR (ctxTR validΔ))))) 
                           (Rep↑-typed upRep-typed)) (Blm σ))) 
                           (varR x₂ (ctxER ((varR (↑ x₀) (ctxTR (ctxTR validΔ)))) (varR x₀ (ctxTR (ctxTR validΔ))))))  
                              (let stepA : Δ , ty A , ty A ,E var x₁ ≡〈 ty A 〉 var x₀ ,T ty A ⊢ M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ∶ ty B
                                   stepA = (change-type 
                                      (Weakening {U = V , -Term , -Term , -Term} {V = V , -Term , -Term , -Path , -Term} {ρ = Rep↑ _ upRep} {Γ = Δ , ty A , ty A , ty A} {M = M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉} 
                                      (Weakening {ρ = Rep↑ _ upRep} {Γ = Δ , ty A , ty A}
                                         {M = (M ⟦ Sub↑ _ σ' ⟧) 〈 Rep↑ _ upRep 〉} 
                                      (Weakening {ρ = Rep↑ _ upRep} {M = M ⟦ Sub↑ _ σ' ⟧} 
                                      (Substitution {σ = Sub↑ _ σ'} {M = M} 
                                      Γ,A⊢M∶B 
                                      (ctxTR validΔ) 
                                      (Sub↑-typed (pathsub-valid₂ (pathsubC-typed {τ = τ} {σ} {σ'} {Γ} {Δ} τ∶σ∼σ')))) 
                                      validΔAA 
                                      (change-codR (Rep↑-typed (upRep-typed {A = ty A})) (cong (λ a → Δ , ty A , a) (trans (sym close-magic) (trans (ty-rep (A ⟦ σ' ⟧)) (ty-sub A))))))
                                      (ctxTR validΔAA) 
                                      (change-codR (Rep↑-typed (upRep-typed {A = ty A})) (cong (λ a → Δ , ty A , ty A , a) (ty-rep' A))))
                                      (ctxTR validΔAAE)
                                      (change-codR (Rep↑-typed (upRep-typed {A = var x₁ ≡〈 ty A 〉 var x₀})) (cong (λ a → Δ , ty A , ty A ,E var x₁ ≡〈 ty A 〉 var x₀ ,T a) (ty-rep' A)))) 
                                      (trans (sym close-magic) (trans (ty-rep (B ⇑ ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉)) (trans (ty-rep (B ⇑ ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉)) (trans (ty-rep (B ⇑ ⟦ Sub↑ _ σ' ⟧)) (trans (ty-sub (B ⇑)) (ty-rep B))))))) in
                              let A-is-A : ∀ (σ : Sub U V) → (ty A) ⟦ σ' ⟧ ⇑ ⇑ ⇑ ≡ ty A
                                  A-is-A σ = trans (rep-congl (rep-congl (rep-congl (ty-sub' A)))) (trans (rep-congl (rep-congl (ty-rep' A))) (trans (rep-congl (ty-rep' A)) (ty-rep' A))) in
                              let stepB : Δ , ty A , ty A ,E var x₁ ≡〈 ty A 〉 var x₀ ⊢ (ΛT (ty A) M) ⟦ σ' ⟧ ⇑ ⇑ ⇑ ∶ ty A ⇛ ty B
                                  stepB = change-type (ΛR (subst₂
                                                             (λ a b →
                                                                Δ , ty A , ty A ,E var x₁ ≡〈 ty A 〉 var x₀ ,T a ⊢
                                                                (((M ⟦ Sub↑ _ σ' ⟧) 〈 Rep↑ _ upRep 〉) 〈 Rep↑ _ upRep 〉) 〈
                                                                Rep↑ _ upRep 〉
                                                                ∶ b)
                                          (sym (A-is-A σ)) (sym (ty-rep' B))
                                          stepA)) 
                                          (cong₂ _⇛_ (A-is-A σ') refl) in
                              let stepC : Δ , ty A , ty A ,E var x₁ ≡〈 ty A 〉 var x₀ ⊢ var x₁ ∶ ty A
                                  stepC = change-type (varR x₁ validΔAAE) 
                                          (trans (rep-congl (ty-rep' A)) (ty-rep' A)) in
                              let stepD : Δ , ty A , ty A ,E var x₁ ≡〈 ty A 〉 var x₀ ⊢ appT ((ΛT (ty A) M) ⟦ σ' ⟧ ⇑ ⇑ ⇑) (var x₁) ∶ ty B
                                  stepD = appR stepB stepC in
                              subst₃ _⊢_∶_ (cong₃ (λ a b c → Δ , a , b ,E c) 
                                (trans (sym (ty-sub A)) close-magic) 
                                (trans (sym (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A))) close-magic)
                                (cong (λ a → var x₁ ≡〈 a 〉 var x₀) 
                                  (trans (sym (trans (ty-rep (A ⟦ σ ⟧ ⇑)) (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A)))) close-magic))) (cong (λ a → appT ((ΛT a M ⟦ σ' ⟧) ⇑ ⇑ ⇑) (var x₁)) {x = ty A} {y = A} close-magic) (trans (sym (trans (ty-rep (B ⟦ σ ⟧ ⇑ ⇑)) (trans (ty-rep (B ⟦ σ ⟧ ⇑)) (trans (ty-rep (B ⟦ σ ⟧)) (ty-sub B))))) close-magic) stepD)
                        (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M ⟦ σ ⟧) ⇑ ⇑ ⇑) (var x₂) ⇒ a) (let open ≡-Reasoning in
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •₂ Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ ⟧) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ ⟦ x₀:= (var x₂) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₂) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep • Sub↑ _ σ ⟧
                         ≡⟨ sub-congr M aux₃ ⟩
                           M ⟦ sub↖ σ ⟧
                           ∎) (redex βI)))) 
                         (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M ⟦ σ' ⟧) ⇑ ⇑ ⇑) (var x₁) ⇒ a) 
                         (let open ≡-Reasoning in
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •₂ Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp₂ (M ⟦ Sub↑ _ σ' ⟧) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ ⟦ x₀:= (var x₁) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₁) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep • Sub↑ _ σ' ⟧
                         ≡⟨ sub-congr M aux₄ ⟩
                           M ⟦ sub↗ σ' ⟧
                           ∎) 
                         (redex βI))))))
    (λ W Θ N N' Q ρ ρ∶Δ⇒Θ validΘ N∈EΘA N'∈EΘA Q∈EΘN≡N' → 
    let σ₁ = x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ in
    let σ₂ = x₀:= N' •₂ Rep↑ -Term ρ • Sub↑ -Term σ' in
    let ρ' = Rep↑ -Path (Rep↑ -Term (Rep↑ -Term ρ)) in
    let step1 : x₀:= N • Sub↑ -Term (ρ •₁ σ) ∼ σ₁
        step1 = sub-trans (comp-congr Sub↑-comp₁) 
                  (assoc₁₂ {ρ = x₀:= N} {σ = Rep↑ -Term ρ} {τ = Sub↑ -Term σ}) in
    let step2 : x₀:= N' • Sub↑ -Term (ρ •₁ σ') ∼ σ₂
        step2 = sub-trans (comp-congr Sub↑-comp₁) 
                  (assoc₁₂ {ρ = x₀:= N'} {σ = Rep↑ -Term ρ} {τ = Sub↑ -Term σ'}) in
    let sub-rep-comp : ∀ (σ : Sub U V) (N : Term W) → M ⟦ x₀:= N •₂ Rep↑ _ ρ • Sub↑ _ σ ⟧ ≡ M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= N ⟧
        sub-rep-comp σ N = let open ≡-Reasoning in
             begin
               M ⟦ x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ ⟧
             ≡⟨ sub-comp M ⟩
               M ⟦ Sub↑ -Term σ ⟧ ⟦ x₀:= N •₂ Rep↑ -Term ρ ⟧
             ≡⟨ sub-comp₂ (M ⟦ Sub↑ -Term σ ⟧) ⟩
               M ⟦ Sub↑ -Term σ ⟧ 〈 Rep↑ -Term ρ 〉 ⟦ x₀:= N ⟧
             ∎ in
    let ih : EE Θ (M ⟦ σ₁ ⟧ ≡〈 B ⇑ ⟦ σ₁ ⟧ 〉 M ⟦ σ₂ ⟧) 
                  (M ⟦⟦ extendPS (ρ •RP τ) Q ∶ σ₁ ∼ σ₂ ⟧⟧)
        ih = (Computable-Path-Substitution (U , -Term) W (extendPS (ρ •RP τ) Q) (σ₁) (σ₂) (Γ ,T A) Θ _ _ 
             (change-ends {σ = x₀:= N' • Sub↑ -Term (ρ •₁ σ')} {σ' = σ₂} (extendPS-typedC (compRP-typedC {σ' = σ'} τ∶σ∼σ' ρ∶Δ⇒Θ)
               (subst (λ a → EE Θ (N ≡〈 a 〉 N') Q) (trans (sym (sub-comp₁ A)) (type-sub {A = A})) Q∈EΘN≡N')) 
                 step1 step2) Γ,A⊢M∶B validΘ) in
    let ih' : EE Θ (M ⟦ σ₁ ⟧ ≡〈 B ⟦ σ ⟧ 〈 ρ 〉 〉 M ⟦ σ₂ ⟧) (M ⟦⟦ extendPS (ρ •RP τ) Q ∶ σ₁ ∼ σ₂ ⟧⟧)
        ih' = subst (λ a → EE Θ (M ⟦ σ₁ ⟧ ≡〈 a 〉 M ⟦ σ₂ ⟧) (M ⟦⟦ extendPS (ρ •RP τ) Q ∶ σ₁ ∼ σ₂ ⟧⟧)) 
          (let open ≡-Reasoning in
          begin
            B ⇑ ⟦ σ₁ ⟧
          ≡⟨ sub-comp (B ⇑) ⟩
            B ⇑ ⟦ Sub↑ _ σ ⟧ ⟦ x₀:= N •₂ Rep↑ _ ρ ⟧
          ≡⟨ sub-congl (Sub↑-upRep B) ⟩
            B ⟦ σ ⟧ ⇑ ⟦ x₀:= N •₂ Rep↑ _ ρ ⟧
          ≡⟨ sub-comp₂ (B ⟦ σ ⟧ ⇑) ⟩
            B ⟦ σ ⟧ ⇑ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= N ⟧
          ≡⟨ sub-congl (Rep↑-upRep (B ⟦ σ ⟧)) ⟩
            B ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⟦ x₀:= N ⟧
          ≡⟨ botsub-upRep (B ⟦ σ ⟧ 〈 ρ 〉) ⟩
            B ⟦ σ ⟧ 〈 ρ 〉
          ∎) ih in
    let Δ,A⊢Mσ∶B : (Δ , (A ⟦ σ ⟧)) ⊢ M ⟦ Sub↑ _ σ ⟧ ∶ (B ⟦ σ ⟧ ⇑)
        Δ,A⊢Mσ∶B = change-type (Substitution Γ,A⊢M∶B (ctxTR validΔ) (Sub↑-typed (pathsub-valid₁ {τ = τ} {σ} {σ'} (pathsubC-typed {τ = τ} {σ} {σ'} τ∶σ∼σ')))) (Sub↑-upRep B) in
    let Δ,A⊢Mσ'∶B : (Δ , (A ⟦ σ' ⟧)) ⊢ M ⟦ Sub↑ _ σ' ⟧ ∶ (B ⟦ σ ⟧ ⇑)
        Δ,A⊢Mσ'∶B = change-type (Substitution Γ,A⊢M∶B (ctxTR validΔ) (Sub↑-typed (pathsub-valid₂ {τ = τ} {σ} {σ'} (pathsubC-typed {τ = τ} {σ} {σ'} τ∶σ∼σ')))) 
          (trans (sym close-magic) (trans (trans (ty-sub (B ⇑)) (trans (ty-rep B) (sym (trans (ty-rep (B ⟦ σ ⟧)) (ty-sub B))))) close-magic)) in
    let Θ,A⊢Mσ∶B : Θ , A ⟦ σ ⟧ 〈 ρ 〉 ⊢ M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 ∶ B ⟦ σ ⟧ 〈 ρ 〉 ⇑
        Θ,A⊢Mσ∶B = change-type (Weakening Δ,A⊢Mσ∶B (ctxTR validΘ) (Rep↑-typed ρ∶Δ⇒Θ)) (Rep↑-upRep (B ⟦ σ ⟧)) in
    let Θ,A⊢Mσ'∶B : Θ , A ⟦ σ' ⟧ 〈 ρ 〉 ⊢ M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 ∶ B ⟦ σ ⟧ 〈 ρ 〉 ⇑
        Θ,A⊢Mσ'∶B = change-type (Weakening Δ,A⊢Mσ'∶B (ctxTR validΘ) (Rep↑-typed ρ∶Δ⇒Θ)) (Rep↑-upRep (B ⟦ σ ⟧)) in
    let Θ⊢N∶A : Θ ⊢ N ∶ A ⟦ σ ⟧ 〈 ρ 〉
        Θ⊢N∶A = change-type (E-typed N∈EΘA) (trans (trans (ty-sub A) (sym (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A)))) close-magic) in
    let Θ⊢N'∶A : Θ ⊢ N' ∶ A ⟦ σ ⟧ 〈 ρ 〉
        Θ⊢N'∶A = change-type (E-typed N'∈EΘA) (trans (trans (ty-sub A) (sym (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A)))) close-magic) in
        expand-EE (conv-EE 
          (subst (EE Θ (M ⟦ σ₁ ⟧ ≡〈 B ⟦ σ ⟧ 〈 ρ 〉 〉 M ⟦ σ₂ ⟧)) (let open ≡-Reasoning in
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
          ∎) ih') 
          (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M) ⟦ σ ⟧ 〈 ρ 〉) N ⇒ a) (sym (sub-rep-comp σ N)) (redex βI)))) 
          (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M) ⟦ σ' ⟧ 〈 ρ 〉) N' ⇒ a) (sym (sub-rep-comp σ' N')) (redex βI)))) --REFACTOR Duplication
          (appR (ΛR Θ,A⊢Mσ∶B) Θ⊢N∶A) 
          (appR (ΛR Θ,A⊢Mσ'∶B) (change-type (E-typed N'∈EΘA) (trans (trans (ty-sub A) (sym (trans (ty-rep (A ⟦ σ' ⟧)) (ty-sub A)))) close-magic))))
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
      app*R (change-type (E-typed N∈EΘA) (trans (sym (ty-rep (A ⟦ σ ⟧))) close-magic)) 
        (change-type (E-typed N'∈EΘA) (trans (sym (ty-rep (A ⟦ σ ⟧))) close-magic)) 
      (lllR (subst₄
                     (λ a b c d →
                        Θ , a , b , var x₁ ≡〈 c 〉 var x₀ ⊢
                        (M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧) 〈 ρ' 〉 ∶
                        appT (((ΛT A M ⟦ σ ⟧) 〈 ρ 〉) ⇑ ⇑ ⇑) (var x₂) ≡〈 d 〉
                        appT (((ΛT A M ⟦ σ' ⟧) 〈 ρ 〉) ⇑ ⇑ ⇑) (var x₁))
                     (sym (trans (sym close-magic) (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A)))) 
                     (sym (trans (sym close-magic) (trans (ty-rep (A ⟦ σ ⟧ 〈 ρ 〉)) (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A))))) 
                     (sym (trans (sym close-magic) (trans (ty-rep (A ⟦ σ ⟧ 〈 ρ 〉 ⇑)) (trans (ty-rep (A ⟦ σ ⟧ 〈 ρ 〉)) (trans (ty-rep (A ⟦ σ ⟧)) (ty-sub A)))))) 
                     (sym (trans (sym close-magic) 
                     (trans (ty-rep (B ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑)) 
                       (trans (ty-rep (B ⟦ σ ⟧ 〈 ρ 〉 ⇑)) 
                         (trans (ty-rep (B ⟦ σ ⟧ 〈 ρ 〉)) 
                           (trans (ty-rep (B ⟦ σ ⟧)) 
                             (ty-sub B))))))) 
                     step6))
        (EE-typed Q∈EΘN≡N'))
        βEkr) where
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
    aux₃ : ∀ {U} {V} {σ : Sub U V} → 
        x₀:= (var x₂) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep • Sub↑ _ σ ∼ sub↖ σ
    aux₃ x₀ = refl
    aux₃ {σ = σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₂) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-comp₂ (σ _ x ⇑) ⟩
        σ _ x ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x)) ⟩
        σ _ x ⇑ ⇑ ⟦ x₀:= (var x₂) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-comp₂ (σ _ x  ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x  ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-comp₂ (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑ 〈 Rep↑ -Term upRep 〉 ⟦ x₀:= (var x₂) ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x  ⇑ ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) ⟧
      ≡⟨ botsub-upRep (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑
      ∎
    aux₄ : ∀ {U} {V} {σ : Sub U V} → 
        x₀:= (var x₁) •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep •₂ Rep↑ _ upRep • Sub↑ _ σ ∼ sub↗ σ
    aux₄ x₀ = refl
    aux₄ {σ = σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₁) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-comp₂ (σ _ x  ⇑) ⟩
        σ _ x  ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x )) ⟩
        σ _ x  ⇑ ⇑ ⟦ x₀:= (var x₁) •₂ Rep↑ -Term upRep •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-comp₂ (σ _ x  ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x  ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) •₂ Rep↑ -Term upRep ⟧
      ≡⟨ sub-comp₂ (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑ 〈 Rep↑ -Term upRep 〉 ⟦ x₀:= (var x₁) ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x  ⇑ ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) ⟧
      ≡⟨ botsub-upRep (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑
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
