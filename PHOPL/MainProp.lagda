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
  aux-lm2 U V σ Γ Δ A B M M' P σ∶Γ⇒Δ Γ+⊢P∶Mx≡M'y validΔ 
  (λ W Θ τ τ∶Γ+⇒Θ validΘ → Computable-Path-Substitution₁ (U , -Term , -Term , -Path) W τ (Γ , A , A ⇑ , var x₁ ≡〈 A ⇑ ⇑ 〉 var x₀) Θ P
                             _ τ∶Γ+⇒Θ Γ+⊢P∶Mx≡M'y validΘ)
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ (app*R Γ⊢P∶M≡M' Γ⊢Q∶N≡N') validΔ = 
  app*-EE 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢P∶M≡M' validΔ) 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢Q∶N≡N' validΔ)
Computable-Path-Substitution₁ U V σ Γ Δ P _ σ∶Γ⇒Δ (convER {M = M} {M'} {N} {N'} {A} Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') validΔ = 
  conv-EE  (Computable-Path-Substitution₁ U V σ Γ Δ P _ σ∶Γ⇒Δ Γ⊢P∶M≡N validΔ) 
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
             (change-ends {σ = x₀:= N' • Sub↑ -Term (ρ •₁ σ')} {σ' = σ₂} (extendPS-typed (compRP-typed {σ' = σ'} τ∶σ∼σ' ρ∶Δ⇒Θ)
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
      {!!} 
      (redexR βE) 
      (βE-exp (E-SN _ N∈EΘA) (E-SN _ N'∈EΘA) (EE-SN _ Q∈EΘN≡N') (EE-SN {!!} {!ih!})))

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
