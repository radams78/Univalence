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

--TODO Rename
Computable-Proof-Substitution : ∀ U V (σ : Sub U V) Γ Δ δ φ →
  σ ∶ Γ ⇒C Δ → Γ ⊢ δ ∶ φ → valid Δ → EP Δ (φ ⟦ σ ⟧) (δ ⟦ σ ⟧)
Computable-Path-Substitution₁ : ∀ U V (σ : Sub U V) Γ Δ P E →
  σ ∶ Γ ⇒C Δ → Γ ⊢ P ∶ E → valid Δ → EE Δ (E ⟦ σ ⟧) (P ⟦ σ ⟧)
Computable-Path-Substitution : ∀ U V (τ : PathSub U V) σ σ' Γ Δ M A → τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → 
  EE Δ (M ⟦ σ ⟧ ≡〈 A ⟦ σ ⟧ 〉 M ⟦ σ' ⟧) (M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧) 

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
        ≡⟨ cong (λ x → (x 〈 Rep↑ -Proof ρ 〉) ⟦ x₀:= ε ⟧) (Sub↑-upRep {E = ψ}) ⟩
--TODO Make E explicit?
            ψ ⟦ σ ⟧ ⇑ 〈 Rep↑ -Proof ρ 〉 ⟦ x₀:= ε ⟧
       ≡⟨ sub-congl (Rep↑-upRep (ψ ⟦ σ ⟧)) ⟩
         ψ ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⟦ x₀:= ε ⟧
       ≡⟨ botsub-upRep ⟩
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
      ≡⟨ rep-congl (Sub↑-upRep {E = ψ}) ⟩
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
  func-EE (λ W Θ N N' Q ρ ρ∶Δ⇒Θ Θvalid N∈EΘA N'∈EΘA Q∈EΘN≡N' → 
    expand-EE 
    (subst₂ (EE Θ) {!!} {!!}
    (Computable-Path-Substitution₁ (U , -Term , -Term , -Path) W 
      (x₀:= Q • (Sub↑ -Path (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ)))))
       (Γ ,T A ,T A ⇑ ,E var x₁ ≡〈 A ⇑ ⇑ 〉 var x₀) Θ P
       (appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 B ⇑ ⇑ ⇑ 〉 appT (M' ⇑ ⇑ ⇑) (var x₁)) 
       (compC {σ = Sub↑ -Path (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ)))} (botsubCE Q∈EΘN≡N') 
         (change-cod 
           (Sub↑C (compC {σ = Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •₁ σ))} 
             (botsubC {M = N'} {A = A ⟦ σ ⟧ 〈 ρ 〉} 
               (subst (λ x → E Θ x N') (sym (close-rep (A ⟦ σ ⟧))) N'∈EΘA))
             (change-cod 
               (Sub↑C (compC {σ = Sub↑ -Term (ρ •₁ σ)} (botsubC {A = A ⟦ σ ⟧ 〈 ρ 〉}
                 (subst (λ x → E Θ x N) (sym (close-rep (A ⟦ σ ⟧))) N∈EΘA)) 
                 (change-cod 
                   (Sub↑C {σ = ρ •₁ σ}
                     (comp₁C ρ∶Δ⇒Θ σ∶Γ⇒Δ)) 
                   {!!}))) 
               {!!}))) 
           {!!})) 
       Γ+⊢P∶Mx≡M'y
       Θvalid) )
    (app*R (lllR {!!}) (EE-typed Q∈EΘN≡N')) 
    (redexR βE) {!!})
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ (app*R Γ⊢P∶M≡M' Γ⊢Q∶N≡N') validΔ = 
  app*-EE 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢P∶M≡M' validΔ) 
  (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢Q∶N≡N' validΔ)
Computable-Path-Substitution₁ U V σ Γ Δ P _ σ∶Γ⇒Δ (convER Γ⊢P∶E Γ⊢P∶E₁ Γ⊢P∶E₂ x x₁) validΔ = {!!}

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
