\AgdaHide{
\begin{code}
module PHOPL.MainProp where
open import Data.Empty renaming (⊥ to Empty)
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
open import PHOPL.MainProp1
open import PHOPL.KeyRedex
\end{code}
}

Our main theorem is as follows.

\begin{theorem}$ $
\begin{enumerate}
\item
If $\Gamma \vdash M : A$, and $\sigma : \Gamma \rightarrow \Delta$ is computable,
then $M [ \sigma ] \in E_\Delta(A)$.
\item
If $\Gamma \vdash \delta : \phi$, and $\sigma : \Gamma \rightarrow \Delta$ is computable,
then $\delta [ \sigma ] \in E_\Delta(\phi[\sigma])$.
\item
If $\Gamma \vdash P : M =_A N$, and $\sigma : \Gamma \rightarrow \Delta$ is computable,
then $P [ \sigma ] \in E_\Delta(M [ \sigma ] =_A N [ \sigma ])$.
\item
\label{computable-path-sub}
If $\Gamma \vdash M : A$, $\tau : \sigma \sim \rho : \Gamma \rightarrow \Delta$, and $\tau$, $\sigma$
and $\rho$ are all computable, then $M \{ \tau : \sigma \sim \rho \} \in E_\Delta(M [ \sigma ] =_A M [ \rho ])$.
\end{enumerate}
\end{theorem}

%<*Computable-Sub>
\begin{code}
Computable-Sub : ∀ {U} {V} {K} (σ : Sub U V) {Γ} {Δ} 
  {M : Expression U (varKind K)} {A} →
  σ ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → E' Δ (A ⟦ σ ⟧) (M ⟦ σ ⟧)
\end{code}
%</Computable-Sub>

\AgdaHide{
\begin{code}
computable-path-substitution : ∀ U V (τ : PathSub U V) σ σ' Γ Δ M A → σ ∶ Γ ⇒C Δ → σ' ∶ Γ ⇒C Δ → τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → 
  EE Δ (M ⟦ σ ⟧ ≡〈 yt A 〉 M ⟦ σ' ⟧) (M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧) 

Computable-Sub σ σ∶Γ⇒Δ (varR x validΓ) validΔ = σ∶Γ⇒Δ x
Computable-Sub {V = V} σ {Δ = Δ} σ∶Γ⇒Δ (appR Γ⊢M∶A⇛B Γ⊢N∶A) validΔ = 
  appT-E validΔ (Computable-Sub σ σ∶Γ⇒Δ Γ⊢M∶A⇛B validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢N∶A validΔ)
Computable-Sub σ σ∶Γ⇒Δ (ΛR {M = M} {B} Γ,A⊢M∶B) validΔ = 
  func-E (λ _ Θ ρ N validΘ ρ∶Δ⇒Θ N∈EΘA → 
    let MN∈EΘB = subst (E Θ B) (subrepsub M)
                 (Computable-Sub (x₀:= N •SR rep↑ _ ρ • sub↑ -Term σ) 
                 (compC (compSRC (botsubC N∈EΘA) 
                        (rep↑-typed ρ∶Δ⇒Θ)) 
                 (sub↑C σ∶Γ⇒Δ)) 
                 Γ,A⊢M∶B validΘ) in
    expand-E MN∈EΘB
      (appR (ΛR (weakening (substitution Γ,A⊢M∶B (ctxTR validΔ) (sub↑-typed (subC-typed σ∶Γ⇒Δ))) 
                                                      (ctxTR validΘ) 
                                         (rep↑-typed ρ∶Δ⇒Θ))) 
                (E-typed N∈EΘA)) 
      (βTkr (SNap' {Ops = SUB} R-respects-sub (E-SN B MN∈EΘB))))
Computable-Sub σ σ∶Γ⇒Δ (⊥R _) validΔ = ⊥-E validΔ
Computable-Sub σ σ∶Γ⇒Δ (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = ⊃-E 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢φ∶Ω validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ψ∶Ω validΔ)
Computable-Sub σ σ∶Γ⇒Δ (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) validΔ = appP-EP 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢δ∶φ⊃ψ validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ε∶φ validΔ)
Computable-Sub σ {Γ = Γ} {Δ = Δ} σ∶Γ⇒Δ (ΛPR {δ = δ} {φ} {ψ} Γ⊢φ∶Ω Γ,φ⊢δ∶ψ) validΔ = 
  let Δ⊢Λφδσ∶φ⊃ψ : Δ ⊢ (ΛP φ δ) ⟦ σ ⟧ ∶ φ ⟦ σ ⟧ ⊃ ψ ⟦ σ ⟧
      Δ⊢Λφδσ∶φ⊃ψ = substitution {A = φ ⊃ ψ} (ΛPR Γ⊢φ∶Ω Γ,φ⊢δ∶ψ) validΔ (subC-typed σ∶Γ⇒Δ) in
  func-EP (λ W Θ ρ ε ρ∶Δ⇒Θ ε∈EΔφ → 
    let δε∈EΘψ : EP Θ (ψ ⟦ σ ⟧ 〈 ρ 〉) (δ ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ ρ 〉 ⟦ x₀:= ε ⟧)
        δε∈EΘψ = subst₂ (EP Θ) (subrepbotsub-up ψ) (subrepsub δ) 
                 (Computable-Sub (x₀:= ε •SR rep↑ _ ρ • sub↑ _ σ) 
                 (compC (compSRC (botsubCP ε∈EΔφ) 
                        (rep↑-typed ρ∶Δ⇒Θ)) 
                 (sub↑C σ∶Γ⇒Δ)) Γ,φ⊢δ∶ψ (Context-Validity (EP-typed ε∈EΔφ))) in
    expand-EP δε∈EΘψ (appPR (weakening Δ⊢Λφδσ∶φ⊃ψ (Context-Validity (EP-typed ε∈EΔφ)) ρ∶Δ⇒Θ) (EP-typed ε∈EΔφ))
      (βPkr (SNrep R-creates-rep (E-SN Ω (Computable-Sub σ σ∶Γ⇒Δ Γ⊢φ∶Ω validΔ))) (EP-SN ε∈EΔφ)))
  Δ⊢Λφδσ∶φ⊃ψ
Computable-Sub σ σ∶Γ⇒Δ (convR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ) validΔ = conv-E' (respects-conv (respects-osr SUB R-respects-sub) φ≃ψ) 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢δ∶φ validΔ) (ctxPR (substitution Γ⊢ψ∶Ω validΔ (subC-typed σ∶Γ⇒Δ)))
Computable-Sub σ σ∶Γ⇒Δ (refR Γ⊢M∶A) validΔ = ref-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢M∶A validΔ)
Computable-Sub σ σ∶Γ⇒Δ (⊃*R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = ⊃*-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢φ∶Ω validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ψ∶Ω validΔ)
Computable-Sub σ σ∶Γ⇒Δ (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) validΔ = univ-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢δ∶φ⊃ψ validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ε∶ψ⊃φ validΔ)
Computable-Sub σ σ∶Γ⇒Δ (plusR Γ⊢P∶φ≡ψ) validΔ = plus-EP (Computable-Sub σ σ∶Γ⇒Δ Γ⊢P∶φ≡ψ validΔ)
Computable-Sub σ σ∶Γ⇒Δ (minusR Γ⊢P∶φ≡ψ) validΔ = minus-EP (Computable-Sub σ σ∶Γ⇒Δ Γ⊢P∶φ≡ψ validΔ)
Computable-Sub σ {Δ = Δ} σ∶Γ⇒Δ (lllR {A = A} {B = B} {M = M} {N = N} {P = P} ΓAAe⊢P∶Mx≡Ny) validΔ = 
   let validΔAA : valid (Δ ,T A ,T A)
       validΔAA = ctxTR (ctxTR validΔ) in
   let ΔAAE⊢P∶Mx≡Ny : addpath Δ A ⊢ P ⟦ sub↑ -Path (sub↑ -Term (sub↑ -Term σ)) ⟧ ∶ appT (M ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT (N ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₁)
       ΔAAE⊢P∶Mx≡Ny = change-type 
                      (substitution ΓAAe⊢P∶Mx≡Ny (valid-addpath validΔ) 
                        (sub↑-typed (sub↑-typed (sub↑-typed (subC-typed σ∶Γ⇒Δ))))) 
                      (cong₂ (λ x y → appT x (var x₂) ≡〈 B 〉 appT y (var x₁)) (sub↑-upRep₃ M) (sub↑-upRep₃ N)) in
   func-EE 
   (lllR ΔAAE⊢P∶Mx≡Ny)
   (λ V Θ L L' Q ρ ρ∶Δ⇒RΘ L∈EΘA L'∈EΘA Q∈EΘL≡L' → 
     let validΘ : valid Θ
         validΘ = Context-Validity (E'-typed L∈EΘA) in
     let rep↑ρ∶apΔ⇒RapΘ : rep↑ _ (rep↑ _ (rep↑ _ ρ)) ∶ addpath Δ A ⇒R addpath Θ A
         rep↑ρ∶apΔ⇒RapΘ = rep↑-typed (rep↑-typed (rep↑-typed ρ∶Δ⇒RΘ)) in --TODO General lemma
     expand-EE 
       (subst₂ (EE Θ) 
         (cong₂ (λ x y → appT x L ≡〈 B 〉 appT y L') 
           (let open ≡-Reasoning in 
           begin
             M ⇑ ⇑ ⇑ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) • sub↑ -Path (sub↑ -Term (sub↑ -Term σ)) ⟧
           ≡⟨ sub-comp (M ⇑ ⇑ ⇑) ⟩
             M ⇑ ⇑ ⇑ ⟦ sub↑ -Path (sub↑ -Term (sub↑ -Term σ)) ⟧ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) ⟧
           ≡⟨ sub-congl (sub↑-upRep₃ M) ⟩
             M ⟦ σ ⟧ ⇑ ⇑ ⇑ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) ⟧
           ≡⟨ sub-compSR (M ⟦ σ ⟧ ⇑ ⇑ ⇑) ⟩
             M ⟦ σ ⟧ ⇑ ⇑ ⇑ 〈 rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) 〉 ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧
           ≡⟨ sub-congl (rep↑-upRep₃ (M ⟦ σ ⟧)) ⟩
             M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧
           ≡⟨ botsub-upRep₃ ⟩
             M ⟦ σ ⟧ 〈 ρ 〉
           ∎) 
           (let open ≡-Reasoning in 
           begin
             N ⇑ ⇑ ⇑ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) • sub↑ -Path (sub↑ -Term (sub↑ -Term σ)) ⟧
           ≡⟨ sub-comp (N ⇑ ⇑ ⇑) ⟩
             N ⇑ ⇑ ⇑ ⟦ sub↑ -Path (sub↑ -Term (sub↑ -Term σ)) ⟧ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) ⟧
           ≡⟨ sub-congl (sub↑-upRep₃ N) ⟩
             N ⟦ σ ⟧ ⇑ ⇑ ⇑ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) ⟧
           ≡⟨ sub-compSR (N ⟦ σ ⟧ ⇑ ⇑ ⇑) ⟩
             N ⟦ σ ⟧ ⇑ ⇑ ⇑ 〈 rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) 〉 ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧
           ≡⟨ sub-congl (rep↑-upRep₃ (N ⟦ σ ⟧)) ⟩
             N ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧
           ≡⟨ botsub-upRep₃ ⟩
             N ⟦ σ ⟧ 〈 ρ 〉
           ∎)) --TODO Common pattern
           (let open ≡-Reasoning in 
           begin
             P ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) • sub↑ -Path (sub↑ -Term (sub↑ -Term σ)) ⟧
           ≡⟨ sub-comp P ⟩
             P ⟦ sub↑ -Path (sub↑ -Term (sub↑ -Term σ)) ⟧ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) ⟧
           ≡⟨ sub-compSR (P ⟦ sub↑ -Path (sub↑ -Term (sub↑ -Term σ)) ⟧) ⟩
             P ⟦ sub↑ -Path (sub↑ -Term (sub↑ -Term σ)) ⟧ 〈 rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) 〉 ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧
           ∎) 
         (Computable-Sub 
           ((x₂:= L ,x₁:= L' ,x₀:= Q) •SR 
             rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) • 
             sub↑ -Path (sub↑ -Term (sub↑ -Term σ))) 
           (compC (compSRC 
                  (botsub₃C L∈EΘA L'∈EΘA Q∈EΘL≡L') 
                  rep↑ρ∶apΔ⇒RapΘ)
           (sub↑C (sub↑C (sub↑C σ∶Γ⇒Δ)))) 
           ΓAAe⊢P∶Mx≡Ny 
           validΘ))
       (app*R (E-typed L∈EΘA) (E-typed L'∈EΘA) 
         (lllR (change-type (weakening ΔAAE⊢P∶Mx≡Ny (valid-addpath validΘ) 
           rep↑ρ∶apΔ⇒RapΘ) 
         (cong₂ (λ x y → appT x (var x₂) ≡〈 B 〉 appT y (var x₁)) 
           (rep↑-upRep₃ (M ⟦ σ ⟧)) (rep↑-upRep₃ (N ⟦ σ ⟧)))))
         (EE-typed Q∈EΘL≡L')) 
       (βEkr (E'-SN L∈EΘA) (E'-SN L'∈EΘA) (E'-SN Q∈EΘL≡L')))
Computable-Sub σ σ∶Γ⇒Δ (app*R Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') validΔ = 
  app*-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢P∶M≡M' validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢Q∶N≡N' validΔ) 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢N∶A validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢N'∶A validΔ)
Computable-Sub σ σ∶Γ⇒Δ (convER Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') validΔ = 
  conv-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢P∶M≡N validΔ) 
    (conv-sub M≃M') (conv-sub N≃N') 
    (substitution Γ⊢M'∶A validΔ (subC-typed σ∶Γ⇒Δ)) (substitution Γ⊢N'∶A validΔ (subC-typed σ∶Γ⇒Δ))
--TODO Common pattern

--TODO Rename
computable-path-substitution U V τ σ σ' Γ Δ .(var x) ._ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (varR x _) _ = 
  τ∶σ∼σ' x
computable-path-substitution U V τ σ σ' Γ Δ .(app -bot out) .(ty Ω) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (⊥R x) validΔ = ref-EE (⊥-E validΔ)
computable-path-substitution U V τ σ σ' Γ Δ _ .(ty Ω) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = ⊃*-EE 
  (computable-path-substitution U V τ σ σ' Γ Δ _ (ty Ω) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢φ∶Ω validΔ) 
  (computable-path-substitution U V τ σ σ' Γ Δ _ (ty Ω) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢ψ∶Ω validΔ) 
computable-path-substitution U V τ σ σ' Γ Δ _ .(ty B) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (appR {N = N} {A} {B} Γ⊢M∶A⇒B Γ⊢N∶A) validΔ = 
  app*-EE 
  (computable-path-substitution U V τ σ σ' Γ Δ _ _ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢M∶A⇒B validΔ) 
  (computable-path-substitution U V τ σ σ' Γ Δ _ _ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢N∶A validΔ)
  (Computable-Sub σ (pathsubC-valid₁ {U} {V} {τ} {σ} {σ'} τ∶σ∼σ') Γ⊢N∶A validΔ)
  (Computable-Sub σ' (pathsubC-valid₂ {τ = τ} {σ} {σ = σ'} {Γ} {Δ} τ∶σ∼σ') Γ⊢N∶A validΔ)
computable-path-substitution U V τ σ σ' Γ Δ ._ ._ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (ΛR {A = A} {M = M} {B = B} Γ,A⊢M∶B) validΔ = 
  let validΔA : valid (Δ ,T A)
      validΔA = ctxTR validΔ in
  let validΔAA : valid (Δ ,T A ,T A)
      validΔAA = ctxTR validΔA in
  let validapΔ : valid (addpath Δ A)
      validapΔ = valid-addpath validΔ in
  func-EE 
  (lllR (convER 
    (path-substitution Γ,A⊢M∶B (pathsub↑-typed (pathsubC-typed τ∶σ∼σ') validΔ) 
    (sub↖-typed (subC-typed σ∶Γ⇒CΔ)) (sub↗-typed (subC-typed σ'∶Γ⇒CΔ)) 
    (valid-addpath validΔ)) (appR 
      (ΛR (weakening (weakening (weakening (substitution Γ,A⊢M∶B 
                                                         validΔA 
                                                         (sub↑-typed (subC-typed σ∶Γ⇒CΔ))) 
                                           validΔAA (rep↑-typed upRep-typed)) 
                                (ctxTR validΔAA) (rep↑-typed upRep-typed)) 
                     (ctxTR validapΔ) (rep↑-typed upRep-typed))) 
      (varR x₂ validapΔ))
    (appR (ΛR (weakening (weakening (weakening (substitution Γ,A⊢M∶B validΔA 
                                                             (sub↑-typed (subC-typed σ'∶Γ⇒CΔ))) 
                                               validΔAA (rep↑-typed upRep-typed)) 
                                    (ctxTR validΔAA) (rep↑-typed upRep-typed)) 
                         (ctxTR validapΔ) (rep↑-typed upRep-typed))) 
              (varR x₁ validapΔ)) 
    (sym-conv (osr-conv (redex (subst
                                  (R -appTerm
                                   (ΛT A
                                    ((((M ⟦ sub↑ -Term σ ⟧) 〈 rep↑ -Term upRep 〉) 〈 rep↑ -Term upRep 〉)
                                     〈 rep↑ -Term upRep 〉)
                                    ,, var x₂ ,, out))
                                  (sub↖-decomp M) βT)))) 
    (sym-conv (osr-conv (redex (subst
                                  (R -appTerm
                                   (ΛT A
                                    ((((M ⟦ sub↑ -Term σ' ⟧) 〈 rep↑ -Term upRep 〉) 〈 rep↑ -Term upRep
                                      〉)
                                     〈 rep↑ -Term upRep 〉)
                                    ,, var x₁ ,, out))
                                  (sub↗-decomp M) βT)))))) 
   (λ W Θ N N' Q ρ ρ∶Δ⇒RΘ N∈EΘA N'∈EΘA Q∈EΘN≡N' → 
   expand-EE (conv-EE
     (computable-path-substitution (U , -Term) W (extendPS (ρ •RP τ) Q) (extendSub (ρ •RS σ) N) (extendSub (ρ •RS σ') N') (Γ ,T A) Θ M (ty B) 
     (extendSubC (compRSC ρ∶Δ⇒RΘ σ∶Γ⇒CΔ) N∈EΘA) 
     (extendSubC (compRSC ρ∶Δ⇒RΘ σ'∶Γ⇒CΔ) N'∈EΘA) 
     (extendPSC (compRPC τ∶σ∼σ' ρ∶Δ⇒RΘ) Q∈EΘN≡N') Γ,A⊢M∶B (Context-Validity (E'-typed N∈EΘA)))
     (sym-conv (osr-conv (redex 
       (subst
          (R -appTerm (ΛT A ((M ⟦ sub↑ _ σ ⟧) 〈 rep↑ _ ρ 〉) ,, N ,, out)) 
          {!!}
          βT)))) 
     (sym-conv (osr-conv (redex 
       (subst
          (R -appTerm (ΛT A ((M ⟦ sub↑ _ σ' ⟧) 〈 rep↑ _ ρ 〉) ,, N' ,, out)) 
          {!!}
          βT)))) 
     {!!} {!!}) {!!} (subst (key-redex _) {!!} (βEkr {!!} {!!} {!!})))
\end{code}
}

\begin{proof}
The four parts are proved simultaneously by induction on derivations.  We give the details of
one case here, for part \ref{computable-path-sub} for the rule
\[ \infer{\Gamma \vdash \lambda x:A.M : A \rightarrow B}{\Gamma, x : A \vdash M : B} \]

We must prove that 
\[ \triplelambda e:a =_A a' . M \{ \tau : \sigma \sim \rho, x := e : a \sim a' \} \in E_\Delta(\lambda x:A.M[\sigma] =_{A \rightarrow B} \lambda x:A.M[\rho]) \enspace . \]
So let $\Theta \supseteq \Delta$; $N, N' \in E_\Theta(A)$; and $Q \in E_\Theta(N =_A N')$.  The induction hypothesis gives
\[ M \{ \tau , x := Q \} \in E_\Theta(M[\sigma, x:= N] =_B M [ \rho, x := N' ]) \enspace . \]
Applying Lemmas \ref{lm:expand-compute} and \ref{lm:conv-compute} gives
\[ (\triplelambda e:a =_A a' . M \{ \tau, x := e \})_{N N'} Q \in E_\Theta((\lambda x:A.M[\sigma]) N =_B (\lambda x:A.M[\rho]) N') \]
as required.
\end{proof}

\AgdaHide{
\begin{code}
{-computable-path-substitution .U V τ σ σ' .Γ Δ _ _ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (ΛR {U} {Γ} {A} {M} {B} Γ,A⊢M∶B) validΔ = 
  let validΔAA : valid (Δ ,T A ,T A)
      validΔAA = ctxTR (ctxTR validΔ) in
  let validΔAAE : valid (addpath Δ A)
      validΔAAE = ctxER (varR x₁ validΔAA) (varR x₀ validΔAA) in
  let σ∶Γ⇒Δ = subC-typed σ∶Γ⇒CΔ in
  let σ'∶Γ⇒Δ = subC-typed σ'∶Γ⇒CΔ in
  let sub↖σ-typed : sub↖ σ ∶ Γ ,T A ⇒ addpath Δ A
      sub↖σ-typed = sub↖-typed σ∶Γ⇒Δ in
  let sub↗σ'-typed : sub↗ σ' ∶ Γ ,T A ⇒ addpath Δ A
      sub↗σ'-typed = sub↗-typed σ'∶Γ⇒Δ in
  func-EE (lllR (convER (Path-substitution Γ,A⊢M∶B
                             (pathsub↑-typed (pathsubC-typed {τ = τ} {σ} {σ = σ'} {Γ} {Δ} τ∶σ∼σ')) sub↖σ-typed sub↗σ'-typed
                             validΔAAE)
                             (appR (ΛR (weakening {ρ = rep↑ _ upRep}
                                           {M = ((M ⟦ sub↑ _ σ ⟧) 〈 rep↑ _ upRep 〉) 〈 rep↑ _ upRep 〉} 
                                        (weakening {ρ = rep↑ _ upRep}
                                           {M = (M ⟦ sub↑ _ σ ⟧) 〈 rep↑ _ upRep 〉} 
                                        (weakening {ρ = rep↑ _ upRep} {M = M ⟦ sub↑ _ σ ⟧} 
                                        (substitution {σ = sub↑ -Term σ} {M = M} Γ,A⊢M∶B (ctxTR validΔ) 
                                          (sub↑-typed (subC-typed σ∶Γ⇒CΔ))) (ctxTR (ctxTR validΔ)) (rep↑-typed upRep-typed)) 
                                        (ctxTR (ctxTR (ctxTR validΔ))) 
                                        (rep↑-typed upRep-typed)) 
                           (ctxTR (ctxER (varR (↑ x₀) (ctxTR (ctxTR validΔ))) (varR x₀ (ctxTR (ctxTR validΔ))))) 
                           (rep↑-typed upRep-typed))) 
                           (varR x₂ (ctxER ((varR (↑ x₀) (ctxTR (ctxTR validΔ)))) (varR x₀ (ctxTR (ctxTR validΔ))))))  
                              (let stepA : addpath Δ A ,T A ⊢ M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 ∶ ty B
                                   stepA = weakening {U = V , -Term , -Term , -Term} {V = V , -Term , -Term , -Path , -Term} {ρ = rep↑ _ upRep} {Γ = Δ , ty A , ty A , ty A} {M = M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉} 
                                      (weakening {ρ = rep↑ _ upRep} {Γ = Δ , ty A , ty A}
                                         {M = (M ⟦ sub↑ _ σ' ⟧) 〈 rep↑ _ upRep 〉} 
                                      (weakening {ρ = rep↑ _ upRep} {M = M ⟦ sub↑ _ σ' ⟧} 
                                      (substitution {σ = sub↑ _ σ'} {M = M} 
                                      Γ,A⊢M∶B 
                                      (ctxTR validΔ) 
                                      (sub↑-typed σ'∶Γ⇒Δ))
                                      validΔAA 
                                      (rep↑-typed upRep-typed)) 
                                      (ctxTR validΔAA) 
                                      (rep↑-typed upRep-typed))
                                      (ctxTR validΔAAE)
                                      (rep↑-typed upRep-typed) in
                              let stepB : addpath Δ A ⊢ (ΛT A M) ⟦ σ' ⟧ ⇑ ⇑ ⇑ ∶ ty (A ⇛ B)
                                  stepB = ΛR stepA in
                              let stepC : addpath Δ A ⊢ var x₁ ∶ ty A
                                  stepC = varR x₁ validΔAAE in
                              let stepD : addpath Δ A ⊢ appT ((ΛT A M) ⟦ σ' ⟧ ⇑ ⇑ ⇑) (var x₁) ∶ ty B
                                  stepD = appR stepB stepC in
                              stepD)
                        (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M ⟦ σ ⟧) ⇑ ⇑ ⇑) (var x₂) ⇒ a) (let open ≡-Reasoning in
                           M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR rep↑ _ upRep •SR rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ ⟧) ⟩⟩
                           M ⟦ sub↑ _ σ ⟧ ⟦ x₀:= (var x₂) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₂) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep • sub↑ _ σ ⟧
                         ≡⟨ sub-congr M aux₃ ⟩
                           M ⟦ sub↖ σ ⟧
                           ∎) (redex ?)))) 
                         (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M ⟦ σ' ⟧) ⇑ ⇑ ⇑) (var x₁) ⇒ a) 
                         (let open ≡-Reasoning in
                           M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR rep↑ _ upRep •SR rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ' ⟧) ⟩⟩
                           M ⟦ sub↑ _ σ' ⟧ ⟦ x₀:= (var x₁) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₁) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep • sub↑ _ σ' ⟧
                         ≡⟨ sub-congr M aux₄ ⟩
                           M ⟦ sub↗ σ' ⟧
                           ∎) 
                         (redex ?))))))
    (λ W Θ N N' Q ρ ρ∶Δ⇒Θ N∈EΘA N'∈EΘA Q∈EΘN≡N' → 
    let validΘ : valid Θ
        validΘ = Context-Validity (E-typed N∈EΘA) in
    let σ₁ : Sub (U , -Term) W
        σ₁ = x₀:= N •SR rep↑ -Term ρ • sub↑ -Term σ in
    let σ₁∶Γ,A⇒Θ : σ₁ ∶ Γ ,T A ⇒C Θ
        σ₁∶Γ,A⇒Θ = compC (compSRC (botsubC N∈EΘA) (rep↑-typed ρ∶Δ⇒Θ)) (sub↑C σ∶Γ⇒CΔ) in
    let σ₂ : Sub (U , -Term) W
        σ₂ = x₀:= N' •SR rep↑ -Term ρ • sub↑ -Term σ' in
    let σ₂∶Γ,A⇒Θ : σ₂ ∶ Γ ,T A ⇒C Θ
        σ₂∶Γ,A⇒Θ = compC (compSRC (botsubC N'∈EΘA) (rep↑-typed ρ∶Δ⇒Θ)) (sub↑C σ'∶Γ⇒CΔ) in --REFACTOR Common pattern
    let ρ' = rep↑ -Path (rep↑ -Term (rep↑ -Term ρ)) in
    let step1 : x₀:= N • sub↑ -Term (ρ •RS σ) ∼ σ₁
        step1 = sub-trans (comp-congr sub↑-compRS) 
                  (assocRSSR {ρ = x₀:= N} {σ = rep↑ -Term ρ} {τ = sub↑ -Term σ}) in
    let step2 : x₀:= N' • sub↑ -Term (ρ •RS σ') ∼ σ₂
        step2 = sub-trans (comp-congr sub↑-compRS) 
                  (assocRSSR {ρ = x₀:= N'} {σ = rep↑ -Term ρ} {τ = sub↑ -Term σ'}) in
    let sub-rep-comp : ∀ (σ : Sub U V) (N : Term W) → M ⟦ x₀:= N •SR rep↑ _ ρ • sub↑ _ σ ⟧ ≡ M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ ρ 〉 ⟦ x₀:= N ⟧
        sub-rep-comp σ N = let open ≡-Reasoning in
             begin
               M ⟦ x₀:= N •SR rep↑ -Term ρ • sub↑ -Term σ ⟧
             ≡⟨ sub-comp M ⟩
               M ⟦ sub↑ -Term σ ⟧ ⟦ x₀:= N •SR rep↑ -Term ρ ⟧
             ≡⟨ sub-compSR (M ⟦ sub↑ -Term σ ⟧) ⟩
               M ⟦ sub↑ -Term σ ⟧ 〈 rep↑ -Term ρ 〉 ⟦ x₀:= N ⟧
             ∎ in
    let ih : EE Θ (M ⟦ σ₁ ⟧ ≡〈 B 〉 M ⟦ σ₂ ⟧) 
                  (M ⟦⟦ extendPS (ρ •RP τ) Q ∶ σ₁ ∼ σ₂ ⟧⟧)
        ih = (computable-path-substitution (U , -Term) W (extendPS (ρ •RP τ) Q) σ₁ σ₂ (Γ ,T A) Θ _ _ σ₁∶Γ,A⇒Θ σ₂∶Γ,A⇒Θ
             (change-ends {σ = x₀:= N' • sub↑ -Term (ρ •RS σ')} {σ' = σ₂} (extendPS-typedC (compRP-typedC {ρ = ρ} {τ} {σ} {σ'} τ∶σ∼σ' ρ∶Δ⇒Θ) 
               Q∈EΘN≡N')
                 step1 step2) Γ,A⊢M∶B validΘ) in
    let Δ,A⊢Mσ∶B : Δ ,T A ⊢ M ⟦ sub↑ _ σ ⟧ ∶ ty B
        Δ,A⊢Mσ∶B = substitution Γ,A⊢M∶B (ctxTR validΔ) (sub↑-typed σ∶Γ⇒Δ) in
    let Δ,A⊢Mσ'∶B : Δ ,T A ⊢ M ⟦ sub↑ _ σ' ⟧ ∶ ty B
        Δ,A⊢Mσ'∶B = substitution Γ,A⊢M∶B (ctxTR validΔ) (sub↑-typed σ'∶Γ⇒Δ) in
    let Θ,A⊢Mσ∶B : Θ ,T A ⊢ M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ ρ 〉 ∶ ty B
        Θ,A⊢Mσ∶B = weakening Δ,A⊢Mσ∶B (ctxTR validΘ) (rep↑-typed ρ∶Δ⇒Θ) in
    let Θ,A⊢Mσ'∶B : Θ ,T A ⊢ M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ ρ 〉 ∶ ty B
        Θ,A⊢Mσ'∶B = weakening Δ,A⊢Mσ'∶B (ctxTR validΘ) (rep↑-typed ρ∶Δ⇒Θ) in --TODO Common pattern
    let Θ⊢N∶A : Θ ⊢ N ∶ ty A
        Θ⊢N∶A = E-typed N∈EΘA in
    let Θ⊢N'∶A : Θ ⊢ N' ∶ ty A
        Θ⊢N'∶A = E-typed N'∈EΘA in
        expand-EE (conv-EE 
          (subst (EE Θ (M ⟦ σ₁ ⟧ ≡〈 B 〉 M ⟦ σSR ⟧)) (let open ≡-Reasoning in
          begin
            M ⟦⟦ extendPS (ρ •RP τ) Q ∶ σ₁ ∼
                 σSR ⟧⟧
          ≡⟨⟨ pathsub-cong M ∼∼-refl step1 step2 ⟩⟩
            M ⟦⟦ extendPS (ρ •RP τ) Q ∶ x₀:= N • sub↑ -Term (ρ •RS σ) ∼
                 x₀:= N' • sub↑ -Term (ρ •RS σ') ⟧⟧
          ≡⟨ pathsub-extendPS M ⟩
            M ⟦⟦ pathsub↑ (ρ •RP τ) ∶ sub↖ (ρ •RS σ) ∼ sub↗ (ρ •RS σ') ⟧⟧ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
          ≡⟨ sub-congl (pathsub-cong M pathsub↑-compRP sub↖-comp₁ sub↗-comp₁) ⟩
            M ⟦⟦ ρ' •RP pathsub↑ τ ∶ ρ' •RS sub↖ σ ∼ ρ' •RS sub↗ σ' ⟧⟧ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
          ≡⟨ sub-congl (pathsub-compRP M) ⟩
            (M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧) 〈 ρ' 〉 ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
          ∎) ih) 
          (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M) ⟦ σ ⟧ 〈 ρ 〉) N ⇒ a) (sym (sub-rep-comp σ N)) (redex ?)))) 
          (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M) ⟦ σ' ⟧ 〈 ρ 〉) N' ⇒ a) (sym (sub-rep-comp σ' N')) (redex ?)))) --REFACTOR Duplication
          (appR (ΛR Θ,A⊢Mσ∶B) Θ⊢N∶A) 
          (appR (ΛR Θ,A⊢Mσ'∶B) (E-typed N'∈EΘA)))
        (let step3 : addpath Δ A ⊢
                         M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧
                         ∶ M ⟦ sub↖ σ ⟧ ≡〈 B 〉 M ⟦ sub↗ σ' ⟧
             step3 = Path-substitution Γ,A⊢M∶B (pathsub↑-typed (pathsubC-typed {τ = τ} {σ} {σ'} {Γ} {Δ} τ∶σ∼σ')) 
                     sub↖σ-typed sub↗σ'-typed validΔAAE in
        let step4 : addpath Θ A ⊢
                    M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ 〈 ρ' 〉
                  ∶ M ⟦ sub↖ σ ⟧ 〈 ρ' 〉 ≡〈 B 〉 M ⟦ sub↗ σ' ⟧ 〈 ρ' 〉
            step4 = weakening step3 
                    (ctxER (varR x₁ (ctxTR (ctxTR validΘ)))
                    (varR x₀ (ctxTR (ctxTR validΘ))))
                    (rep↑-typed (rep↑-typed (rep↑-typed ρ∶Δ⇒Θ))) in
        let step5 : ∀ σ x → σ ∶ Γ ⇒ Δ → typeof x (addpath Θ A) ≡ ty A → addpath Θ A ⊢
                    appT ((ΛT A M) ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x) ∶ ty B
            step5 σ x σ∶Γ⇒Θ x∶A∈ΘA = appR 
                           (ΛR (subst (λ a → addpath Θ A ,T A ⊢ a ∶ ty B) 
                           (trans (sub-compRS M) (trans (rep-comp (M ⟦ sub↑ _ σ ⟧))
                           (trans (rep-comp (M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ ρ 〉)) 
                             (rep-comp (M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ ρ 〉 〈 rep↑ _ upRep 〉)))))
                         (substitution {σ = rep↑ _ upRep •R rep↑ _ upRep •R rep↑ _ upRep •R rep↑ _ ρ •RS sub↑ _ σ} Γ,A⊢M∶B 
                         (ctxTR (ctxER (varR x₁ (ctxTR (ctxTR validΘ))) (varR x₀ (ctxTR (ctxTR validΘ)))))
                         (compRS-typed
                            {ρ = rep↑ _ upRep •R rep↑ _ upRep •R rep↑ _ upRep •R rep↑ _ ρ}
                            {σ = sub↑ _ σ} 
                            (compR-typed {ρ = rep↑ _ upRep •R rep↑ _ upRep •R rep↑ _ upRep}
                              {σ = rep↑ _ ρ}
                              (compR-typed {ρ = rep↑ _ upRep •R rep↑ _ upRep} {σ = rep↑ _ upRep}
                                (compR-typed {ρ = rep↑ _ upRep} {σ = rep↑ _ upRep} (rep↑-typed upRep-typed) (rep↑-typed upRep-typed)) (rep↑-typed upRep-typed)) 
                            (rep↑-typed ρ∶Δ⇒Θ))
                         (sub↑-typed σ∶Γ⇒Θ)))))
                         (change-type (varR x (ctxER (varR x₁ (ctxTR (ctxTR validΘ))) (varR x₀ (ctxTR (ctxTR validΘ))))) x∶A∈ΘA) in --TODO Extract last line as lemma
             let step6 : addpath Θ A ⊢
                         M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ 〈 ρ' 〉
                         ∶ appT ((ΛT A M) ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT ((ΛT A M) ⟦ σ' ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x₁)
                 step6 = convER step4 (step5 σ x₂ σ∶Γ⇒Δ refl) (step5 σ' x₁ σ'∶Γ⇒Δ refl)
                         (subst (λ a → a ≃ appT (((ΛT A M ⟦ σ ⟧) 〈 ρ 〉) ⇑ ⇑ ⇑) (var x₂)) 
                         (let open ≡-Reasoning in
                           M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ ρ 〉 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ ρ 〉 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ ρ 〉 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ ρ 〉 〈 rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ ρ 〉 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR rep↑ _ upRep •SR rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ ρ 〉) ⟩⟩
                           M ⟦ sub↑ _ σ ⟧ 〈 rep↑ _ ρ 〉 ⟦ x₀:= (var x₂) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ ⟧) ⟩⟩
                           M ⟦ sub↑ _ σ ⟧ ⟦ x₀:= (var x₂) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ ρ ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₂) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ ρ • sub↑ _ σ ⟧
                         ≡⟨ sub-congr M aux ⟩
                           M ⟦ rep↑ _ (rep↑ _ (rep↑ _ ρ)) •RS sub↖ σ ⟧
                         ≡⟨ sub-compRS M ⟩ 
                           M ⟦ sub↖ σ ⟧ 〈 rep↑ _ (rep↑ _ (rep↑ _ ρ)) 〉
                           ∎)
                           (sym-conv (osr-conv (redex ?)))) 
                         (subst (λ a → a ≃ appT (((ΛT A M ⟦ σ' ⟧) 〈 ρ 〉) ⇑ ⇑ ⇑) (var x₁)) 
                           (let open ≡-Reasoning in 
                           M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ ρ 〉 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ ρ 〉 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ ρ 〉 〈 rep↑ _ upRep 〉 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ ρ 〉 〈 rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ ρ 〉 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR rep↑ _ upRep •SR rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ ρ 〉) ⟩⟩
                           M ⟦ sub↑ _ σ' ⟧ 〈 rep↑ _ ρ 〉 ⟦ x₀:= (var x₁) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ sub↑ _ σ' ⟧) ⟩⟩
                           M ⟦ sub↑ _ σ' ⟧ ⟦ x₀:= (var x₁) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ ρ ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₁) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ ρ • sub↑ _ σ' ⟧
                         ≡⟨ sub-congr M aux₂ ⟩
                           M ⟦ rep↑ _ (rep↑ _ (rep↑ _ ρ)) •RS sub↗ σ' ⟧
                         ≡⟨ sub-compRS M ⟩ 
                           M ⟦ sub↗ σ' ⟧ 〈 rep↑ _ (rep↑ _ (rep↑ _ ρ)) 〉
                           ∎)
                           (sym-conv (osr-conv (redex ?)))) in
      app*R (E-typed N∈EΘA) (E-typed N'∈EΘA) 
      (lllR step6) (EE-typed Q∈EΘN≡N'))
      ?) where
    aux : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} → 
        x₀:= (var x₂) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ ρ • sub↑ _ σ ∼ rep↑ _ (rep↑ _ (rep↑ _ ρ)) •RS sub↖ σ
    aux x₀ = refl
    aux {ρ = ρ} {σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₂) •SR rep↑ -Term upRep •SR rep↑ -Term upRep •SR
       rep↑ -Term upRep
       •SR rep↑ -Term ρ ⟧
      ≡⟨ sub-compSR (σ _ x ⇑) ⟩
        σ _ x ⇑ 〈 rep↑ _ ρ 〉 ⟦ x₀:= (var x₂) •SR rep↑ -Term upRep •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⟦ x₀:= (var x₂) •SR rep↑ -Term upRep •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x 〈 ρ 〉)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⟦ x₀:= (var x₂) •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x 〈 ρ 〉 ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ 〈 rep↑ -Term upRep 〉 ⟦ x₀:= (var x₂) ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) ⟧
      ≡⟨ botsub-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑
      ≡⟨⟨ rep↑-upRep₃ (σ _ x) ⟩⟩
        σ _ x ⇑ ⇑ ⇑ 〈 rep↑ _ (rep↑ _ (rep↑ _ ρ)) 〉
      ∎
    aux₂ : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} → 
        x₀:= (var x₁) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ ρ • sub↑ _ σ ∼ rep↑ _ (rep↑ _ (rep↑ _ ρ)) •RS sub↗ σ
    aux₂ x₀ = refl
    aux₂ {ρ = ρ} {σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₁) •SR rep↑ -Term upRep •SR rep↑ -Term upRep •SR
       rep↑ -Term upRep
       •SR rep↑ -Term ρ ⟧
      ≡⟨ sub-compSR (σ _ x ⇑) ⟩
        σ _ x ⇑ 〈 rep↑ _ ρ 〉 ⟦ x₀:= (var x₁) •SR rep↑ -Term upRep •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⟦ x₀:= (var x₁) •SR rep↑ -Term upRep •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x 〈 ρ 〉)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⟦ x₀:= (var x₁) •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x 〈 ρ 〉 ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ 〈 rep↑ -Term upRep 〉 ⟦ x₀:= (var x₁) ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) ⟧
      ≡⟨ botsub-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑
      ≡⟨⟨ rep↑-upRep₃ (σ _ x) ⟩⟩
        σ _ x ⇑ ⇑ ⇑ 〈 rep↑ _ (rep↑ _ (rep↑ _ ρ)) 〉
      ∎
    aux₃ : ∀ {U} {V} {σ : Sub U V} → 
        x₀:= (var x₂) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep • sub↑ _ σ ∼ sub↖ σ
    aux₃ x₀ = refl
    aux₃ {σ = σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₂) •SR rep↑ -Term upRep •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x ⇑) ⟩
        σ _ x ⇑ 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x)) ⟩
        σ _ x ⇑ ⇑ ⟦ x₀:= (var x₂) •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x  ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑ 〈 rep↑ -Term upRep 〉 ⟦ x₀:= (var x₂) ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x  ⇑ ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) ⟧
      ≡⟨ botsub-upRep (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑
      ∎
    aux₄ : ∀ {U} {V} {σ : Sub U V} → 
        x₀:= (var x₁) •SR rep↑ _ upRep •SR rep↑ _ upRep •SR rep↑ _ upRep • sub↑ _ σ ∼ sub↗ σ
    aux₄ x₀ = refl
    aux₄ {σ = σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₁) •SR rep↑ -Term upRep •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑) ⟩
        σ _ x  ⇑ 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x )) ⟩
        σ _ x  ⇑ ⇑ ⟦ x₀:= (var x₁) •SR rep↑ -Term upRep •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ 〈 rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x  ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) •SR rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑ 〈 rep↑ -Term upRep 〉 ⟦ x₀:= (var x₁) ⟧
      ≡⟨ sub-congl (rep↑-upRep (σ _ x  ⇑ ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) ⟧
      ≡⟨ botsub-upRep (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑
      ∎ -}
\end{code}
}

\begin{corollary}[Strong Normalization]
Every well-typed term, proof and path is strongly normalizing.
\end{corollary}

\begin{proof}
We apply the theorem with $\sigma$ the identity substitution.  The identity substitution is computable
by Lemma \ref{lm:var-compute}.
\end{proof}

%<*Strong-Normalization>
\begin{code}
Strong-Normalization : ∀ V K (Γ : Context V) 
  (M : Expression V (varKind K)) A → Γ ⊢ M ∶ A → SN M
\end{code}
%</Strong-Normalization>

\AgdaHide{
\begin{code}
Strong-Normalization V K Γ M A Γ⊢M∶A = E'-SN 
  (subst (E' Γ _) sub-idOp
  (Computable-Sub (idSub V) idSubC Γ⊢M∶A (Context-Validity Γ⊢M∶A)))
\end{code}
}

\begin{corollary}[Consistency]
There is no proof $\delta$ such that $\vdash \delta : \bot$.
\end{corollary}

\AgdaHide{
\begin{code}
postulate Consistency' : ∀ {M : Proof ∅} → SN M → 〈〉 ⊢ M ∶ ⊥ → Empty
-- Consistency' (SNI M SNM) ⊢M∶⊥ = {!!}
\end{code}
}

%<*Consistency>
\begin{code}
postulate Consistency : ∀ {M : Proof ∅} → 〈〉 ⊢ M ∶ ⊥ → Empty
\end{code}
%</Consistency>

\AgdaHide{
\begin{code}
-- Consistency = {!!}
\end{code}
}
