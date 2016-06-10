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
open import PHOPL.MainPropFinal
open import PHOPL.MainProp1
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

\begin{code}
postulate Computable-Sub : ∀ {U} {V} {K} (σ : Sub U V) {Γ} {Δ} 
                         {M : Expression U (varKind K)} {A} →
                         σ ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → E' Δ (A ⟦ σ ⟧) (M ⟦ σ ⟧)

postulate Computable-Path-Substitution : ∀ U V (τ : PathSub U V) σ σ' Γ Δ M A → σ ∶ Γ ⇒C Δ → σ' ∶ Γ ⇒C Δ → τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → 
                                       EE Δ (M ⟦ σ ⟧ ≡〈 yt A 〉 M ⟦ σ' ⟧) (M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧) 
\end{code}

\AgdaHide{
\begin{code}
{-Computable-Sub σ σ∶Γ⇒Δ (varR x validΓ) validΔ = σ∶Γ⇒Δ x
Computable-Sub {V = V} σ {Δ = Δ} σ∶Γ⇒Δ (appR Γ⊢M∶A⇛B Γ⊢N∶A) validΔ = 
  appT-E validΔ (Computable-Sub σ σ∶Γ⇒Δ Γ⊢M∶A⇛B validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢N∶A validΔ)
Computable-Sub σ σ∶Γ⇒Δ (ΛR {M = M} {B} Γ,A⊢M∶B) validΔ = 
  func-E (λ _ Θ ρ N validΘ ρ∶Δ⇒Θ N∈EΘA → 
    let MN∈EΘB = subst (E Θ B) (subrepsub M)
                 (Computable-Sub (x₀:= N •SR Rep↑ _ ρ • Sub↑ -Term σ) 
                 (compC (compSRC (botsubC N∈EΘA) 
                        (Rep↑-typed ρ∶Δ⇒Θ)) 
                 (Sub↑C σ∶Γ⇒Δ)) 
                 Γ,A⊢M∶B validΘ) in
    expand-E MN∈EΘB
      (appR (ΛR (Weakening (Substitution Γ,A⊢M∶B (ctxTR validΔ) (Sub↑-typed (subC-typed σ∶Γ⇒Δ))) 
                                                      (ctxTR validΘ) 
                                         (Rep↑-typed ρ∶Δ⇒Θ))) 
                (E-typed N∈EΘA)) 
      (βTkr (SNap' {Ops = substitution} R-respects-sub (E-SN B MN∈EΘB))))
Computable-Sub σ σ∶Γ⇒Δ (⊥R _) validΔ = ⊥-E validΔ
Computable-Sub σ σ∶Γ⇒Δ (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = ⊃-E 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢φ∶Ω validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ψ∶Ω validΔ)
Computable-Sub σ σ∶Γ⇒Δ (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) validΔ = appP-EP 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢δ∶φ⊃ψ validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ε∶φ validΔ)
Computable-Sub σ {Γ = Γ} {Δ = Δ} σ∶Γ⇒Δ (ΛPR {δ = δ} {φ} {ψ} Γ⊢φ∶Ω Γ,φ⊢δ∶ψ) validΔ = 
  let Δ⊢Λφδσ∶φ⊃ψ : Δ ⊢ (ΛP φ δ) ⟦ σ ⟧ ∶ φ ⟦ σ ⟧ ⊃ ψ ⟦ σ ⟧
      Δ⊢Λφδσ∶φ⊃ψ = Substitution {A = φ ⊃ ψ} (ΛPR Γ⊢φ∶Ω Γ,φ⊢δ∶ψ) validΔ (subC-typed σ∶Γ⇒Δ) in
  func-EP (λ W Θ ρ ε ρ∶Δ⇒Θ ε∈EΔφ → 
    let δε∈EΘψ : EP Θ (ψ ⟦ σ ⟧ 〈 ρ 〉) (δ ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= ε ⟧)
        δε∈EΘψ = subst₂ (EP Θ) (subrepbotsub-up ψ) (subrepsub δ) 
                 (Computable-Sub (x₀:= ε •SR Rep↑ _ ρ • Sub↑ _ σ) 
                 (compC (compSRC (botsubCP ε∈EΔφ) 
                        (Rep↑-typed ρ∶Δ⇒Θ)) 
                 (Sub↑C σ∶Γ⇒Δ)) Γ,φ⊢δ∶ψ (Context-Validity (EP-typed ε∈EΔφ))) in
    expand-EP δε∈EΘψ (appPR (Weakening Δ⊢Λφδσ∶φ⊃ψ (Context-Validity (EP-typed ε∈EΔφ)) ρ∶Δ⇒Θ) (EP-typed ε∈EΔφ))
      (βPkr (SNrep R-creates-rep (E-SN Ω (Computable-Sub σ σ∶Γ⇒Δ Γ⊢φ∶Ω validΔ))) (EP-SN ε∈EΔφ))) 
  Δ⊢Λφδσ∶φ⊃ψ
Computable-Sub σ σ∶Γ⇒Δ (convR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ) validΔ = conv-E' (respects-conv (respects-osr substitution R-respects-sub) φ≃ψ) 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢δ∶φ validΔ) (ctxPR (Substitution Γ⊢ψ∶Ω validΔ (subC-typed σ∶Γ⇒Δ)))
Computable-Sub σ σ∶Γ⇒Δ (refR Γ⊢M∶A) validΔ = ref-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢M∶A validΔ)
Computable-Sub σ σ∶Γ⇒Δ (⊃*R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = ⊃*-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢φ∶Ω validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ψ∶Ω validΔ)
Computable-Sub σ σ∶Γ⇒Δ (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) validΔ = univ-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢δ∶φ⊃ψ validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ε∶ψ⊃φ validΔ)
Computable-Sub σ σ∶Γ⇒Δ (plusR Γ⊢P∶φ≡ψ) validΔ = plus-EP (Computable-Sub σ σ∶Γ⇒Δ Γ⊢P∶φ≡ψ validΔ)
Computable-Sub σ σ∶Γ⇒Δ (minusR Γ⊢P∶φ≡ψ) validΔ = minus-EP (Computable-Sub σ σ∶Γ⇒Δ Γ⊢P∶φ≡ψ validΔ)
Computable-Sub σ σ∶Γ⇒Δ (lllR Γ⊢M∶A) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒Δ (app*R Γ⊢M∶A Γ⊢M∶A₁ Γ⊢M∶A₂ Γ⊢M∶A₃) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒Δ (convER Γ⊢M∶A Γ⊢M∶A₁ Γ⊢M∶A₂ M≃M' N≃N') validΔ = {!!}

--TODO Rename
Computable-Path-Substitution U V τ σ σ' Γ Δ .(var x) ._ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (varR x _) _ = 
  τ∶σ∼σ' x
Computable-Path-Substitution U V τ σ σ' Γ Δ .(app -bot out) .(ty Ω) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (⊥R x) validΔ = ref-EE (⊥-E validΔ)
Computable-Path-Substitution U V τ σ σ' Γ Δ _ .(ty Ω) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = ⊃*-EE 
  (Computable-Path-Substitution U V τ σ σ' Γ Δ _ (ty Ω) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢φ∶Ω validΔ) 
  (Computable-Path-Substitution U V τ σ σ' Γ Δ _ (ty Ω) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢ψ∶Ω validΔ) 
Computable-Path-Substitution U V τ σ σ' Γ Δ _ .(ty B) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (appR {N = N} {A} {B} Γ⊢M∶A⇒B Γ⊢N∶A) validΔ = 
  app*-EE 
  (Computable-Path-Substitution U V τ σ σ' Γ Δ _ _ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢M∶A⇒B validΔ) 
  (Computable-Path-Substitution U V τ σ σ' Γ Δ _ _ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢N∶A validΔ)
  (Computable-Substitution U V σ Γ Δ N A (pathsubC-valid₁ {U} {V} {τ} {σ} {σ'} τ∶σ∼σ') Γ⊢N∶A refl validΔ)
  (Computable-Substitution U V σ' Γ Δ N A (pathsubC-valid₂ {τ = τ} {σ} {σ = σ'} {Γ} {Δ} τ∶σ∼σ') Γ⊢N∶A refl validΔ)-}
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
{-Computable-Path-Substitution .U V τ σ σ' .Γ Δ _ _ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (ΛR {U} {Γ} {A} {M} {B} Γ,A⊢M∶B) validΔ = 
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
  func-EE (lllR (convER (Path-Substitution Γ,A⊢M∶B
                             (pathsub↑-typed (pathsubC-typed {τ = τ} {σ} {σ = σ'} {Γ} {Δ} τ∶σ∼σ')) sub↖σ-typed sub↗σ'-typed
                             validΔAAE)
                             (appR (ΛR (Weakening {ρ = Rep↑ _ upRep}
                                           {M = ((M ⟦ Sub↑ _ σ ⟧) 〈 Rep↑ _ upRep 〉) 〈 Rep↑ _ upRep 〉} 
                                        (Weakening {ρ = Rep↑ _ upRep}
                                           {M = (M ⟦ Sub↑ _ σ ⟧) 〈 Rep↑ _ upRep 〉} 
                                        (Weakening {ρ = Rep↑ _ upRep} {M = M ⟦ Sub↑ _ σ ⟧} 
                                        (Substitution {σ = Sub↑ -Term σ} {M = M} Γ,A⊢M∶B (ctxTR validΔ) 
                                          (Sub↑-typed (subC-typed σ∶Γ⇒CΔ))) (ctxTR (ctxTR validΔ)) (Rep↑-typed upRep-typed)) 
                                        (ctxTR (ctxTR (ctxTR validΔ))) 
                                        (Rep↑-typed upRep-typed)) 
                           (ctxTR (ctxER (varR (↑ x₀) (ctxTR (ctxTR validΔ))) (varR x₀ (ctxTR (ctxTR validΔ))))) 
                           (Rep↑-typed upRep-typed))) 
                           (varR x₂ (ctxER ((varR (↑ x₀) (ctxTR (ctxTR validΔ)))) (varR x₀ (ctxTR (ctxTR validΔ))))))  
                              (let stepA : addpath Δ A ,T A ⊢ M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ∶ ty B
                                   stepA = Weakening {U = V , -Term , -Term , -Term} {V = V , -Term , -Term , -Path , -Term} {ρ = Rep↑ _ upRep} {Γ = Δ , ty A , ty A , ty A} {M = M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉} 
                                      (Weakening {ρ = Rep↑ _ upRep} {Γ = Δ , ty A , ty A}
                                         {M = (M ⟦ Sub↑ _ σ' ⟧) 〈 Rep↑ _ upRep 〉} 
                                      (Weakening {ρ = Rep↑ _ upRep} {M = M ⟦ Sub↑ _ σ' ⟧} 
                                      (Substitution {σ = Sub↑ _ σ'} {M = M} 
                                      Γ,A⊢M∶B 
                                      (ctxTR validΔ) 
                                      (Sub↑-typed σ'∶Γ⇒Δ))
                                      validΔAA 
                                      (Rep↑-typed upRep-typed)) 
                                      (ctxTR validΔAA) 
                                      (Rep↑-typed upRep-typed))
                                      (ctxTR validΔAAE)
                                      (Rep↑-typed upRep-typed) in
                              let stepB : addpath Δ A ⊢ (ΛT A M) ⟦ σ' ⟧ ⇑ ⇑ ⇑ ∶ ty (A ⇛ B)
                                  stepB = ΛR stepA in
                              let stepC : addpath Δ A ⊢ var x₁ ∶ ty A
                                  stepC = varR x₁ validΔAAE in
                              let stepD : addpath Δ A ⊢ appT ((ΛT A M) ⟦ σ' ⟧ ⇑ ⇑ ⇑) (var x₁) ∶ ty B
                                  stepD = appR stepB stepC in
                              stepD)
                        (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M ⟦ σ ⟧) ⇑ ⇑ ⇑) (var x₂) ⇒ a) (let open ≡-Reasoning in
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR Rep↑ _ upRep •SR Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ ⟧) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ ⟦ x₀:= (var x₂) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₂) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep • Sub↑ _ σ ⟧
                         ≡⟨ sub-congr M aux₃ ⟩
                           M ⟦ sub↖ σ ⟧
                           ∎) (redex ?)))) 
                         (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M ⟦ σ' ⟧) ⇑ ⇑ ⇑) (var x₁) ⇒ a) 
                         (let open ≡-Reasoning in
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR Rep↑ _ upRep •SR Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ' ⟧) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ ⟦ x₀:= (var x₁) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₁) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep • Sub↑ _ σ' ⟧
                         ≡⟨ sub-congr M aux₄ ⟩
                           M ⟦ sub↗ σ' ⟧
                           ∎) 
                         (redex ?))))))
    (λ W Θ N N' Q ρ ρ∶Δ⇒Θ N∈EΘA N'∈EΘA Q∈EΘN≡N' → 
    let validΘ : valid Θ
        validΘ = Context-Validity (E-typed N∈EΘA) in
    let σ₁ : Sub (U , -Term) W
        σ₁ = x₀:= N •SR Rep↑ -Term ρ • Sub↑ -Term σ in
    let σ₁∶Γ,A⇒Θ : σ₁ ∶ Γ ,T A ⇒C Θ
        σ₁∶Γ,A⇒Θ = compC (compSRC (botsubC N∈EΘA) (Rep↑-typed ρ∶Δ⇒Θ)) (Sub↑C σ∶Γ⇒CΔ) in
    let σ₂ : Sub (U , -Term) W
        σ₂ = x₀:= N' •SR Rep↑ -Term ρ • Sub↑ -Term σ' in
    let σ₂∶Γ,A⇒Θ : σ₂ ∶ Γ ,T A ⇒C Θ
        σ₂∶Γ,A⇒Θ = compC (compSRC (botsubC N'∈EΘA) (Rep↑-typed ρ∶Δ⇒Θ)) (Sub↑C σ'∶Γ⇒CΔ) in --REFACTOR Common pattern
    let ρ' = Rep↑ -Path (Rep↑ -Term (Rep↑ -Term ρ)) in
    let step1 : x₀:= N • Sub↑ -Term (ρ •RS σ) ∼ σ₁
        step1 = sub-trans (comp-congr Sub↑-compRS) 
                  (assocRSSR {ρ = x₀:= N} {σ = Rep↑ -Term ρ} {τ = Sub↑ -Term σ}) in
    let step2 : x₀:= N' • Sub↑ -Term (ρ •RS σ') ∼ σ₂
        step2 = sub-trans (comp-congr Sub↑-compRS) 
                  (assocRSSR {ρ = x₀:= N'} {σ = Rep↑ -Term ρ} {τ = Sub↑ -Term σ'}) in
    let sub-rep-comp : ∀ (σ : Sub U V) (N : Term W) → M ⟦ x₀:= N •SR Rep↑ _ ρ • Sub↑ _ σ ⟧ ≡ M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= N ⟧
        sub-rep-comp σ N = let open ≡-Reasoning in
             begin
               M ⟦ x₀:= N •SR Rep↑ -Term ρ • Sub↑ -Term σ ⟧
             ≡⟨ sub-comp M ⟩
               M ⟦ Sub↑ -Term σ ⟧ ⟦ x₀:= N •SR Rep↑ -Term ρ ⟧
             ≡⟨ sub-compSR (M ⟦ Sub↑ -Term σ ⟧) ⟩
               M ⟦ Sub↑ -Term σ ⟧ 〈 Rep↑ -Term ρ 〉 ⟦ x₀:= N ⟧
             ∎ in
    let ih : EE Θ (M ⟦ σ₁ ⟧ ≡〈 B 〉 M ⟦ σ₂ ⟧) 
                  (M ⟦⟦ extendPS (ρ •RP τ) Q ∶ σ₁ ∼ σ₂ ⟧⟧)
        ih = (Computable-Path-Substitution (U , -Term) W (extendPS (ρ •RP τ) Q) σ₁ σ₂ (Γ ,T A) Θ _ _ σ₁∶Γ,A⇒Θ σ₂∶Γ,A⇒Θ
             (change-ends {σ = x₀:= N' • Sub↑ -Term (ρ •RS σ')} {σ' = σ₂} (extendPS-typedC (compRP-typedC {ρ = ρ} {τ} {σ} {σ'} τ∶σ∼σ' ρ∶Δ⇒Θ) 
               Q∈EΘN≡N')
                 step1 step2) Γ,A⊢M∶B validΘ) in
    let Δ,A⊢Mσ∶B : Δ ,T A ⊢ M ⟦ Sub↑ _ σ ⟧ ∶ ty B
        Δ,A⊢Mσ∶B = Substitution Γ,A⊢M∶B (ctxTR validΔ) (Sub↑-typed σ∶Γ⇒Δ) in
    let Δ,A⊢Mσ'∶B : Δ ,T A ⊢ M ⟦ Sub↑ _ σ' ⟧ ∶ ty B
        Δ,A⊢Mσ'∶B = Substitution Γ,A⊢M∶B (ctxTR validΔ) (Sub↑-typed σ'∶Γ⇒Δ) in
    let Θ,A⊢Mσ∶B : Θ ,T A ⊢ M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 ∶ ty B
        Θ,A⊢Mσ∶B = Weakening Δ,A⊢Mσ∶B (ctxTR validΘ) (Rep↑-typed ρ∶Δ⇒Θ) in
    let Θ,A⊢Mσ'∶B : Θ ,T A ⊢ M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 ∶ ty B
        Θ,A⊢Mσ'∶B = Weakening Δ,A⊢Mσ'∶B (ctxTR validΘ) (Rep↑-typed ρ∶Δ⇒Θ) in --TODO Common pattern
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
            M ⟦⟦ extendPS (ρ •RP τ) Q ∶ x₀:= N • Sub↑ -Term (ρ •RS σ) ∼
                 x₀:= N' • Sub↑ -Term (ρ •RS σ') ⟧⟧
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
             step3 = Path-Substitution Γ,A⊢M∶B (pathsub↑-typed (pathsubC-typed {τ = τ} {σ} {σ'} {Γ} {Δ} τ∶σ∼σ')) 
                     sub↖σ-typed sub↗σ'-typed validΔAAE in
        let step4 : addpath Θ A ⊢
                    M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ 〈 ρ' 〉
                  ∶ M ⟦ sub↖ σ ⟧ 〈 ρ' 〉 ≡〈 B 〉 M ⟦ sub↗ σ' ⟧ 〈 ρ' 〉
            step4 = Weakening step3 
                    (ctxER (varR x₁ (ctxTR (ctxTR validΘ)))
                    (varR x₀ (ctxTR (ctxTR validΘ))))
                    (Rep↑-typed (Rep↑-typed (Rep↑-typed ρ∶Δ⇒Θ))) in
        let step5 : ∀ σ x → σ ∶ Γ ⇒ Δ → typeof x (addpath Θ A) ≡ ty A → addpath Θ A ⊢
                    appT ((ΛT A M) ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x) ∶ ty B
            step5 σ x σ∶Γ⇒Θ x∶A∈ΘA = appR 
                           (ΛR (subst (λ a → addpath Θ A ,T A ⊢ a ∶ ty B) 
                           (trans (sub-compRS M) (trans (rep-comp (M ⟦ Sub↑ _ σ ⟧))
                           (trans (rep-comp (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉)) 
                             (rep-comp (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉)))))
                         (Substitution {σ = Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ ρ •RS Sub↑ _ σ} Γ,A⊢M∶B 
                         (ctxTR (ctxER (varR x₁ (ctxTR (ctxTR validΘ))) (varR x₀ (ctxTR (ctxTR validΘ)))))
                         (compRS-typed
                            {ρ = Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ ρ}
                            {σ = Sub↑ _ σ} 
                            (compR-typed {ρ = Rep↑ _ upRep •R Rep↑ _ upRep •R Rep↑ _ upRep}
                              {σ = Rep↑ _ ρ}
                              (compR-typed {ρ = Rep↑ _ upRep •R Rep↑ _ upRep} {σ = Rep↑ _ upRep}
                                (compR-typed {ρ = Rep↑ _ upRep} {σ = Rep↑ _ upRep} (Rep↑-typed upRep-typed) (Rep↑-typed upRep-typed)) (Rep↑-typed upRep-typed)) 
                            (Rep↑-typed ρ∶Δ⇒Θ))
                         (Sub↑-typed σ∶Γ⇒Θ)))))
                         (change-type (varR x (ctxER (varR x₁ (ctxTR (ctxTR validΘ))) (varR x₀ (ctxTR (ctxTR validΘ))))) x∶A∈ΘA) in --TODO Extract last line as lemma
             let step6 : addpath Θ A ⊢
                         M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ 〈 ρ' 〉
                         ∶ appT ((ΛT A M) ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT ((ΛT A M) ⟦ σ' ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x₁)
                 step6 = convER step4 (step5 σ x₂ σ∶Γ⇒Δ refl) (step5 σ' x₁ σ'∶Γ⇒Δ refl)
                         (subst (λ a → a ≃ appT (((ΛT A M ⟦ σ ⟧) 〈 ρ 〉) ⇑ ⇑ ⇑) (var x₂)) 
                         (let open ≡-Reasoning in
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR Rep↑ _ upRep •SR Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= (var x₂) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ ⟧) ⟩⟩
                           M ⟦ Sub↑ _ σ ⟧ ⟦ x₀:= (var x₂) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ ρ ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₂) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ ρ • Sub↑ _ σ ⟧
                         ≡⟨ sub-congr M aux ⟩
                           M ⟦ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) •RS sub↖ σ ⟧
                         ≡⟨ sub-compRS M ⟩ 
                           M ⟦ sub↖ σ ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉
                           ∎)
                           (sym-conv (osr-conv (redex ?)))) 
                         (subst (λ a → a ≃ appT (((ΛT A M ⟦ σ' ⟧) 〈 ρ 〉) ⇑ ⇑ ⇑) (var x₁)) 
                           (let open ≡-Reasoning in 
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR Rep↑ _ upRep •SR Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= (var x₁) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ Sub↑ _ σ' ⟧) ⟩⟩
                           M ⟦ Sub↑ _ σ' ⟧ ⟦ x₀:= (var x₁) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ ρ ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₁) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ ρ • Sub↑ _ σ' ⟧
                         ≡⟨ sub-congr M aux₂ ⟩
                           M ⟦ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) •RS sub↗ σ' ⟧
                         ≡⟨ sub-compRS M ⟩ 
                           M ⟦ sub↗ σ' ⟧ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉
                           ∎)
                           (sym-conv (osr-conv (redex ?)))) in
      app*R (E-typed N∈EΘA) (E-typed N'∈EΘA) 
      (lllR step6) (EE-typed Q∈EΘN≡N'))
      ?) where
    aux : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} → 
        x₀:= (var x₂) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ ρ • Sub↑ _ σ ∼ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) •RS sub↖ σ
    aux x₀ = refl
    aux {ρ = ρ} {σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₂) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep •SR
       Rep↑ -Term upRep
       •SR Rep↑ -Term ρ ⟧
      ≡⟨ sub-compSR (σ _ x ⇑) ⟩
        σ _ x ⇑ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= (var x₂) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⟦ x₀:= (var x₂) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x 〈 ρ 〉)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⟦ x₀:= (var x₂) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x 〈 ρ 〉 ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ 〈 Rep↑ -Term upRep 〉 ⟦ x₀:= (var x₂) ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) ⟧
      ≡⟨ botsub-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑
      ≡⟨⟨ Rep↑-upRep₃ (σ _ x) ⟩⟩
        σ _ x ⇑ ⇑ ⇑ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉
      ∎
    aux₂ : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} → 
        x₀:= (var x₁) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ ρ • Sub↑ _ σ ∼ Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) •RS sub↗ σ
    aux₂ x₀ = refl
    aux₂ {ρ = ρ} {σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₁) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep •SR
       Rep↑ -Term upRep
       •SR Rep↑ -Term ρ ⟧
      ≡⟨ sub-compSR (σ _ x ⇑) ⟩
        σ _ x ⇑ 〈 Rep↑ _ ρ 〉 ⟦ x₀:= (var x₁) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⟦ x₀:= (var x₁) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x 〈 ρ 〉)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⟦ x₀:= (var x₁) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x 〈 ρ 〉 ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ 〈 Rep↑ -Term upRep 〉 ⟦ x₀:= (var x₁) ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) ⟧
      ≡⟨ botsub-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑
      ≡⟨⟨ Rep↑-upRep₃ (σ _ x) ⟩⟩
        σ _ x ⇑ ⇑ ⇑ 〈 Rep↑ _ (Rep↑ _ (Rep↑ _ ρ)) 〉
      ∎
    aux₃ : ∀ {U} {V} {σ : Sub U V} → 
        x₀:= (var x₂) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep • Sub↑ _ σ ∼ sub↖ σ
    aux₃ x₀ = refl
    aux₃ {σ = σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₂) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x ⇑) ⟩
        σ _ x ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x)) ⟩
        σ _ x ⇑ ⇑ ⟦ x₀:= (var x₂) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₂) •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x  ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑ 〈 Rep↑ -Term upRep 〉 ⟦ x₀:= (var x₂) ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x  ⇑ ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) ⟧
      ≡⟨ botsub-upRep (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑
      ∎
    aux₄ : ∀ {U} {V} {σ : Sub U V} → 
        x₀:= (var x₁) •SR Rep↑ _ upRep •SR Rep↑ _ upRep •SR Rep↑ _ upRep • Sub↑ _ σ ∼ sub↗ σ
    aux₄ x₀ = refl
    aux₄ {σ = σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₁) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑) ⟩
        σ _ x  ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x )) ⟩
        σ _ x  ⇑ ⇑ ⟦ x₀:= (var x₁) •SR Rep↑ -Term upRep •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ 〈 Rep↑ _ upRep 〉 ⟦ x₀:= (var x₁) •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x  ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) •SR Rep↑ -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑ 〈 Rep↑ -Term upRep 〉 ⟦ x₀:= (var x₁) ⟧
      ≡⟨ sub-congl (Rep↑-upRep (σ _ x  ⇑ ⇑)) ⟩
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

\begin{code}
postulate Strong-Normalization : ∀ V K (Γ : Context V) 
                               (M : Expression V (varKind K)) A → Γ ⊢ M ∶ A → SN M
\end{code}

\AgdaHide{
\begin{code}
{-Strong-Normalization V -Proof Γ δ φ Γ⊢δ∶φ = EP-SN 
  (subst (EP Γ _) sub-idOp
  (Computable-Proof-Substitution V V (idSub V) Γ Γ δ φ idSubC Γ⊢δ∶φ (Context-Validity Γ⊢δ∶φ)))
Strong-Normalization V -Term Γ M (app (-ty A) out) Γ⊢M∶A = E-SN A
  (subst (E Γ A) sub-idOp 
  (Computable-Substitution V V (idSub V) Γ Γ M A idSubC Γ⊢M∶A (Context-Validity Γ⊢M∶A)))
Strong-Normalization V -Path Γ P E Γ⊢P∶E = EE-SN E 
  (substSR (EE Γ) sub-idOp sub-idOp
  (Computable-Path-SubstitutionRS V V (idSub V) Γ Γ P E idSubC Γ⊢P∶E (Context-Validity Γ⊢P∶E)))-}
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

\begin{code}
postulate Consistency : ∀ {M : Proof ∅} → 〈〉 ⊢ M ∶ ⊥ → Empty
\end{code}

\AgdaHide{
\begin{code}
-- Consistency = {!!}
\end{code}
}