\AgdaHide{
\begin{code}
module PHOPL.SubC where
open import Data.Nat
open import Data.Fin
open import Data.List
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Red
open import PHOPL.Rules
open import PHOPL.Meta
open import PHOPL.Computable
open import PHOPL.PathSub
open import PHOPL.KeyRedex2
\end{code}
}

Let us say that a substitution $\sigma : \Gamma \Rightarrow \Delta$ is \emph{computable}
iff, for all $z : T \in \Gamma$, we have $\sigma(z) \in E\Delta(T[\sigma])$.

\begin{code}
_∶_⇒C_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set
_∶_⇒C_ {U} {V} σ Γ Δ = ∀ {K} (x : Var U K) → E' {V} Δ ((typeof x Γ) ⟦ σ ⟧) (σ _ x)
\end{code}

\AgdaHide{
\begin{code}
postulate subC-typed : ∀ {U} {V} {σ : Sub U V} {Γ : Context U} {Δ : Context V} →
                     σ ∶ Γ ⇒C Δ → σ ∶ Γ ⇒ Δ

postulate subC-cong : ∀ {U} {V} {σ τ : Sub U V} {Γ} {Δ} →
                    σ ∶ Γ ⇒C Δ → σ ∼ τ → τ ∶ Γ ⇒C Δ

postulate change-codC : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} →
                     σ ∶ Γ ⇒C Δ → Δ ≡ Δ' → σ ∶ Γ ⇒C Δ'
\end{code}
}

\begin{lemma}
\begin{enumerate}
\item
The identity substitution is computable.

\begin{code}
idSubC : ∀ {V} {Γ : Context V} → idSub V ∶ Γ ⇒C Γ
\end{code}

\AgdaHide{
\begin{code}
idSubC {V} {Γ} x = subst (λ a → E' Γ a (var x)) (sym sub-idOp) var-E'
\end{code}
}

\item
The computable substitutions are closed under composition.

\begin{code}
postulate compC : ∀ {U} {V} {W} {ρ : Sub V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                ρ ∶ Δ ⇒C Θ → σ ∶ Γ ⇒C Δ → ρ • σ ∶ Γ ⇒C Θ
\end{code}

\AgdaHide{
\begin{code}
postulate compRSC : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                 ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒C Δ → ρ •RS σ ∶ Γ ⇒C Θ

postulate compSRC : ∀ {U} {V} {W} {σ : Sub V W} {ρ : Rep U V} {Γ} {Δ} {Θ} →
                 σ ∶ Δ ⇒C Θ → ρ ∶ Γ ⇒R Δ → σ •SR ρ ∶ Γ ⇒C Θ
\end{code}
}

\item
If $\sigma$ is computable, then so is $(\sigma , K)$.

\begin{code}
postulate liftSubC : ∀ {U} {V} {σ : Sub U V} {K} {Γ} {Δ} {A} →
                    σ ∶ Γ ⇒C Δ → liftSub K σ ∶ (Γ , A) ⇒C (Δ , A ⟦ σ ⟧)
\end{code}

\item
If $M \in E_\Gamma(A)$ then $(x := M) : (Γ , x : A) \rightarrow_C \Gamma$.

\begin{code}
postulate botsubC : ∀ {V K} {Γ : Context V} {A : Expression V (parent K)} {M : Expression V (varKind K)} →
                    E' Γ A M → x₀:= M ∶ (Γ , A) ⇒C Γ
\end{code}

\AgdaHide{
\begin{code}
postulate botsub₃C : ∀ {V} {Γ : Context V} {A} {M} {N} {P} →
                   E Γ A M → E Γ A N → EE Γ (M ≡〈 A 〉 N) P →
                   (x₂:= M ,x₁:= N ,x₀:= P) ∶ Γ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀ ⇒C Γ
\end{code}
}
\item
If $\sigma : \Gamma \Rightarrow_C \Delta$ and $M \in E_\Delta(A)$ then $(\sigma , x := M) : (\Gamma , x : A) \Rightarrow_C \Delta$.

\begin{code}
postulate extendSubC : ∀ {U} {V} {σ : Sub U V} {M : Term V} {Γ} {Δ} {A} →
                          σ ∶ Γ ⇒C Δ → E Δ A M → extendSub σ M ∶ Γ ,T A ⇒C Δ
\end{code}
\end{enumerate}
\end{lemma}

Let us say that a path substitution $\tau : \rho \sim \sigma : \Gamma \Rightarrow \Delta$ is
\emph{computable} iff, for all $x : A \in \Gamma$, we have $\tau(x) \in E_\Delta(\rho(x) =_A \sigma(x))$.

\begin{code}
_∶_∼_∶_⇒C_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ = ∀ x → EE Δ (ρ _ x ≡〈 typeof' x Γ 〉 σ _ x) (τ x)
\end{code}

\AgdaHide{
\begin{code}
postulate pathsubC-typed : ∀ {U} {V} {τ : PathSub U V} ρ σ {Γ} {Δ} → 
                     τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ

postulate pathsubC-valid₁ : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} →
                          τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → ρ ∶ Γ ⇒C Δ

postulate pathsubC-valid₂ : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} →
                          τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → σ ∶ Γ ⇒C Δ

postulate change-ends : ∀ {U} {V} {τ : PathSub U V} {ρ} {ρ'} {σ} {σ'} {Γ} {Δ} → 
                      τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → ρ ∼ ρ' → σ ∼ σ' → τ ∶ ρ' ∼ σ' ∶ Γ ⇒C Δ
\end{code}
}

\begin{lemma}
\item
If $\tau : \rho \sim \sigma : \Gamma \Rightarrow \Delta$ and $Q \in E_\Delta(N =_A N')$ then $(\tau, x := Q) : (\rho , x := N) \sim (\sigma , x := N') : (\Gamma , x : A) \Rightarrow \Delta$.

\begin{code}
postulate extendPSC : ∀ {U} {V} {τ : PathSub U V} {ρ σ : Sub U V} {Γ : Context U} {Δ : Context V} {A : Type} {Q : Path V} {N N' : Term V} →
                         τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → EE Δ (N ≡〈 A 〉 N') Q → extendPS τ Q ∶ extendSub ρ N ∼ extendSub σ N' ∶ Γ ,T A ⇒C Δ
\end{code}

\AgdaHide{
\begin{code}
postulate compRPC : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} {σ} {σ'} {Γ} {Δ} {Θ} →
                         τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → ρ ∶ Δ ⇒R Θ → ρ •RP τ ∶ ρ •RS σ ∼ ρ •RS σ' ∶ Γ ⇒C Θ

APP*-rep : ∀ {U V n} MM {NN : snocVec (Term U) n} {P QQ} {ρ : Rep U V} →
  (APP* MM NN P QQ) 〈 ρ 〉 ≡ APP* (snocVec-rep MM ρ) (snocVec-rep NN ρ) (P 〈 ρ 〉) (snocVec-rep QQ ρ)
APP*-rep [] {[]} {QQ = []} = refl
APP*-rep (MM snoc M) {NN snoc N} {QQ = QQ snoc Q} {ρ = ρ} = 
  cong (λ x → app* (M 〈 ρ 〉) (N 〈 ρ 〉) x (Q 〈 ρ 〉)) (APP*-rep MM)

private pre-wte+-computeP : ∀ {m} {n} {V} {Γ : Context V} {S} {L₁ : Leaves V S}
                          {MM NN : snocVec (Term V) m} {P L L' Q RR} {εε : snocVec (Proof V) n} {A} →
                          computeP Γ L₁ (APPP (plus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR)) εε) →
                          valid Γ → SN L → SN L' → SN Q →
                          computeP Γ L₁ (APPP (plus (APP* MM NN (app* L L' (λλλ A P) Q) RR)) εε)
pre-wte+-computeP {L₁ = neutral x} {MM} {NN} {P} {L} {L'} {Q} {RR} {εε} computePRRεε validΓ SNL SNL' SNQ = 
  lmSNE MM εε (computeP-SN {L = neutral x} computePRRεε validΓ) SNL SNL' SNQ
pre-wte+-computeP {L₁ = bot} {MM} {NN} {P} {L} {L'} {Q} {RR} {εε} computePRRεε validΓ SNL SNL' SNQ = 
  lmSNE MM εε (computeP-SN {L = bot} computePRRεε validΓ) SNL SNL' SNQ
pre-wte+-computeP {m} {n} {V} {Γ} {imp S₁ S₂} {L₁ = imp L₁ L₂} {MM} {NN} {P} {L} {L'} {Q} {RR} {εε} {A} computePRRεε validΓ SNL SNL' SNQ {W} Δ {ρ = ρ} {ε = ε} ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε = 
  subst (computeP Δ (lrep L₂ ρ)) (let open ≡-Reasoning in 
  begin
    appP (APPP (plus (APP* (snocVec-rep MM ρ) (snocVec-rep NN ρ) (app* (L 〈 ρ 〉) (L' 〈 ρ 〉) (λλλ A (P 〈 liftsRep pathDom ρ 〉)) (Q 〈 ρ 〉)) (snocVec-rep RR ρ))) (snocVec-rep εε ρ)) ε
  ≡⟨⟨ cong (λ x → appP (APPP (plus x) (snocVec-rep εε ρ)) ε) (APP*-rep MM) ⟩⟩
    appP (APPP (plus ((APP* MM NN (app* L L' (λλλ A P) Q) RR) 〈 ρ 〉)) (snocVec-rep εε ρ)) ε
  ≡⟨⟨ cong (λ x → appP x ε) (APPP-rep εε) ⟩⟩
    appP (APPP (plus (APP* MM NN (app* L L' (λλλ A P) Q) RR)) εε 〈 ρ 〉) ε
  ∎)
  (pre-wte+-computeP {m} {suc n} {W} {Δ} {S₂} {lrep L₂ ρ} {snocVec-rep MM ρ} {snocVec-rep NN ρ} {P 〈 liftsRep pathDom ρ 〉} {L 〈 ρ 〉} {L' 〈 ρ 〉} {Q 〈 ρ 〉} {snocVec-rep RR ρ} {εε = snocVec-rep εε ρ snoc ε} {A}
  (subst (computeP Δ (lrep L₂ ρ)) 
  (let open ≡-Reasoning in 
  begin
    appP (APPP (plus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR)) εε 〈 ρ 〉) ε
  ≡⟨ cong (λ x → appP x ε) (APPP-rep εε) ⟩
    appP (APPP (plus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) 〈 ρ 〉) (snocVec-rep εε ρ)) ε
  ≡⟨ cong (λ x → appP (APPP (plus x) (snocVec-rep εε ρ)) ε) (APP*-rep MM) ⟩
    appP (APPP (plus (APP* (snocVec-rep MM ρ) (snocVec-rep NN ρ) (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧ 〈 ρ 〉) (snocVec-rep RR ρ))) (snocVec-rep εε ρ)) ε
  ≡⟨⟨ cong (λ x → appP (APPP (plus (APP* (snocVec-rep MM ρ) (snocVec-rep NN ρ) x (snocVec-rep RR ρ))) (snocVec-rep εε ρ)) ε) (botSub₃-liftRep₃ P) ⟩⟩
    appP (APPP (plus (APP* (snocVec-rep MM ρ) (snocVec-rep NN ρ) (P 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= L 〈 ρ 〉 ,x₁:= L' 〈 ρ 〉 ,x₀:= Q 〈 ρ 〉 ⟧) (snocVec-rep RR ρ))) (snocVec-rep εε ρ)) ε
  ∎) 
  (computePRRεε Δ ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε))
  (context-validity Δ⊢ε∶φ) 
  (SNrep R-creates-rep SNL) 
  (SNrep R-creates-rep SNL') 
  (SNrep R-creates-rep SNQ))

private postulate pre-wte--computeP : ∀ {m} {n} {V} {Γ : Context V} {S} {L₁ : Leaves V S}
                                    {MM NN : snocVec (Term V) m} {P L L' Q RR} {εε : snocVec (Proof V) n} {A} →
                                    computeP Γ L₁ (APPP (minus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR)) εε) →
                                    valid Γ → SN L → SN L' → SN Q →
                                    computeP Γ L₁ (APPP (minus (APP* MM NN (app* L L' (λλλ A P) Q) RR)) εε)

data Emult {V} (Γ : Context V) : ∀ {AA} → snocTypes V AA → snocListExp V AA → Set where
  [] : Emult Γ [] []
  _snoc_ : ∀ {n AA A MM M} → Emult Γ {n} AA MM → E' Γ A M → Emult Γ (AA snoc A) (MM snoc M)

Emult-rep : ∀ {U V Γ Δ n AA} {MM : snocVec (Term U) n} {ρ : Rep U V} → Emult Γ AA MM → ρ ∶ Γ ⇒R Δ → valid Δ → Emult Δ AA (snocVec-rep MM ρ)
Emult-rep [] _ _ = []
Emult-rep (MM∈EΓAA snoc M∈EΓA) ρ∶Γ⇒RΔ validΔ = (Emult-rep MM∈EΓAA ρ∶Γ⇒RΔ validΔ) snoc (E'-rep M∈EΓA ρ∶Γ⇒RΔ validΔ)

private pre-wte-compute : ∀ {n} {V} {Γ : Context V} {A P M} {BB : snocVec Type n} {C M' L L' Q NN NN' RR} →
                 addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 Pi BB C 〉 appT (M' ⇑ ⇑ ⇑) (var x₁) →
                 E Γ A L → E Γ A L' → E' Γ (L ≡〈 A 〉 L') Q →
                 Emult Γ BB NN → Emult Γ BB NN' → (∀ i → E' Γ (lookup i NN ≡〈 lookup i BB 〉 lookup i NN') (lookup i RR)) →
                 E' Γ (APP (appT M L) NN ≡〈 C 〉 APP (appT M' L') NN') (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) →
                 computeE Γ (APP (appT M L) NN) C (APP (appT M' L') NN') (APP* NN NN' (app* L L' (λλλ A P) Q) RR)
pre-wte-compute {A = A} {P} {C = Ω} {L = L} {L'} {Q} {NN} {NN'} {RR} ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' Ni∈EΓBi N'i∈EΓBi Ri∈EΓNi≡N'i (E'I Γ⊢PLL'Q∶MNN≡M'NN' (S₁ ,p S₂ ,p L₁ ,p L₂ ,p MLNN↠L₁ ,p M'L'NN'↠L₂ ,p computeP+ ,p computeP- )) =
  S₁ ,p S₂ ,p L₁ ,p L₂ ,p MLNN↠L₁ ,p M'L'NN'↠L₂ ,p 
  (λ Δ {ρ} {ε} ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε → subst (computeP Δ (lrep L₂ ρ)) 
    (cong (λ x → appP (plus x) ε) (sym (APP*-rep NN))) 
    (pre-wte+-computeP {Γ = Δ} {S₂} {lrep L₂ ρ} {snocVec-rep NN ρ} {snocVec-rep NN' ρ} {P 〈 liftsRep pathDom ρ 〉} {L 〈 ρ 〉} {L' 〈 ρ 〉} {Q 〈 ρ 〉} {snocVec-rep RR ρ} {εε = [] snoc ε} {A}
      (subst (computeP Δ (lrep L₂ ρ)) 
        (cong (λ x → appP (plus x) ε) (let open ≡-Reasoning in 
          begin
            (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) 〈 ρ 〉
          ≡⟨ APP*-rep NN ⟩
            APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧ 〈 ρ 〉) (snocVec-rep RR ρ)
          ≡⟨⟨ cong (λ x → APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) x (snocVec-rep RR ρ)) (botSub₃-liftRep₃ P) ⟩⟩
            APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) (P 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= L 〈 ρ 〉 ,x₁:= L' 〈 ρ 〉 ,x₀:= Q 〈 ρ 〉 ⟧) (snocVec-rep RR ρ)
          ∎)) 
        (computeP+ Δ ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε)) (context-validity Δ⊢ε∶φ) (SNrep R-creates-rep (E-SN A L∈EΓA)) (SNrep R-creates-rep (E-SN A L'∈EΓA)) (SNrep R-creates-rep (EE-SN _ Q∈EΓL≡L')))) ,p
  (λ Δ {ρ} {ε} ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε → subst (computeP Δ (lrep L₁ ρ)) 
    (cong (λ x → appP (minus x) ε) (sym (APP*-rep NN))) 
    (pre-wte--computeP {Γ = Δ} {S₁} {lrep L₁ ρ} {snocVec-rep NN ρ} {snocVec-rep NN' ρ} {P 〈 liftsRep pathDom ρ 〉} {L 〈 ρ 〉} {L' 〈 ρ 〉} {Q 〈 ρ 〉} {snocVec-rep RR ρ} {εε = [] snoc ε} {A}
      (subst (computeP Δ (lrep L₁ ρ)) 
        (cong (λ x → appP (minus x) ε) (let open ≡-Reasoning in 
          begin
            (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) 〈 ρ 〉
          ≡⟨ APP*-rep NN ⟩
            APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧ 〈 ρ 〉) (snocVec-rep RR ρ)
          ≡⟨⟨ cong (λ x → APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) x (snocVec-rep RR ρ)) (botSub₃-liftRep₃ P) ⟩⟩
            APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) (P 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= L 〈 ρ 〉 ,x₁:= L' 〈 ρ 〉 ,x₀:= Q 〈 ρ 〉 ⟧) (snocVec-rep RR ρ)
          ∎)) 
        (computeP- Δ ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε)) (context-validity Δ⊢ε∶φ) (SNrep R-creates-rep (E-SN A L∈EΓA)) (SNrep R-creates-rep (E-SN A L'∈EΓA)) (SNrep R-creates-rep (EE-SN _ Q∈EΓL≡L'))))
pre-wte-compute {Γ = Γ} {A} {P} {M} {BB} {C ⇛ C₁} {M'} {L} {L'} {Q} {NN} {NN'} {RR} 
  ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' NN∈EΓBB N'i∈EΓBi Ri∈EΓNi≡N'i PLL'QRR∈EΓMLNN≡M'L'NN' Δ {ρ} {N} {N'} {Q'} ρ∶Γ⇒RΔ Δ⊢Q∶N≡N' computeN computeN' computeQ = 
  let validΔ : valid Δ
      validΔ = context-validity Δ⊢Q∶N≡N' in
  subst₃ (λ a b c → computeE Δ a C₁ b c) (cong (λ x → appT x N) (sym (APP-rep NN))) (cong (λ x → appT x N') (sym (APP-rep NN'))) 
    (cong (λ x → app* N N' x Q') (sym (APP*-rep NN))) 
  (pre-wte-compute {Γ = Δ} {A} {P 〈 liftsRep pathDom ρ 〉} {M 〈 ρ 〉} {BB snoc C} {C₁} {M' 〈 ρ 〉} {L 〈 ρ 〉} {L' 〈 ρ 〉} {Q 〈 ρ 〉} {snocVec-rep NN ρ snoc N} {snocVec-rep NN' ρ snoc N'} {snocVec-rep RR ρ snoc Q'} 
  (change-type (weakening ΓAAE⊢P∶Mx≡Ny (valid-addpath validΔ) (liftsRep-typed ρ∶Γ⇒RΔ)) 
    (cong₂ (λ a b → appT a (var x₂) ≡〈 Pi BB (C ⇛ C₁) 〉 appT b (var x₁)) (liftRep-upRep₃ M) (liftRep-upRep₃ M'))) 
  (E'-rep L∈EΓA ρ∶Γ⇒RΔ validΔ) (E'-rep L'∈EΓA ρ∶Γ⇒RΔ validΔ) (E'-rep Q∈EΓL≡L' ρ∶Γ⇒RΔ validΔ) 
  (Emult-rep NN∈EΓBB ρ∶Γ⇒RΔ validΔ snoc E'I (equation-validity₁ Δ⊢Q∶N≡N') computeN) 
  (Emult-rep N'i∈EΓBi ρ∶Γ⇒RΔ validΔ snoc E'I (equation-validity₂ Δ⊢Q∶N≡N') computeN') 
  {!!} {!!})

private pre-wteE : ∀ {n} {V} {Γ : Context V} {A P M} {BB : snocVec Type n} {C M' L L' Q NN NN' RR} →
                 addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 Pi BB C 〉 appT (M' ⇑ ⇑ ⇑) (var x₁) →
                 E Γ A L → E Γ A L' → E' Γ (L ≡〈 A 〉 L') Q →
                 Emult Γ BB NN → Emult Γ BB NN' → (∀ i → E' Γ (lookup i NN ≡〈 lookup i BB 〉 lookup i NN') (lookup i RR)) →
                 E' Γ (APP (appT M L) NN ≡〈 C 〉 APP (appT M' L') NN') (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) →
                 E' Γ (APP (appT M L) NN ≡〈 C 〉 APP (appT M' L') NN') (APP* NN NN' (app* L L' (λλλ A P) Q) RR)
pre-wteE ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' Ni∈EΓBi N'i∈EΓBi Ri∈EΓNi≡N'i PLL'QRR∈EΓMLNN≡M'L'NN' = E'I (APP*-typed (app*R (E'.typed L∈EΓA) (E'.typed L'∈EΓA) 
  (lllR ΓAAE⊢P∶Mx≡Ny) (E'.typed Q∈EΓL≡L')) 
  (λ i → E'.typed (Ri∈EΓNi≡N'i i))) (pre-wte-compute ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' Ni∈EΓBi N'i∈EΓBi Ri∈EΓNi≡N'i PLL'QRR∈EΓMLNN≡M'L'NN')

wteE : ∀ {V} {Γ : Context V} {A P M B N L L' Q} →
  addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT (N ⇑ ⇑ ⇑) (var x₁) → 
  E Γ A L → E Γ A L' → E' Γ (L ≡〈 A 〉 L') Q →
  E' Γ (appT M L ≡〈 B 〉 appT N L') (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) →
  E' Γ (appT M L ≡〈 B 〉 appT N L') (app* L L' (λλλ A P) Q)
wteE {V} {Γ} {A} {P} {M} {B} {N} {L} {L'} {Q} ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' PLL'P∈EΓML≡NL' = 
  pre-wteE {BB = []} {NN = []} {[]} {[]} ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' [] [] (λ ()) PLL'P∈EΓML≡NL'

--TODO Duplications with PL
postulate extend-subC : ∀ {U} {V} {σ : Sub U V} {Γ : Context U} {Δ : Context V} {K} {M : Expression V (varKind K)} {A : Expression U (parent K)} →
                      σ ∶ Γ ⇒C Δ → E' Δ (A ⟦ σ ⟧) M → 
                      x₀:= M • liftSub K σ ∶ Γ , A ⇒C Δ

subCRS : ∀ {U V W} {ρ : Rep V W} {σ : Sub U V} {Γ Δ Θ} →
         ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒C Δ → valid Θ → ρ •RS σ ∶ Γ ⇒C Θ
subCRS {ρ = ρ} {σ = σ} {Γ} {Θ = Θ} ρ∶Δ⇒RΘ σ∶Γ⇒CΔ validΘ x = 
  subst (λ a → E' Θ a ((σ _ x) 〈 ρ 〉)) {typeof x Γ ⟦ σ ⟧ 〈 ρ 〉} {typeof x Γ ⟦ ρ •RS σ ⟧} 
    (sym (sub-compRS (typeof x Γ))) (E'-rep (σ∶Γ⇒CΔ x) ρ∶Δ⇒RΘ validΘ)
\end{code}
}

