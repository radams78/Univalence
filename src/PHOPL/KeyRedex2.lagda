<\AgdaHide{
\begin{code}
module PHOPL.KeyRedex2 where
open import Prelims
open import Prelims.Closure
open import Data.Product renaming (_,_ to _,p_)
open import Data.Nat
open import Data.Vec
open import PHOPL.Grammar
open import PHOPL.Rules
open import PHOPL.Meta
open import PHOPL.Computable
open import PHOPL.Red
open import PHOPL.KeyRedex2.SNE
\end{code}
}

\subsubsection{Well-Typed Expansion}

Let $\SN$ be the set of all strongly normalizing expressions.

\begin{proposition}
\label{prop:SN}
$ $
\begin{enumerate}
\item
\label{prop:SNT}
If $M[x:=N]L_1 \cdots L_n \in \SN$ and $N \in \SN$ then $(\lambda x:A.M)NL_1 \cdots L_n \in \SN$.
\item
\label{prop:SNP}
If $\delta[p:=\epsilon], \phi, \epsilon \in \SN$ then $(\lambda p:\phi.\delta)\epsilon \in \SN$.
\item
If $(P[x:=L, y:=L', e:=Q]_{M_1 N_1} Q_1 \cdots_{M_n N_n} Q_n)^- \delta_1 \cdots \delta_m \in \SN$ and $L, L', Q \in \SN$ then $((\triplelambda e:x =_A y.P)_{L L'} Q_{M_1 N_1} Q_1 \cdots_{M_n N_n} Q_n)^- \delta_1 \cdots \delta_m \in \SN$.
\end{enumerate}
\end{proposition}

\begin{proof}
+We prove part \ref{prop:SNT}; the proofs of the other parts are similar.

The proof is by a double induction on the hypotheses.  Consider all possible one-step reductions from $(\lambda x:A.M) N \vec{L}$.  The possibilities are:
\begin{description}
\item[$(\lambda x:A.M) N \vec{L} \rightarrow (\lambda x:A.M')N \vec{L}$, where $M \rightarrow M'$]
$ $

In this case, we have $M[x:=N] \vec{L} \rightarrow M'[x:=N] \vec{L}$, and the result follows by the induction hypothesis.  Similarly for the case
where we reduce $N$ or one of the $L_i$.
\item[$(\lambda x:A.M)N \vec{L} \rightarrow M{[x:=N]} \vec{L}$]
$ $

In this case, the result follows immediately from the hypothesis.
\end{description}
\end{proof}

\begin{code}
pre-wte+-computeP : ∀ {m} {n} {V} {Γ : Context V} {S} {L₁ : Leaves V S}
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

postulate pre-wte--computeP : ∀ {m} {n} {V} {Γ : Context V} {S} {L₁ : Leaves V S}
                              {MM NN : snocVec (Term V) m} {P L L' Q RR} {εε : snocVec (Proof V) n} {A} →
                              computeP Γ L₁ (APPP (minus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR)) εε) →
                              valid Γ → SN L → SN L' → SN Q →
                              computeP Γ L₁ (APPP (minus (APP* MM NN (app* L L' (λλλ A P) Q) RR)) εε)

pre-wte-compute : ∀ {n} {V} {Γ : Context V} {A P M} {BB : snocVec Type n} {C M' L L' Q NN NN' RR} →
                        addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 Pi BB C 〉 appT (M' ⇑ ⇑ ⇑) (var x₁) →
                        E Γ A L → E Γ A L' → E' Γ (L ≡〈 A 〉 L') Q →
                        Emult Γ (toSnocTypes BB) (toSnocListExp NN) → Emult Γ (toSnocTypes BB) (toSnocListExp NN') → Emult Γ (eqmult NN BB NN') (toSnocListExp RR) →
                        E' Γ (APP (appT M L) NN ≡〈 C 〉 APP (appT M' L') NN') (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) →
                        computeE Γ (APP (appT M L) NN) C (APP (appT M' L') NN') (APP* NN NN' (app* L L' (λλλ A P) Q) RR)
pre-wte-compute {A = A} {P} {C = Ω} {L = L} {L'} {Q} {NN} {NN'} {RR} ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' Ni∈EΓBi N'i∈EΓBi Ri∈EΓNi≡N'i (E'I Γ⊢PLL'Q∶MNN≡M'NN' (S₁ ,p S₂ ,p L₁ ,p L₂ ,p MLNN↠L₁ ,p M'L'NN'↠L₂ ,p computeP+ ,p computeP- )) =
  S₁ ,p S₂ ,p L₁ ,p L₂ ,p MLNN↠L₁ ,p M'L'NN'↠L₂ ,p 
  (λ Δ {ρ} {ε} ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε → subst (computeP Δ (lrep L₂ ρ)) 
    (cong (λ x → appP (plus x) ε) (Prelims.sym (APP*-rep NN))) 
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
    (cong (λ x → appP (minus x) ε) (Prelims.sym (APP*-rep NN))) 
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
pre-wte-compute {n} {Γ = Γ} {A} {P} {M} {BB} {C ⇛ C₁} {M'} {L} {L'} {Q} {NN} {NN'} {RR} 
  ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' NN∈EΓBB NN'∈EΓBB RR∈EΓNN≡NN' (E'I Γ⊢PRR∶NN≡NN' computePLL') Δ {ρ} {N} {N'} {Q'} ρ∶Γ⇒RΔ Δ⊢Q∶N≡N' computeN computeN' computeQ = 
  let validΔ : valid Δ
      validΔ = context-validity Δ⊢Q∶N≡N' in
  let Δ⊢N∶C : Δ ⊢ N ∶ ty C
      Δ⊢N∶C = equation-validity₁ Δ⊢Q∶N≡N' in
  let Δ⊢N'∶C : Δ ⊢ N' ∶ ty C
      Δ⊢N'∶C = equation-validity₂ Δ⊢Q∶N≡N' in
  subst₃ (λ a b c → computeE Δ a C₁ b c) (cong (λ x → appT x N) (Prelims.sym (APP-rep NN))) (cong (λ x → appT x N') (Prelims.sym (APP-rep NN'))) 
    (cong (λ x → app* N N' x Q') (Prelims.sym (APP*-rep NN))) 
  (pre-wte-compute {Γ = Δ} {A} {P 〈 liftsRep pathDom ρ 〉} {M 〈 ρ 〉} {BB snoc C} {C₁} {M' 〈 ρ 〉} {L 〈 ρ 〉} {L' 〈 ρ 〉} {Q 〈 ρ 〉} {snocVec-rep NN ρ snoc N} {snocVec-rep NN' ρ snoc N'} {snocVec-rep RR ρ snoc Q'} 
  (change-type (weakening ΓAAE⊢P∶Mx≡Ny (valid-addpath validΔ) (liftsRep-typed ρ∶Γ⇒RΔ)) 
    (cong₂ (λ a b → appT a (var x₂) ≡〈 Pi BB (C ⇛ C₁) 〉 appT b (var x₁)) (liftRep-upRep₃ M) (liftRep-upRep₃ M'))) 
  (E'-rep L∈EΓA ρ∶Γ⇒RΔ validΔ) (E'-rep L'∈EΓA ρ∶Γ⇒RΔ validΔ) (E'-rep Q∈EΓL≡L' ρ∶Γ⇒RΔ validΔ) 
  (subst₂ (Emult Δ) toSnocTypes-rep toSnocListExp-rep (Emult-rep NN∈EΓBB ρ∶Γ⇒RΔ validΔ) snoc E'I Δ⊢N∶C computeN) 
  (subst₂ (Emult Δ) toSnocTypes-rep toSnocListExp-rep (Emult-rep NN'∈EΓBB ρ∶Γ⇒RΔ validΔ) snoc E'I Δ⊢N'∶C computeN') 
  ((subst₂ (Emult Δ) eqmult-rep toSnocListExp-rep (Emult-rep RR∈EΓNN≡NN' ρ∶Γ⇒RΔ validΔ)) snoc subst₂ (λ a b → E' Δ (a ≡〈 C 〉 b) Q') 
    (Prelims.sym (botSub-ups (Prelims.replicate n -Path))) (Prelims.sym (botSub-ups (Prelims.replicate n -Path))) (E'I Δ⊢Q∶N≡N' computeQ))
  (subst₃ (λ a b c → E' Δ (a ≡〈 C₁ 〉 b) c) (cong (λ x → appT x N) (APP-rep NN)) (cong (λ x → appT x N') (APP-rep NN')) 
    (cong (λ x → app* N N' x Q') (let open ≡-Reasoning in 
      begin
        (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) 〈 ρ 〉
      ≡⟨ APP*-rep NN ⟩
        APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧ 〈 ρ 〉) (snocVec-rep RR ρ)
      ≡⟨⟨ cong (λ x → APP* (snocVec-rep NN ρ) _ x _) (botSub₃-liftRep₃ P) ⟩⟩
        APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) (P 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= L 〈 ρ 〉 ,x₁:= L' 〈 ρ 〉 ,x₀:= Q 〈 ρ 〉 ⟧) (snocVec-rep RR ρ)
      ∎)) 
  (E'I (app*R Δ⊢N∶C Δ⊢N'∶C (weakening Γ⊢PRR∶NN≡NN' validΔ ρ∶Γ⇒RΔ) Δ⊢Q∶N≡N') 
  (computePLL' Δ ρ∶Γ⇒RΔ Δ⊢Q∶N≡N' computeN computeN' computeQ))))
\end{code}
