<\AgdaHide{
\begin{code}
module PHOPL.KeyRedex where
open import Prelims
open import Prelims.Closure
open import Data.Product renaming (_,_ to _,p_)
open import Data.Nat
open import Data.Fin
open import PHOPL.Grammar
open import PHOPL.Rules
open import PHOPL.Meta
open import PHOPL.Computable
open import PHOPL.Red
open import PHOPL.KeyRedex.SNE
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
We prove part \ref{prop:SNT}; the proofs of the other parts are similar.

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
pre-wte+-computeP : ∀ {m} {n} {V} {Γ : Context V} {S} {L₁ : Meaning V S}
                          {MM NN : snocVec (Term V) m} {P L L' Q RR} {εε : snocVec (Proof V) n} {A} →
                          computeP Γ L₁ (APPP (plus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR)) εε) →
                          valid Γ → SN L → SN L' → SN Q →
                          computeP Γ L₁ (APPP (plus (APP* MM NN (app* L L' (λλλ A P) Q) RR)) εε)
pre-wte+-computeP {L₁ = nf₀ (neutral x)} {MM} {NN} {P} {L} {L'} {Q} {RR} {εε} computePRRεε validΓ SNL SNL' SNQ = 
  lmSNE MM εε (computeP-SN (nf₀ (neutral x)) computePRRεε validΓ) SNL SNL' SNQ
pre-wte+-computeP {L₁ = nf₀ bot} {MM} {NN} {P} {L} {L'} {Q} {RR} {εε} computePRRεε validΓ SNL SNL' SNQ = 
  lmSNE MM εε (computeP-SN (nf₀ bot) computePRRεε validΓ) SNL SNL' SNQ
pre-wte+-computeP {m} {n} {V} {Γ} {S₁ imp S₂} {L₁ = L₁ imp L₂} {MM} {NN} {P} {L} {L'} {Q} {RR} {εε} {A} computePRRεε validΓ SNL SNL' SNQ {W} Δ {ρ = ρ} {ε = ε} ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε = 
  subst (computeP Δ (nfrep L₂ ρ)) (let open ≡-Reasoning in 
  begin
    appP (APPP (plus (APP* (snocVec-rep MM ρ) (snocVec-rep NN ρ) (app* (L 〈 ρ 〉) (L' 〈 ρ 〉) (λλλ A (P 〈 liftsRep pathDom ρ 〉)) (Q 〈 ρ 〉)) (snocVec-rep RR ρ))) (snocVec-rep εε ρ)) ε
  ≡⟨⟨ cong (λ x → appP (APPP (plus x) (snocVec-rep εε ρ)) ε) (APP*-rep MM) ⟩⟩
    appP (APPP (plus ((APP* MM NN (app* L L' (λλλ A P) Q) RR) 〈 ρ 〉)) (snocVec-rep εε ρ)) ε
  ≡⟨⟨ cong (λ x → appP x ε) (APPP-rep εε) ⟩⟩
    appP (APPP (plus (APP* MM NN (app* L L' (λλλ A P) Q) RR)) εε 〈 ρ 〉) ε
  ∎)
  (pre-wte+-computeP {m} {suc n} {W} {Δ} {S₂} {nfrep L₂ ρ} {snocVec-rep MM ρ} {snocVec-rep NN ρ} {P 〈 liftsRep pathDom ρ 〉} {L 〈 ρ 〉} {L' 〈 ρ 〉} {Q 〈 ρ 〉} {snocVec-rep RR ρ} {εε = snocVec-rep εε ρ snoc ε} {A}
  (subst (computeP Δ (nfrep L₂ ρ)) 
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

postulate pre-wte--computeP : ∀ {m} {n} {V} {Γ : Context V} {S} {L₁ : Meaning V S}
                              {MM NN : snocVec (Term V) m} {P L L' Q RR} {εε : snocVec (Proof V) n} {A} →
                              computeP Γ L₁ (APPP (minus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR)) εε) →
                              valid Γ → SN L → SN L' → SN Q →
                              computeP Γ L₁ (APPP (minus (APP* MM NN (app* L L' (λλλ A P) Q) RR)) εε)

pre-wte-compute : ∀ {n} {V} {Γ : Context V} {A P M} {BB : snocVec Type n} {C M' L L' Q NN NN' RR} →
                        addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 Pi BB C 〉 appT (M' ⇑ ⇑ ⇑) (var x₁) →
                        E Γ (ty A) L → E Γ (ty A) L' → E Γ (L ≡〈 A 〉 L') Q →
                        Emult Γ (toSnocTypes BB) (toSnocListExp NN) → Emult Γ (toSnocTypes BB) (toSnocListExp NN') → Emult Γ (eqmult NN BB NN') (toSnocListExp RR) →
                        E Γ (APP (appT M L) NN ≡〈 C 〉 APP (appT M' L') NN') (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) →
                        computeE Γ (APP (appT M L) NN) C (APP (appT M' L') NN') (APP* NN NN' (app* L L' (λλλ A P) Q) RR)
pre-wte-compute {A = A} {P} {C = Ω} {L = L} {L'} {Q} {NN} {NN'} {RR} ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' Ni∈EΓBi N'i∈EΓBi Ri∈EΓNi≡N'i (EI Γ⊢PLL'Q∶MNN≡M'NN' (S ,p φ ,p ψ ,p MLNN↠φ ,p M'L'NN'↠ψ ,p computeP+ ,p computeP- )) =
  S ,p φ ,p ψ ,p MLNN↠φ ,p M'L'NN'↠ψ ,p 
  (λ Δ {ρ} {ε} ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε → subst (computeP Δ (nfrep ψ ρ)) 
    (cong (λ x → appP (plus x) ε) (Prelims.sym (APP*-rep NN))) 
    (pre-wte+-computeP {Γ = Δ} {S} {nfrep ψ ρ} {snocVec-rep NN ρ} {snocVec-rep NN' ρ} {P 〈 liftsRep pathDom ρ 〉} {L 〈 ρ 〉} {L' 〈 ρ 〉} {Q 〈 ρ 〉} {snocVec-rep RR ρ} {εε = [] snoc ε} {A}
      (subst (computeP Δ (nfrep ψ ρ)) 
        (cong (λ x → appP (plus x) ε) (let open ≡-Reasoning in 
          begin
            (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) 〈 ρ 〉
          ≡⟨ APP*-rep NN ⟩
            APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧ 〈 ρ 〉) (snocVec-rep RR ρ)
          ≡⟨⟨ cong (λ x → APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) x (snocVec-rep RR ρ)) (botSub₃-liftRep₃ P) ⟩⟩
            APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) (P 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= L 〈 ρ 〉 ,x₁:= L' 〈 ρ 〉 ,x₀:= Q 〈 ρ 〉 ⟧) (snocVec-rep RR ρ)
          ∎)) 
        (computeP+ Δ ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε)) (context-validity Δ⊢ε∶φ) (SNrep R-creates-rep (E-SNT L∈EΓA)) (SNrep R-creates-rep (E-SNT L'∈EΓA)) (SNrep R-creates-rep (E-SNE Q∈EΓL≡L')))) ,p
  (λ Δ {ρ} {ε} ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε → subst (computeP Δ (nfrep φ ρ)) 
    (cong (λ x → appP (minus x) ε) (Prelims.sym (APP*-rep NN))) 
    (pre-wte--computeP {Γ = Δ} {S} {nfrep φ ρ} {snocVec-rep NN ρ} {snocVec-rep NN' ρ} {P 〈 liftsRep pathDom ρ 〉} {L 〈 ρ 〉} {L' 〈 ρ 〉} {Q 〈 ρ 〉} {snocVec-rep RR ρ} {εε = [] snoc ε} {A}
      (subst (computeP Δ (nfrep φ ρ)) 
        (cong (λ x → appP (minus x) ε) (let open ≡-Reasoning in 
          begin
            (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) 〈 ρ 〉
          ≡⟨ APP*-rep NN ⟩
            APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧ 〈 ρ 〉) (snocVec-rep RR ρ)
          ≡⟨⟨ cong (λ x → APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) x (snocVec-rep RR ρ)) (botSub₃-liftRep₃ P) ⟩⟩
            APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) (P 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= L 〈 ρ 〉 ,x₁:= L' 〈 ρ 〉 ,x₀:= Q 〈 ρ 〉 ⟧) (snocVec-rep RR ρ)
          ∎)) 
        (computeP- Δ ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε)) (context-validity Δ⊢ε∶φ) (SNrep R-creates-rep (E-SNT L∈EΓA)) (SNrep R-creates-rep (E-SNT L'∈EΓA)) (SNrep R-creates-rep (E-SNE Q∈EΓL≡L'))))
pre-wte-compute {n} {Γ = Γ} {A} {P} {M} {BB} {C ⇛ C₁} {M'} {L} {L'} {Q} {NN} {NN'} {RR} 
  ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' NN∈EΓBB NN'∈EΓBB RR∈EΓNN≡NN' (EI Γ⊢PRR∶NN≡NN' computePLL') Δ {ρ} {N} {N'} {Q'} ρ∶Γ⇒RΔ Δ⊢Q∶N≡N' computeN computeN' computeQ = 
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
  (E-rep L∈EΓA ρ∶Γ⇒RΔ validΔ) (E-rep L'∈EΓA ρ∶Γ⇒RΔ validΔ) (E-rep Q∈EΓL≡L' ρ∶Γ⇒RΔ validΔ) 
  (subst₂ (Emult Δ) toSnocTypes-rep toSnocListExp-rep (Emult-rep NN∈EΓBB ρ∶Γ⇒RΔ validΔ) snoc EI Δ⊢N∶C computeN) 
  (subst₂ (Emult Δ) toSnocTypes-rep toSnocListExp-rep (Emult-rep NN'∈EΓBB ρ∶Γ⇒RΔ validΔ) snoc EI Δ⊢N'∶C computeN') 
  ((subst₂ (Emult Δ) eqmult-rep toSnocListExp-rep (Emult-rep RR∈EΓNN≡NN' ρ∶Γ⇒RΔ validΔ)) snoc subst₂ (λ a b → E Δ (a ≡〈 C 〉 b) Q') 
    (Prelims.sym (botSub-ups (Prelims.replicate n -Path))) (Prelims.sym (botSub-ups (Prelims.replicate n -Path))) (EI Δ⊢Q∶N≡N' computeQ))
  (subst₃ (λ a b c → E Δ (a ≡〈 C₁ 〉 b) c) (cong (λ x → appT x N) (APP-rep NN)) (cong (λ x → appT x N') (APP-rep NN')) 
    (cong (λ x → app* N N' x Q') (let open ≡-Reasoning in 
      begin
        (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) 〈 ρ 〉
      ≡⟨ APP*-rep NN ⟩
        APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧ 〈 ρ 〉) (snocVec-rep RR ρ)
      ≡⟨⟨ cong (λ x → APP* (snocVec-rep NN ρ) _ x _) (botSub₃-liftRep₃ P) ⟩⟩
        APP* (snocVec-rep NN ρ) (snocVec-rep NN' ρ) (P 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= L 〈 ρ 〉 ,x₁:= L' 〈 ρ 〉 ,x₀:= Q 〈 ρ 〉 ⟧) (snocVec-rep RR ρ)
      ∎)) 
  (EI (app*R Δ⊢N∶C Δ⊢N'∶C (weakening Γ⊢PRR∶NN≡NN' validΔ ρ∶Γ⇒RΔ) Δ⊢Q∶N≡N') 
  (computePLL' Δ ρ∶Γ⇒RΔ Δ⊢Q∶N≡N' computeN computeN' computeQ))))
\end{code}

\AgdaHide{
\begin{code}
Emult-lookup : ∀ {V n} {Γ : Context V} {MM NN : snocVec (Term V) n} {AA PP i} →
  Emult Γ (eqmult MM AA NN) (toSnocListExp PP) → E Γ (lookup i MM ≡〈 lookup i AA 〉 lookup i NN) (lookup i PP)
Emult-lookup {n = suc n} {Γ} {_ snoc _} {_ snoc _} {_ snoc A} {_ snoc P} {zero} (_ snoc P∈EΓM≡N) = 
  subst₂ (λ a b → E Γ (a ≡〈 A 〉 b) P) (botSub-ups (replicate n -Path)) (botSub-ups (replicate n -Path)) P∈EΓM≡N
Emult-lookup {MM = _ snoc _} {_ snoc _} {_ snoc _} {_ snoc _} {suc i} (PP∈EΓMM≡NN snoc _) = Emult-lookup {i = i} PP∈EΓMM≡NN

private pre-wteE : ∀ {n} {V} {Γ : Context V} {A P M} {BB : snocVec Type n} {C M' L L' Q NN NN' RR} →
                 addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 Pi BB C 〉 appT (M' ⇑ ⇑ ⇑) (var x₁) →
                 E Γ (ty A) L → E Γ (ty A) L' → E Γ (L ≡〈 A 〉 L') Q →
                 Emult Γ (toSnocTypes BB) (toSnocListExp NN) → Emult Γ (toSnocTypes BB) (toSnocListExp NN') → Emult Γ (eqmult NN BB NN') (toSnocListExp RR) →
                 E Γ (APP (appT M L) NN ≡〈 C 〉 APP (appT M' L') NN') (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) →
                 E Γ (APP (appT M L) NN ≡〈 C 〉 APP (appT M' L') NN') (APP* NN NN' (app* L L' (λλλ A P) Q) RR)
pre-wteE ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' Ni∈EΓBi N'i∈EΓBi Ri∈EΓNi≡N'i PLL'QRR∈EΓMLNN≡M'L'NN' = EI (APP*-typed (app*R (E.typed L∈EΓA) (E.typed L'∈EΓA) 
  (lllR ΓAAE⊢P∶Mx≡Ny) (E.typed Q∈EΓL≡L')) 
  (λ i → E.typed (Emult-lookup {i = i} Ri∈EΓNi≡N'i))) (pre-wte-compute ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' Ni∈EΓBi N'i∈EΓBi Ri∈EΓNi≡N'i PLL'QRR∈EΓMLNN≡M'L'NN')
\end{code}
}

\begin{lemma}
\label{lm:wte}
$ $
\begin{enumerate}
\item
\label{lm:wteE}
Let $\Gamma, x : A, y : A, e : x =_A y \vdash P : M x =_B N y$.  If
$L, L' \in E_\Gamma(A)$; $Q \in E_\Gamma(L =_A L')$ and $P[ x := L, y := L', e
:= Q ] \in E_\Gamma(M L =_B N L')$, then $(\triplelambda e : x =_A y . P)_{L L'} Q \in E_\Gamma(ML =_B NL')$.
\begin{code}
wteE : ∀ {V} {Γ : Context V} {A P M B N L L' Q} →
  addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT (N ⇑ ⇑ ⇑) (var x₁) → 
  E Γ (ty A) L → E Γ (ty A) L' → E Γ (L ≡〈 A 〉 L') Q →
  E Γ (appT M L ≡〈 B 〉 appT N L') (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) →
  E Γ (appT M L ≡〈 B 〉 appT N L') (app* L L' (λλλ A P) Q)
\end{code}

\AgdaHide{
\begin{code}
wteE {V} {Γ} {A} {P} {M} {B} {N} {L} {L'} {Q} ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' PLL'P∈EΓML≡NL' = 
  pre-wteE {BB = []} {NN = []} {[]} {[]} ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' [] [] [] PLL'P∈EΓML≡NL'
\end{code}
}
\item
\label{lm:wteP}
Let $\Gamma, p : \phi \vdash \delta : \psi$.  If $\epsilon \in E_\Gamma(\phi)$
and $\delta [p := \epsilon] \in E_\Gamma(\psi)$ then $(\lambda p:\phi.\delta) \epsilon \in E_\Gamma(\psi)$.
\begin{code}
postulate wteP : ∀ {V} {Γ : Context V} {φ ψ : Term V} {δ ε} →
               Γ ,P φ ⊢ δ ∶ ψ ⇑ → E Γ φ ε → E Γ ψ (δ ⟦ x₀:= ε ⟧) → E Γ ψ (appP (ΛP φ δ) ε)
\end{code}
\item
\label{lm:wteT}
Let $\Gamma, x : A \vdash M : B$ and let $N \in E_\Gamma(A)$. If $M[x:=N] \in E_\Gamma(B)$ then $(\lambda x:A.M)N \in E_\Gamma(B)$.
\end{enumerate}
\end{lemma}

\begin{proof}
We prove part \ref{lm:wteT} here; the proofs for the other parts are similar.

We shall prove the following stronger statement:

Suppose $\Gamma, x : A \vdash M : B_1 \rightarrow \cdots \rightarrow B_n \rightarrow C$.  Let $N \in E_\Gamma(A)$ and $N_i \in E_\Gamma(B_i)$ for $i = 1, \ldots, n$.  If
$M[x:=N]N_1 \cdots N_n \in E_\Gamma(C)$ then $(\lambda x:A.M)NN_1 \cdots N_n \in E_\Gamma(C)$.

The proof is by induction on the type $C$.

If $C \equiv \Omega$: it is easy to verify that $\Gamma \vdash (\lambda x:A.M)NN_1 \cdots N_n : \Omega$.  Proposition \ref{prop:SN}.\ref{prop:SNT}
gives that $(\lambda x:A.M)NN_1 \cdots N_n \in \SN$.

Now let $\Delta \supseteq \Gamma$ and $\delta \in E_\Delta((\lambda x:A.M)N \vec{N})$.  Let $\nf{(\lambda x:A.M)N \vec{N}} \equiv \phi_1 \supset \cdots \supset \phi_n \supset \chi$ where $\chi$ is $\bot$ or neutral.  Let $\epsilon_j \in E_\Delta(\phi_j)$ for each $j$.  We must show that
\[ ((\lambda x:A.M)N \vec{N})\{\}^+ \delta \epsilon_1 \cdots \epsilon_m
\in E_\Delta(\chi) \]
i.e.
\[ ((\triplelambda e:x =_A y. M \{ x:=e : x \sim y \})_{NN} N\{\}_{N_1 N_1}
N_1\{\} \cdots_{N_n N_n} N_n\{\})^+ \delta \vec{\epsilon} \in E_\Delta(\chi) \enspace . \]
It is easy to check that this proof is well-typed.  We need to prove that it is strongly normalizing.

By hypothesis, we have
\[ (M[x:=N] \vec{N})\{\}^+ \delta \vec{\epsilon} \in E_\Delta(\chi) \subseteq \SN \]
i.e.
\[ (M\{x:=N\{\} : N \sim N\} N_1 \{\} \cdots N_n \{\})^+ \delta \vec{\epsilon}
\in \SN \]
and so the result follows by Proposition \ref{prop:SN}.\ref{prop:SNE}.

The proof for $(\lambda x:A.M)N \vec{N})\{\}^-$ is similar.

If $C \equiv B_{n+1} \rightarrow D$: let $N_{n+1} \in E_{\Gamma}(B_{n+1})$.  Then
\begin{align*}
M[x:=N]\vec{N} N_{n+1} & \in E_\Gamma(C) \\
\therefore (\lambda x:A.M)N \vec{N} N_{n+1} & \in E_\Gamma(C)
\end{align*}
by the induction hypothesis, as required.

Now let $N_{n+1}, N_{n+1}' \in E_\Gamma(B_{n+1})$ and $P \in E_\Gamma(N_{n+1} =_{B_{n+1}} N_{n+1}')$.  We must show that
\begin{align*}
((\lambda x:A.M)N \vec{N}) \{\}_{N_{n+1}N_{n+1}'}P \\
\quad \in E_\Gamma((\lambda x:A.M) N \vec{N} N_{n+1} =_C (\lambda x:A.M) N \vec{N} N_{n+1}')
\end{align*}
i.e.
\begin{align*}
(\triplelambda e:x =_A y . M \{ x:=e \})_{NN} N \{ \}_{N_1 N_1} N_1\{\} \cdots_{N_n N_n} N_n\{\}_{N_{n+1} N_{n+1}'} P \\
\quad \in E_\Gamma(M[x:=N] N \vec{N} N_{n+1} = M[x:=N] N \vec{N} N_{n+1}')
\end{align*}
This follows from part \ref{lm:wteE}, since we have
\[ M[x:=N]\{\} \equiv M \{ x:= N \{ \} : N \sim N \} \in E_\Gamma(M[x:=N] = M[x:=N]) \]
\end{proof}
