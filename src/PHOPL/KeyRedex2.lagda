\AgdaHide{
\begin{code}
module PHOPL.KeyRedex2 where
open import Data.Nat
open import Data.Vec
open import PHOPL.Grammar
open import PHOPL.Computable
open import PHOPL.Red
\end{code}
}

\subsubsection{Well-Typed Expansion}

Let $\SN$ be the set of all strongly normalizing expressions.

\begin{prop}
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
\label{prop:SNE}
If $(P[x:=L, y:=L', e:=Q]_{M_1 N_1} Q_1 \cdots_{M_n N_n} Q_n)^+ \delta_1 \cdots \delta_m \in \SN$ and $L, L', Q \in \SN$ then $((\triplelambda e:x =_A y.P)_{L L'} Q_{M_1 N_1} Q_1 \cdots_{M_n N_n} Q_n)^+ \delta_1 \cdots \delta_m \in \SN$.

\AgdaHide{
\begin{code}
botsub₃-red : ∀ {V K₂ K₁ K₀} 
  {E₂ F₂ : Expression V (varKind K₂)} {E₁ F₁ : Expression V (varKind K₁)} {E₀ F₀ : Expression V (varKind K₀)} →
  E₂ ↠ F₂ → E₁ ↠ F₁ → E₀ ↠ F₀ → _↠s_ SUB (x₂:= E₂ ,x₁:= E₁ ,x₀:= E₀) (x₂:= F₂ ,x₁:= F₁ ,x₀:= F₀)
botsub₃-red _ _ E₀↠F₀ _ x₀ = E₀↠F₀
botsub₃-red _ E₁↠F₁ _ _ (↑ x₀) = E₁↠F₁
botsub₃-red E₂↠F₂ _ _ _ (↑ (↑ x₀)) = E₂↠F₂
botsub₃-red _ _ _ _ (↑ (↑ (↑ _))) = ref

lmSNE₁ : ∀ {V} {L L' : Term V} {P} {Q} {A} {F} → 
  SN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) → SN L → SN L' → SN Q →
  app* L L' (λλλ A P) Q ⇒ F → SN F
lmSNE₁ SNPQ _ _ _ (redex βE) = SNPQ
lmSNE₁ {P = P} SNPQ (SNI _ SNL) SNL' SNQ (app (appl L⇒L₀)) = SNI _ (λ _ → lmSNE₁ 
  (SNred SNPQ (apredl SUB {E = P} R-respects-sub (botsub₃-red (osr-red L⇒L₀) ref ref))) (SNL _ L⇒L₀) SNL' SNQ)
lmSNE₁ {P = P} SNPQ SNL (SNI E₁ SNL') SNQ (app (appr (appl L'⇒L'₀))) = SNI _ (λ _ → lmSNE₁ 
  (SNred SNPQ (apredl SUB {E = P} R-respects-sub (botsub₃-red ref (osr-red L'⇒L'₀) ref))) SNL (SNL' _ L'⇒L'₀) SNQ)
lmSNE₁ _ _ _ _ (app (appr (appr (appl (redex ())))))
lmSNE₁ (SNI _ SNPQ) SNL SNL' SNQ (app (appr (appr (appl (app (appl P⇒P')))))) = SNI _ (λ _ → lmSNE₁ 
  (SNPQ _ (respects-osr SUB R-respects-sub P⇒P')) SNL SNL' SNQ)
lmSNE₁ _ _ _ _ (app (appr (appr (appl (app (appr ()))))))
lmSNE₁ {P = P} SNPQ SNL SNL' (SNI _ SNQ) (app (appr (appr (appr (appl Q⇒Q'))))) = SNI _ (λ _ → lmSNE₁ 
  (SNred SNPQ (apredl SUB {E = P} R-respects-sub (botsub₃-red ref ref (osr-red Q⇒Q')))) SNL SNL' (SNQ _ Q⇒Q'))
lmSNE₁ (SNI _ PQ) (SNI E₂ SNL) (SNI E SNL') (SNI E₁ SNQ) (app (appr (appr (appr (appr ())))))

data redVP {V} : ∀ {n} → Vec (Proof V) n → Vec (Proof V) n → Set where
  redleft : ∀ {n} {δ} {δ'} {εε : Vec _ n} → δ ⇒ δ' → redVP (δ ∷ εε) (δ' ∷ εε)
  redright : ∀ {n} {δ} {εε εε' : Vec _ n} → redVP εε εε' → redVP (δ ∷ εε) (δ ∷ εε')

plusAPP*-red : ∀ {n} {V} {MM NN : Vec (Term V) n} {M} {N} {P} {Q} {QQ} {conc : Proof V → Set} →
  (∀ {X} → APP* MM NN (app* M N P Q) QQ ⇒ X → conc (plus X)) →
  ∀ {X} → plus (APP* MM NN (app* M N P Q) QQ) ⇒ X → conc X
plusAPP*-red {MM = []} {[]} {QQ = []} hyp (redex ())
plusAPP*-red {MM = []} {[]} {QQ = []} hyp (app (appl x)) = hyp x
plusAPP*-red {MM = []} {[]} {QQ = []} hyp (app (appr ()))
plusAPP*-red {MM = _ ∷ MM} {NN = _ ∷ _} {QQ = _ ∷ _} {conc} hyp M⇒X = 
  plusAPP*-red {MM = MM} {conc = conc} hyp M⇒X 

lmSNE : ∀ {m} {n} {V} {Γ : Context V} {S} {L₁ : Leaves V S}
      {MM NN : Vec (Term V) m} {P L L' Q RR} {εε : Vec (Proof V) n} {A} →
      SN (APPP (plus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR)) εε) →
      SN L → SN L' → SN Q → ∀ F →
      APPP (plus (APP* MM NN (app* L L' (λλλ A P) Q) RR)) εε ⇒ F → SN F
lmSNE {MM = MM} {NN} {P} {L} {L'} {Q} {RR} {εε = []} SNPRRεε SNL SNL' SNQ F PRRεε⇒F = plusAPP*-red {MM = MM} {NN} {QQ = RR} {conc = SN} 
  (λ {X} x → {!!}) 
  PRRεε⇒F
lmSNE {εε = ε ∷ εε} SNPRRεε SNL SNL' SNQ F PRRεε⇒F = {!!}
\end{code}
}

\item
If $(P[x:=L, y:=L', e:=Q]_{M_1 N_1} Q_1 \cdots_{M_n N_n} Q_n)^- \delta_1 \cdots \delta_m \in \SN$ and $L, L', Q \in \SN$ then $((\triplelambda e:x =_A y.P)_{L L'} Q_{M_1 N_1} Q_1 \cdots_{M_n N_n} Q_n)^- \delta_1 \cdots \delta_m \in \SN$.
\end{enumerate}
\end{prop}

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
