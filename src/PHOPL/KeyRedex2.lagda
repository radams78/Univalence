\AgdaHide{
\begin{code}
module PHOPL.KeyRedex2 where
open import Prelims
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
{-botsub₃-red : ∀ {V K₂ K₁ K₀} 
  {E₂ F₂ : Expression V (varKind K₂)} {E₁ F₁ : Expression V (varKind K₁)} {E₀ F₀ : Expression V (varKind K₀)} →
  E₂ ↠ F₂ → E₁ ↠ F₁ → E₀ ↠ F₀ → _↠s_ SUB (x₂:= E₂ ,x₁:= E₁ ,x₀:= E₀) (x₂:= F₂ ,x₁:= F₁ ,x₀:= F₀)
botsub₃-red _ _ E₀↠F₀ _ x₀ = E₀↠F₀
botsub₃-red _ E₁↠F₁ _ _ (↑ x₀) = E₁↠F₁
botsub₃-red E₂↠F₂ _ _ _ (↑ (↑ x₀)) = E₂↠F₂
botsub₃-red _ _ _ _ (↑ (↑ (↑ _))) = ref

pre-lmSNE₁ : ∀ {V} {L L' : Term V} {P} {Q} {A} {F} → 
  SN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) → SN L → SN L' → SN Q →
  app* L L' (λλλ A P) Q ⇒ F → SN F
pre-lmSNE₁ SNPQ _ _ _ (redex βE) = SNPQ
pre-lmSNE₁ {P = P} SNPQ (SNI _ SNL) SNL' SNQ (app (appl L⇒L₀)) = SNI _ (λ _ → pre-lmSNE₁ 
  (SNred SNPQ (apredl SUB {E = P} R-respects-sub (botsub₃-red (osr-red L⇒L₀) ref ref))) (SNL _ L⇒L₀) SNL' SNQ)
pre-lmSNE₁ {P = P} SNPQ SNL (SNI E₁ SNL') SNQ (app (appr (appl L'⇒L'₀))) = SNI _ (λ _ → pre-lmSNE₁ 
  (SNred SNPQ (apredl SUB {E = P} R-respects-sub (botsub₃-red ref (osr-red L'⇒L'₀) ref))) SNL (SNL' _ L'⇒L'₀) SNQ)
pre-lmSNE₁ _ _ _ _ (app (appr (appr (appl (redex ())))))
pre-lmSNE₁ (SNI _ SNPQ) SNL SNL' SNQ (app (appr (appr (appl (app (appl P⇒P')))))) = SNI _ (λ _ → pre-lmSNE₁ 
  (SNPQ _ (respects-osr SUB R-respects-sub P⇒P')) SNL SNL' SNQ)
pre-lmSNE₁ _ _ _ _ (app (appr (appr (appl (app (appr ()))))))
pre-lmSNE₁ {P = P} SNPQ SNL SNL' (SNI _ SNQ) (app (appr (appr (appr (appl Q⇒Q'))))) = SNI _ (λ _ → pre-lmSNE₁ 
  (SNred SNPQ (apredl SUB {E = P} R-respects-sub (botsub₃-red ref ref (osr-red Q⇒Q')))) SNL SNL' (SNQ _ Q⇒Q'))
pre-lmSNE₁ (SNI _ PQ) (SNI E₂ SNL) (SNI E SNL') (SNI E₁ SNQ) (app (appr (appr (appr (appr ())))))-}

pre-lmSNE₁ : ∀ {V} {L L' : Term V} {P Q A F} {C : Path V → Set} →
  C (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) →
  (∀ L₁ → L ⇒ L₁ → C (app* L₁ L' (λλλ A P) Q)) →
  (∀ L'₁ → L' ⇒ L'₁ → C (app* L L'₁ (λλλ A P) Q)) →
  (∀ P₁ → P ⇒ P₁ → C (app* L L' (λλλ A P₁) Q)) →
  (∀ Q₁ → Q ⇒ Q₁ → C (app* L L' (λλλ A P) Q₁)) →
  app* L L' (λλλ A P) Q ⇒ F → C F
pre-lmSNE₁ hyp-red _ _ _ _ (redex βE) = hyp-red
pre-lmSNE₁ _ hypL _ _ _ (app (appl L⇒L')) = hypL _ L⇒L'
pre-lmSNE₁ _ _ hypL' _ _ (app (appr (appl L₁⇒L'₁))) = hypL' _ L₁⇒L'₁
pre-lmSNE₁ _ _ _ _ _ (app (appr (appr (appl (redex ())))))
pre-lmSNE₁ _ _ _ hypP _ (app (appr (appr (appl (app (appl P⇒P')))))) = hypP _ P⇒P'
pre-lmSNE₁ _ _ _ _ _ (app (appr (appr (appl (app (appr ()))))))
pre-lmSNE₁ _ _ _ _ hypQ (app (appr (appr (appr (appl Q⇒Q'))))) = hypQ _ Q⇒Q'
pre-lmSNE₁ _ _ _ _ _ (app (appr (appr (appr (appr ())))))

data redVT {V} : ∀ {n} → snocVec (Term V) n → snocVec (Term V) n → Set where
  redleft : ∀ {n} {MM MM' : snocVec (Term V) n} {N} → redVT MM MM' → redVT (MM snoc N) (MM' snoc N)
  redright : ∀ {n} {MM : snocVec (Term V) n} {N N'} → N ⇒ N' → redVT (MM snoc N) (MM snoc N')

data redVP {V} : ∀ {n} → Vec (Proof V) n → Vec (Proof V) n → Set where
  redleft : ∀ {n} {δ} {δ'} {εε : Vec _ n} → δ ⇒ δ' → redVP (δ ∷ εε) (δ' ∷ εε)
  redright : ∀ {n} {δ} {εε εε' : Vec _ n} → redVP εε εε' → redVP (δ ∷ εε) (δ ∷ εε')

data redVPa {V} : ∀ {n} → snocVec (Path V) n → snocVec (Path V) n → Set where
  redleft : ∀ {n} {PP PP' : snocVec (Path V) n} {Q} → redVPa PP PP' → redVPa (PP snoc Q) (PP' snoc Q)
  redright : ∀ {n} {PP : snocVec (Path V) n} {Q Q'} → Q ⇒ Q' → redVPa (PP snoc Q) (PP snoc Q')

pre-lmSNE₂ : ∀ {n} {V} {L L' : Term V} {P Q A F} {MM NN : snocVec (Term V) n} {PP} 
  {C : Path V → Set} →
  C (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) PP) →
  (∀ MM' → redVT MM MM' → C (APP* MM' NN (app* L L' (λλλ A P) Q) PP)) →
  (∀ NN' → redVT NN NN' → C (APP* MM NN' (app* L L' (λλλ A P) Q) PP)) →
  (∀ L₁ → L ⇒ L₁ → C (APP* MM NN (app* L₁ L' (λλλ A P) Q) PP)) →
  (∀ L'₁ → L' ⇒ L'₁ → C (APP* MM NN (app* L L'₁ (λλλ A P) Q) PP)) →
  (∀ P₁ → P ⇒ P₁ → C (APP* MM NN (app* L L' (λλλ A P₁) Q) PP)) →
  (∀ Q₁ → Q ⇒ Q₁ → C (APP* MM NN (app* L L' (λλλ A P) Q₁) PP)) →
  (∀ PP' → redVPa PP PP' → C (APP* MM NN (app* L L' (λλλ A P) Q) PP')) →
  APP* MM NN (app* L L' (λλλ A P) Q) PP ⇒ F → C F
pre-lmSNE₂ {MM = []} {[]} {[]} hyp-red _ _ hypL hypL' hypP hypQ _ PQPP⇒F = pre-lmSNE₁ hyp-red hypL hypL' hypP hypQ PQPP⇒F
pre-lmSNE₂ {MM = [] snoc _} {[] snoc _} {[] snoc _} _ _ _ _ _ _ _ _ (redex ())
pre-lmSNE₂ {MM = _ snoc _} {_ snoc _} {_ snoc _} _ hypMM _ _ _ _ _ _ (app (appl M⇒M')) = hypMM _ (redright M⇒M')
pre-lmSNE₂ {MM = _ snoc _} {_ snoc _} {_ snoc _} _ _ hypNN _ _ _ _ _ (app (appr (appl N⇒N'))) = hypNN _ (redright N⇒N')
pre-lmSNE₂ {MM = _ snoc _} {_ snoc _} {_ snoc P} _ _ _ _ _ _ _ hypPP (app (appr (appr (appr (appl P⇒P'))))) = hypPP _ (redright P⇒P')
pre-lmSNE₂ {MM = _ snoc _} {_ snoc _} {_ snoc _} _ _ _ _ _ _ _ _ (app (appr (appr (appr (appr ())))))
pre-lmSNE₂ {MM = _ snoc _ snoc _} {_ snoc _ snoc _} {_ snoc _ snoc _} _ _ _ _ _ _ _ _ (redex ())
pre-lmSNE₂ {MM = MM snoc M} {NN snoc N} {PP snoc P} {C = C} hyp-red hypMM hypNN hypL hypL' hypP hypQ hypPP (app (appr (appr (appl PQPP⇒F)))) = 
  pre-lmSNE₂ {MM = MM} {NN} {PP} {C = λ x → C (app* M N x P)} 
    hyp-red 
    (λ _ MM⇒MM' → hypMM _ (redleft MM⇒MM')) (λ _ NN⇒NN' → hypNN _ (redleft NN⇒NN'))
    hypL hypL' hypP hypQ 
    (λ _ PP⇒PP' → hypPP _ (redleft PP⇒PP')) 
    PQPP⇒F

pre-lmSNE₃ : ∀ {n} {V} {L L' : Term V} {P Q A F} {MM NN : snocVec (Term V) n} {PP} {C : Proof V → Set} →
  C (plus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) PP)) →
  (∀ MM' → redVT MM MM' → C (plus (APP* MM' NN (app* L L' (λλλ A P) Q) PP))) →
  (∀ NN' → redVT NN NN' → C (plus (APP* MM NN' (app* L L' (λλλ A P) Q) PP))) →
  (∀ L₁ → L ⇒ L₁ → C (plus (APP* MM NN (app* L₁ L' (λλλ A P) Q) PP))) →
  (∀ L'₁ → L' ⇒ L'₁ → C (plus (APP* MM NN (app* L L'₁ (λλλ A P) Q) PP))) →
  (∀ P₁ → P ⇒ P₁ → C (plus (APP* MM NN (app* L L' (λλλ A P₁) Q) PP))) →
  (∀ Q₁ → Q ⇒ Q₁ → C (plus (APP* MM NN (app* L L' (λλλ A P) Q₁) PP))) →
  (∀ PP' → redVPa PP PP' → C (plus (APP* MM NN (app* L L' (λλλ A P) Q) PP'))) →
  plus (APP* MM NN (app* L L' (λλλ A P) Q) PP) ⇒ F → C F
pre-lmSNE₃ {MM = []} {[]} {[]} _ _ _ _ _ _ _ _ (redex ())
pre-lmSNE₃ {MM = _ snoc _} {_ snoc _} {_ snoc _} _ _ _ _ _ _ _ _ (redex ())
pre-lmSNE₃ {C = C} hyp-red hypMM hypNN hypL hypL' hypP hypQ hypPP (app (appl plusPQPP⇒F)) = 
  pre-lmSNE₂ {C = λ x → C (plus x)} hyp-red hypMM hypNN hypL hypL' hypP hypQ hypPP plusPQPP⇒F
pre-lmSNE₃ hyp-red hypMM hypNN hypL hypL' hypP hypQ hypPP (app (appr ()))

{-lmSNE₁ : ∀ {V} {L L' : Term V} {P} {Q} {A} → 
  SN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) → SN L → SN L' → SN Q →
  SN (app* L L' (λλλ A P) Q)
lmSNE₁ {V} {L} {L'} {P} {Q} {A} SNPQ SNL SNL' SNQ = SNI _ (λ F → pre-lmSNE₁ SNPQ SNL SNL' SNQ) -}

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
