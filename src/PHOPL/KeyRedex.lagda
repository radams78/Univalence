\AgdaHide{
\begin{code}
module PHOPL.KeyRedex where

open import Data.Sum
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.PathSub
open import PHOPL.Red
\end{code}
}

Let $\SN$ be the set of strongly normalizing terms.

We define the relation $\kr$ between expressions as follows.  If $M \kr N$, we say that $M$ has a \emph{key redex} with \emph{reduct} $N$.

\[ \infer{(\lambda x:A.M)N \kr M[x:= N]}{N \in \SN} \]
\[ \infer{(\lambda p:\phi.\delta)\epsilon \kr \delta[p:= \epsilon]}{\phi, \epsilon \in \SN} \]
\[ \infer{(\triplelambda e:x =_A y.P)_{N N'} Q \kr P[x:= N, y:= N', e:= Q]}{N, N', Q \in \SN} \]
\[ \infer{\reff{\lambda x:A.M}_{N N'} P \kr M\{ x:= P : N \sim N' \}}{P, N, N' \in \SN, P \not\equiv \reff{-}} \]
\[ \infer{\reff{\lambda x:A.M}_{N_1 N_2} \ref{N} \kr \reff{M[x:=N]}}{N, N_1, N_2 \in \SN, N \simeq N_1 \simeq N_2} \]
\[ \infer{\reff{M} \kr \reff{N}}{M \kr N} \]
\[ \infer{ML \kr NL}{M \kr N} \qquad \infer{\delta \epsilon \kr \delta' \epsilon}{\delta \kr \delta'} \]
\[ \infer{P_{L L'} Q \kr P'_{L L'} Q}{P \kr P'} \]

\begin{code}
data key-redex {V} : ∀ {K} → Expression V K → Expression V K → Set where
  βTkr : ∀ {A} {M} {N : Term V} → SN M → key-redex (appT (ΛT A M) N) (M ⟦ x₀:= N ⟧)
  βPkr : ∀ {φ : Term V} {δ ε} (SNφ : SN φ) (SNε : SN ε) → key-redex (appP (ΛP φ δ) ε) (δ ⟦ x₀:= ε ⟧)
  βEkr : ∀ {N N' : Term V} {A} {P} {Q} (SNN : SN N) (SNN' : SN N') (SNQ : SN Q) →
           key-redex (app* N N' (λλλ A P) Q) (P ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧)
  appTkr : ∀ {M N P : Term V} → key-redex M N → key-redex (appT M P) (appT N P)
\end{code}

We have the following properties.

\AgdaHide{
\begin{code}
key-redex-rep : ∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} →
  key-redex M N → key-redex (M 〈 ρ 〉) (N 〈 ρ 〉)
key-redex-rep {ρ = ρ} (βTkr {A} {M} {N} SNM) = 
  subst (key-redex (appT (ΛT A M) N 〈 ρ 〉)) (sym (compRS-botSub M)) 
    (βTkr (SNrep R-creates-rep SNM))
key-redex-rep {ρ = ρ} (βPkr {φ} {δ} {ε} SNφ SNε) = 
  subst (key-redex ((appP (ΛP φ δ) ε) 〈 ρ 〉)) (sym (compRS-botSub δ)) 
    (βPkr (SNrep R-creates-rep SNφ) (SNrep R-creates-rep SNε))
key-redex-rep {ρ = ρ} (βEkr {N} {N'} {A} {P} {Q} SNN SNN' SNQ) = 
  subst (key-redex (app* N N' (λλλ A P) Q 〈 ρ 〉)) (botSub₃-liftRep₃ P)
    (βEkr (SNrep R-creates-rep SNN) (SNrep R-creates-rep SNN') (SNrep R-creates-rep SNQ))
key-redex-rep {ρ = ρ} (appTkr M▷N) = appTkr (key-redex-rep M▷N)
--REFACTOR Common pattern
\end{code}
}

\begin{lemma}
If $s \kr t \in \SN$ then $s \in \SN$.
\end{lemma}

\begin{proof}
The proof is by induction on $s \kr t$.  We deal with the following cases; the others are similar.

\paragraph{$(\lambda x:A.M)N \kr M[x:=N]$} where $N \in \SN$.

We must show that, if $M[x:=N], N \in \SN$, then $(\lambda x:A.M)N \in \SN$.  The proof is by
double induction on $N \in \SN$, then on $M[x:=N] \in \SN$.  The possible one-step reductions from $(\lambda x:A.M)N$ are:

\begin{description}
\item[$(\lambda x:A.M)N \rightarrow (\lambda x:A.M')N$, where $M \rightarrow M'$]  Then we have
$M[x:=N] \rightarrow M'[x:=N]$, and we apply the secondary induction hypothesis.
\item[$(\lambda x:A.M)N \rightarrow (\lambda x:A.M)N'$, where $N \rightarrow N'$]  Then we have $M[x:=N] \twoheadrightarrow M[x:=N']$ and
$N \rightarrow N'$, and we apply the primary induction hypothesis.
\item[$(\lambda x:A.M)N \rightarrow M{[x:=N]}$]  We have $M[x:=N] \in \SN$ by hypothesis.
\end{description}

\paragraph{$P_{L L'} Q \kr P'_{L L'} Q$, where $P \kr P'$}  By case analysis, if $P_{L L'} Q$ is a redex then it is of the form $\reff{M}_{L L'} \reff{N}$.
Therefore, the following are the possible one-step reductions from $P_{L L'} Q$:

\begin{description}
\item{$P_{L L'} Q \rightarrow P^\dagger_{L L'} Q$, where $P \rightarrow P^\dagger$}  
\end{description}
\end{proof}