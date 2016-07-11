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

We define the relation $\kr$ between expressions as follows.  If $M \kr N$, we say that $M$ has a \emph{key redex} with \emph{reduct} $N$.

\[ \infer{(\lambda x:A.M)N \kr M[x:= N]}{M \text{ is strongly normalising}} \]
\[ \infer{(\lambda p:\phi.\delta)\epsilon \kr \delta[p:= \epsilon]}{\phi, \epsilon \text{ are strongly normalising}} \]
\[ \infer{(\triplelambda e:x =_A y.P)_{N N'} Q \kr P[x:= N, y:= N', e:= Q]}{N, N', Q \text{ are strongly normalising} \quad P \text{ is in normal form}} \]
\[ \infer{MP \kr NP}{M \kr N} \qquad \infer{\delta \epsilon \kr \delta' \epsilon}{\delta \kr \delta'} \]

\begin{code}
data key-redex {V} : ∀ {K} → Expression V K → Expression V K → Set where
  βTkr : ∀ {A} {M} {N : Term V} → SN M → key-redex (appT (ΛT A M) N) (M ⟦ x₀:= N ⟧)
  βPkr : ∀ {φ : Term V} {δ ε} (SNφ : SN φ) (SNε : SN ε) → key-redex (appP (ΛP φ δ) ε) (δ ⟦ x₀:= ε ⟧)
  βEkr : ∀ {N N' : Term V} {A} {P} {Q} (SNN : SN N) (SNN' : SN N') (SNQ : SN Q) →
           key-redex (app* N N' (λλλ A P) Q) (P ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧)
  appTkr : ∀ {M N P : Term V} → key-redex M N → key-redex (appT M P) (appT N P)
\end{code}

Clearly, if $M \kr N$, then $M \rightarrow N$.  We also have the following properties.

\begin{lm}
\label{lm:krsn}
If $M \kr N$ and $M \twoheadrightarrow P$, then there exists $Q$ such that $N \twoheadrightarrow Q$, and either $P \kr Q$ or $P \equiv Q$.
\end{lm}

\begin{proof}
The proof is by induction on $M \kr N$.  All cases are simple.
\end{proof}

\begin{code}
postulate key-redex-confluent : ∀ {V} {K} {M N P : Expression V K} →
                              key-redex M N → M ⇒ P → Σ[ Q ∈ Expression V K ] (key-redex P Q ⊎ P ≡ Q) × (N ↠⁺ Q ⊎ N ≡ Q)

postulate expand-lemma : ∀ {V} {M M' N : Term V} →
                       SN M → key-redex M M' → SN (appT M' N) → SN (appT M N)
\end{code}

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

postulate key-redex-red : ∀ {V} {K} {M N : Expression V K} → key-redex M N → M ↠ N

postulate key-redex-⋆ : ∀ {V} {M M' N N' : Term V} {P} →
                        key-redex M M' → key-redex (M ⋆[ P ∶ N ∼ N' ]) (M' ⋆[ P ∶ N ∼ N' ])
\end{code}
}
