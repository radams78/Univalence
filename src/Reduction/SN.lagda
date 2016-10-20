\AgdaHide{
\begin{code}
open import Grammar.Base

module Reduction.SN (G : Grammar) (R : Grammar.Reduction G) where

open import Prelims
open import Prelims.Closure
open import Grammar G
open import Reduction.Base G R
\end{code}
}

\subsection{Strong Normalization}

The \emph{strongly normalizable} expressions are defined inductively as follows.

\begin{code}
data SN {V C K} : Subexp V C K → Set where
  SNI : ∀ E → (∀ F → E ⇒ F → SN F) → SN E
\end{code}

\begin{lemma}$ $
\begin{enumerate}
\item
If $c([\vec{x_1}]E_1, \ldots, [\vec{x_n}]E_n)$ is strongly normalizable, then each $E_i$ is strongly normalizable.

\begin{code}
SNapp' : ∀ {V K AA} {c : Con (SK AA K)} {E : ListAbs V AA} → SN (app c E) → SN E
\end{code}

\AgdaHide{
\begin{code}
SNapp' {c = c} {E = E} (SNI _ SNcE) = SNI E (λ F E→F → SNapp' (SNcE (app c F) (app E→F)))
\end{code}
}

\begin{code}
SNappl' : ∀ {V A L M N} → SN (_∷_ {V} {A} {L} M N) → SN M
\end{code}

\AgdaHide{
\begin{code}
SNappl' {V} {A} {L} {M} {N} (SNI _ SNM) = 
  SNI M (λ M' M⇒M' → SNappl' (SNM (M' ∷ N) (appl M⇒M')))
\end{code}
}

\begin{code}
SNappr' : ∀ {V A L M N} → SN (_∷_ {V} {A} {L} M N) → SN N
\end{code}

\AgdaHide{
\begin{code}
SNappr' {V} {A} {L} {M} {N} (SNI _ SNN) = 
  SNI N (λ N' N⇒N' → SNappr' (SNN (M ∷ N') (appr N⇒N')))
\end{code}
}

\item
Let $F$ be a family of operations and $\sigma \in F$.
If $E[\sigma]$ is strongly normalizable and $R$ respects $F$ then $E$ is strongly normalizable.

\begin{code}
SNap' : ∀ {Ops U V C K} {E : Subexp U C K} {σ : OpFamily.Op Ops U V} →
  respects' Ops → SN (OpFamily.ap Ops σ E) → SN E
\end{code}

\AgdaHide{
\begin{code}
SNap' {Ops} {E = E} {σ = σ} hyp (SNI _ SNσE) = 
  SNI E (λ F E→F → SNap' {Ops} hyp (SNσE _ (aposrr Ops hyp E→F)))
\end{code}
}

\item
If $\rho$ is a replacement, $E$ is strongly normalizable and $R$ creates replacements then $E \langle \rho \rangle$ is strongly normalizable.

\begin{code}
SNrep : ∀ {U V C K} {E : Subexp U C K} {σ : Rep U V} →
  creates' REP → SN E → SN (E 〈 σ 〉)
\end{code}

\AgdaHide{
\begin{code}
SNrep {U} {V} {C} {K} {E} {σ} hyp (SNI .E SNE) = SNI (E 〈 σ 〉) (λ F σE⇒F → 
  let open creation {Ops = REP} (create-osr hyp E σE⇒F) in
  subst SN ap-created (SNrep hyp (SNE created red-created)))
\end{code}
}

\item
If $E$ is strongly normalizable and $E \twoheadrightarrow_R F$ then $F$ is strongly normalizable.
\begin{code}
SNred : ∀ {V K} {E F : Expression V K} → SN E → E ↠ F → SN F
\end{code}

\AgdaHide{
\begin{code}
SNred {V} {K} {E} {F} (SNI .E SNE) (inc E→F) = SNE F E→F
SNred SNE ref = SNE
SNred SNE (trans E↠F F↠G) = SNred (SNred SNE E↠F) F↠G
\end{code}
}
\item
Every variable is strongly normalizing.
\begin{code}
SNvar : ∀ {V} {K} (x : Var V K) → SN (var x)
\end{code}

\AgdaHide{
\begin{code}
SNvar x = SNI (var x) (λ _ ())
\end{code}
}
\end{enumerate}
\end{lemma}

