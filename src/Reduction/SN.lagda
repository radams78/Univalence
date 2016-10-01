\AgdaHide{
\begin{code}
open import Grammar.Base

module Reduction.SN (G : Grammar) (R : Grammar.Reduction G) where

open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G
open import Reduction.Base G R
\end{code}
}

\subsection{Strong Normalization}

The \emph{strongly normalizable} expressions are defined inductively as follows.

\begin{code}
data SN {V C K} : Subexpression V C K → Set where
  SNI : ∀ E → (∀ F → E ⇒ F → SN F) → SN E
\end{code}

\begin{lemma}$ $
\begin{enumerate}
\item
If $c([\vec{x_1}]E_1, \ldots, [\vec{x_n}]E_n)$ is strongly normalizable, then each $E_i$ is strongly normalizable.
\item
Let $F$ be a family of operations and $\sigma \in F$.
If $E[\sigma]$ is strongly normalizable and $R$ respects $F$ then $E$ is strongly normalizable.
\item
If $\rho$ is a replacement, $E$ is strongly normalizable and $R$ creates replacements then $E \langle \rho \rangle$ is strongly normalizable.
\item
If $E$ is strongly normalizable and $E \twoheadrightarrow_R F$ then $F$ is strongly normalizable.
\end{enumerate}
\end{lemma}

\begin{code}
SNsubexp : ∀ {V K C}
  {c : Constructor (SK C K)} {E : Subexpression V -ListAbs C} → 
  SN (app c E) → SN E
\end{code}

\AgdaHide{
\begin{code}
SNsubexp {c = c} {E = E} (SNI .(app c E) SNcE) = 
  SNI E (λ F E→F → SNsubexp (SNcE (app c F) (app E→F)))
\end{code}
}

\begin{code}
SNsubbodyl : ∀ {V A L M N} → 
  SN (_∷_ {V} {A} {L} M N) → SN M
\end{code}

\AgdaHide{
\begin{code}
SNsubbodyl {V} {A} {L} {M} {N} (SNI .(_∷_ M N) SNM) = SNI M (λ M' M⇒M' → SNsubbodyl (SNM (_∷_ M' N) (appl M⇒M')))
\end{code}
}

\begin{code}
SNsubbodyr : ∀ {V A L M N} → 
  SN (_∷_ {V} {A} {L} M N) → SN N
\end{code}

\AgdaHide{
\begin{code}
SNsubbodyr {V} {A} {L} {M} {N} (SNI .(_∷_ M N) SNN) = SNI N (λ N' N⇒N' → SNsubbodyr (SNN (_∷_ M N') (appr N⇒N')))
\end{code}
}

\begin{code}
SNap' : ∀ {Ops : OpFamily} {U V C K} 
  {E : Subexpression U C K} {σ : OpFamily.Op Ops U V} →
  respects' Ops → SN (OpFamily.ap Ops σ E) → SN E
\end{code}

\AgdaHide{
\begin{code}
SNap' {Ops} {E = E} {σ = σ} hyp (SNI .(OpFamily.ap Ops σ E) SNσE) = SNI E (λ F E→F → SNap' {Ops} hyp (SNσE (OpFamily.ap Ops σ F) 
  (respects-osr Ops hyp E→F)))
\end{code}
}

\begin{code}
SNrep : ∀ {U V C K} {E : Subexpression U C K} {σ : Rep U V} →
  creates' REP → SN E → SN (E 〈 σ 〉)
\end{code}

\AgdaHide{
\begin{code}
SNrep {U} {V} {C} {K} {E} {σ} hyp (SNI .E SNE) = SNI (E 〈 σ 〉) (λ F σE→F → 
  let E₀ = create-osr hyp E σE→F in
  let open creation {Ops = REP} E₀ in
  subst SN ap-created (SNrep hyp (SNE created red-created)))
\end{code}
}

\begin{code}
SNred : ∀ {V K} {E F : Expression V K} → SN E → E ↠ F → SN F
\end{code}

\AgdaHide{
\begin{code}
SNred {V} {K} {E} {F} (SNI .E SNE) (osr-red E→F) = SNE F E→F
SNred SNE ref = SNE
SNred SNE (trans-red E↠F F↠G) = SNred (SNred SNE E↠F) F↠G

SNvar : ∀ {V} {K} (x : Var V K) → SN (var x)
SNvar x = SNI (var x) (λ _ ())

data redview {V} {C} {K} (E : Subexpression V C K) : Subexpression V C K → Set where
  ref : redview E E
  trans-redview : ∀ {F} {G} → E ⇒ F → redview F G → redview E G

data SNview : ∀ {V} {C} {K} → Subexpression V C K → Set where
  SNviewI : ∀ {V} {C} {K} {E : Subexpression V C K} →
    (∀ F → E ↠⁺ F → SNview F) → SNview E

postulate SNtoSNview : ∀ {V} {C} {K} (M : Subexpression V C K) →
                     SN M → SNview M
\end{code}
}
