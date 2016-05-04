\begin{code}
open import Grammar.Base

module Reduction.SN
  (G : Grammar) 
  (R : ∀ {V} {K} {C : Grammar.Kind G (Grammar.-Constructor {G} K)} → Grammar.Constructor G C → Grammar.Subexpression G V (Grammar.-Constructor {G} K) C → Grammar.Expression G V K → Set)
  where

open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G
open import Reduction G R
\end{code}

\subsection{Strong Normalization}

The \emph{strongly normalizable} expressions are defined inductively as follows.

\begin{code}
data SN {V C K} : Subexpression V C K → Set where
  SNI : ∀ E → (∀ F → E ⇒ F → SN F) → SN E
\end{code}

\begin{lemma}
\begin{enumerate}
\item
If $c([\vec{x_1}]E_1, \ldots, [\vec{x_n}]E_n)$ is strongly normalizable, then each $E_i$ is strongly normalizable.
\item
Let $F$ be a family of operations and $\sigma \in F$.
If $E[\sigma]$ is strongly normalizable and $R$ respects $F$ then $E$ is strongly normalizable.
\item
If $E$ is strongly normalizable and $R$ creates replacement then $E \langle \rho \rangle$ is strongly normalizable.
\item
If $E$ is strongly normalizable and $E \twoheadrightarrow_R F$ then $F$ is strongly normalizable.
\end{enumerate}
\end{lemma}

\begin{code}
SNsubexp : ∀ {V K} {C : Kind (-Constructor K)} {c : Constructor C} {EE : Subexpression V (-Constructor K) C} → SN (app c EE) → SN EE
SNsubexp {c = c} {EE = EE} (SNI .(app c EE) SNcEE) = SNI EE (λ FF EE→FF → SNsubexp (SNcEE (app c FF) (app EE→FF)))

SNsubbodyl : ∀ {V K A L C M N} → SN (_,,_ {V} {K} {A} {L} {C} M N) → SN M
SNsubbodyl {V} {K} {A} {L} {C} {M} {N} (SNI .(_,,_ M N) SNM) = SNI M (λ M' M⇒M' → SNsubbodyl (SNM (_,,_ M' N) (appl M⇒M')))

SNsubbodyr : ∀ {V K A L C M N} → SN (_,,_ {V} {K} {A} {L} {C} M N) → SN N
SNsubbodyr {V} {K} {A} {L} {C} {M} {N} (SNI .(_,,_ M N) SNN) = SNI N (λ N' N⇒N' → SNsubbodyr (SNN (_,,_ M N') (appr N⇒N')))

SNap' : ∀ {Ops : OpFamily} {U V C K} {E : Subexpression U C K} {σ : OpFamily.Op Ops U V} →
  Respects-Creates.respects' Ops → SN (OpFamily.ap Ops σ E) → SN E
SNap' {Ops} {E = E} {σ = σ} hyp (SNI .(OpFamily.ap Ops σ E) SNσE) = SNI E (λ F E→F → SNap' {Ops} hyp (SNσE (OpFamily.ap Ops σ F) 
  (Respects-Creates.respects-osr Ops hyp E→F)))

SNap : ∀ {U V C K} {E : Subexpression U C K} {σ : Rep U V} →
  Respects-Creates.creates' replacement → SN E → SN (E 〈 σ 〉)
SNap {U} {V} {C} {K} {E} {σ} hyp (SNI .E SNE) = SNI (E 〈 σ 〉) (λ F σE→F → 
  let E₀ = create-osr hyp E σE→F in
  let open Respects-Creates.creation {Ops = replacement} E₀ in
  subst SN ap-created (SNap hyp (SNE created red-created)))

SNred : ∀ {V K} {E F : Expression V K} → SN E → E ↠ F → SN F
SNred {V} {K} {E} {F} (SNI .E SNE) (osr-red E→F) = SNE F E→F
SNred SNE ref = SNE
SNred SNE (trans-red E↠F F↠G) = SNred (SNred SNE E↠F) F↠G
\end{code}
