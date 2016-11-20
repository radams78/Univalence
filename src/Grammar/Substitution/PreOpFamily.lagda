\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.Substitution.PreOpFamily (G : Grammar) where
open import Data.List
open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G
\end{code}
}

\subsection{Substitution}

A \emph{substitution} $\sigma$ from alphabet $U$ to alphabet $V$, $\sigma : U \Rightarrow V$, is a function $\sigma$ that maps every variable $x$ of kind $K$ in $U$ to an
\emph{expression} $\sigma(x)$ of kind $K$ over $V$.  We now aim to prov that the substitutions form a family of operations, with application and identity being simply function application and identity.

%<*Sub>
\begin{code}
Sub : Alphabet → Alphabet → Set
Sub U V = ∀ K → Var U K → VExpression V K
\end{code}
%</Sub>

\AgdaHide{
\begin{code}
upSub : ∀ {V} {K} → Sub V (V , K)
upSub _ x = var (↑ x)

pre-substitution : PreOpFamily
pre-substitution = record { 
  Op = Sub; 
  apV = λ σ x → σ _ x; 
  up = upSub;
  apV-up = refl; 
  idOp = λ _ _ → var; 
  apV-idOp = λ _ → refl }

open PreOpFamily pre-substitution using () renaming (_∼op_ to _∼_;idOp to idSub) public
\end{code}
}

