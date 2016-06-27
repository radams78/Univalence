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

\begin{frame}[fragile]
\frametitle{Substitution}
\mode<beamer>{A \emph{substitution} between alphabets $U$ and $V$ maps variables of $U$ to expressions of $V$.}

\begin{code}
Sub : Alphabet VarKind → Alphabet VarKind → Set
Sub U V = ∀ K → Var U K → Expression V (varKind K)
\end{code}

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
\end{frame}
