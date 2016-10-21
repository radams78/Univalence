\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.Context (G : Grammar) where

open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality
open Grammar G
open import Grammar.Replacement G
\end{code}
}

\subsection{Contexts}

A \emph{context} has the form $x_1 : A_1, \ldots, x_n : A_n$ where, for each $i$:
\begin{itemize}
\item $x_i$ is a variable of kind $K_i$ distinct from $x_1$, \ldots, $x_{i-1}$;
\item $A_i$ is an expression whose kind is the parent of $K_i$.
\end{itemize}
The \emph{domain} of this context is the alphabet $\{ x_1, \ldots, x_n \}$.

\begin{code}
infixl 55 _,_
data Context : Alphabet → Set where
  〈〉 : Context ∅
  _,_ : ∀ {V} {K} → Context V → Expression V (parent K) → 
    Context (V , K)

-- Define typeof such that, if x : A ∈ Γ, then typeof x Γ ≡ A
-- We define it the following way so that typeof x Γ computes to an expression of the form
-- M 〈 upRep 〉, even if x is not in canonical form
pretypeof : ∀ {V} {K} {L} (x : Var (V , K) L) (Γ : Context (V , K)) → Expression V (parent L)
typeof : ∀ {V} {K} (x : Var V K) (Γ : Context V) → Expression V (parent K)

pretypeof x₀ (Γ , A) = A
pretypeof (↑ x) (Γ , A) = typeof x Γ

typeof {∅} ()
typeof {_ , _} x Γ = pretypeof x Γ ⇑
\end{code}

We say that a replacement $\rho$ is a \emph{(well-typed) replacement from $\Gamma$ to $\Delta$},
$\rho : \Gamma \rightarrow \Delta$, iff, for each entry $x : A$ in $\Gamma$, we have that
$\rho(x) : A \langle ρ \rangle$ is an entry in $\Delta$.

\begin{code}
_∶_⇒R_ : ∀ {U} {V} → Rep U V → Context U → Context V → Set
ρ ∶ Γ ⇒R Δ = ∀ {K} x → typeof (ρ K x) Δ ≡ typeof x Γ 〈 ρ 〉
\end{code}
