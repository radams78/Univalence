\subsection{Contexts}

A \emph{context} has the form $x_1 : A_1, \ldots, x_n : A_n$ where, for each $i$:
\begin{itemize}
\item $x_i$ is a variable of kind $K_i$ distinct from $x_1$, \ldots, $x_{i-1}$;
\item $A_i$ is an expression of some kind $L_i$;
\item $L_i$ is a parent of $K_i$.
\end{itemize}
The \emph{domain} of this context is the extend'bet $\{ x_1, \ldots, x_n \}$.

\begin{code}
open import Data.Nat
open import Data.Fin
open import Grammar

module Grammar.Context (G : Grammar') where
open Grammar' G

data Context (K : VarKind) : Alphabet → Set where
  〈〉 : Context K ∅
  _,_ : ∀ {V} → Context K V → Expression V (parent K) → Context K (V , K)

typeof : ∀ {V} {K} (x : Var V K) (Γ : Context K V) → Expression V (parent K)
typeof x₀ (_ , A) = A 〈 upRep 〉
typeof (↑ x) (Γ , _) = typeof x Γ 〈 upRep 〉

data Context' (A : Alphabet) (K : VarKind) : ℕ → Set where
  〈〉 : Context' A K zero
  _,_ : ∀ {F} → Context' A K F → Expression (extend A K F) (parent K) → Context' A K (suc F)
    
typeof' : ∀ {A} {K} {F} → Fin F → Context' A K F → Expression (extend A K F) (parent K)
typeof' zero (_ , A) = A 〈 upRep 〉
typeof' (suc x) (Γ , _) = typeof' x Γ 〈 upRep 〉
\end{code}
