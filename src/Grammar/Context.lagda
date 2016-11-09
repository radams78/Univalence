\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.Context (G : Grammar) where

open import Data.Nat
open import Data.Fin
open import Prelims
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

infix 25 _,,_
_,,_ : ∀ {V} {AA} → Context V → Types V AA → Context (extend V AA)
Γ ,, [] = Γ
Γ ,, (A , AA) = (Γ , A) ,, AA

infix 25 _,,,_
_,,,_ : ∀ {V AA} → Context V → snocTypes V AA → Context (snoc-extend V AA)
Γ ,,, [] = Γ
Γ ,,, (AA snoc A) = (Γ ,,, AA) , A
\end{code}

\begin{lemma}
\begin{enumerate}
\item
$\id{P}$ is a replacement $\Gamma \rightarrow \Gamma$.

\begin{code}
idRep-typed : ∀ {V} {Γ : Context V} → idRep V ∶ Γ ⇒R Γ
\end{code}

\AgdaHide{
\begin{code}
idRep-typed _ = sym rep-idRep
\end{code}
}

\item
$\uparrow$ is a replacement $\Gamma \rightarrow \Gamma , \phi$.

\begin{code}
↑-typed : ∀ {V Γ K} {A : Expression V (parent K)} → upRep ∶ Γ ⇒R (Γ , A)
\end{code}

\AgdaHide{
\begin{code}
↑-typed _ = refl
\end{code}
}

\item
If $\rho : \Gamma \rightarrow \Delta$ then $(\rho , K) : (\Gamma , x : A) \rightarrow (\Delta , x : A 〈 ρ 〉)$.

\begin{code}
liftRep-typed : ∀ {U V ρ K} {Γ : Context U} {Δ : Context V} {A : Expression U (parent K)} → 
  ρ ∶ Γ ⇒R Δ → liftRep K ρ ∶ (Γ , A) ⇒R (Δ , A 〈 ρ 〉)
\end{code}

\AgdaHide{
\begin{code}
--TODO Refactor?
liftRep-typed {A = A} ρ∶Γ⇒Δ x₀ = sym (liftRep-upRep A)
liftRep-typed {ρ = ρ} {K} {Γ} {Δ} {A} ρ∶Γ⇒Δ {L} (↑ x) = let open ≡-Reasoning in 
  begin
    typeof (ρ L x) Δ ⇑
  ≡⟨ rep-congl (ρ∶Γ⇒Δ x) ⟩
    typeof x Γ 〈 ρ 〉 ⇑
  ≡⟨⟨ liftRep-upRep (typeof x Γ) ⟩⟩
    (typeof x Γ ⇑) 〈 liftRep K ρ 〉
  ∎
\end{code}
}

\item
If $\rho : \Gamma \rightarrow \Delta$ and $\sigma : \Delta \rightarrow \Theta$ then $\sigma \circ \rho : \Gamma \rightarrow \Delta$.

\begin{code}
•R-typed : ∀ {U V W} {σ : Rep V W} {ρ : Rep U V} {Γ} {Δ} {Θ} → 
  σ ∶ Δ ⇒R Θ → ρ ∶ Γ ⇒R Δ → (σ •R ρ) ∶ Γ ⇒R Θ
\end{code}

\AgdaHide{
\begin{code}
•R-typed {U} {V} {W} {σ} {ρ} {Γ} {Δ} {Θ} σ∶Δ⇒RΘ ρ∶Γ⇒RΔ {K} x = let open ≡-Reasoning in 
  begin
    typeof (σ K (ρ K x)) Θ
  ≡⟨ σ∶Δ⇒RΘ (ρ K x) ⟩
    typeof (ρ K x) Δ 〈 σ 〉
  ≡⟨ rep-congl (ρ∶Γ⇒RΔ x) ⟩
    typeof x Γ 〈 ρ 〉 〈 σ 〉
  ≡⟨⟨ rep-comp (typeof x Γ) ⟩⟩
    typeof x Γ 〈 σ •R ρ 〉
  ∎
\end{code}
}

\end{enumerate}
\end{lemma}

