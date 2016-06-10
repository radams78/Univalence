\AgdaHide{
\begin{code}
--TODO Module parameters
module PHOPL.PathSub where
open import Prelims
open import PHOPL.Grammar
\end{code}
}

\subsection{Path Substitution}

We introduce a notion of \emph{path substitution}.  The intention is that, if
$\Gamma \vdash P : M =_A M'$ and $\Gamma, x : A \vdash N : B$ then $\Gamma \vdash N \{ x := P : M \sim M' \} : N [ x:= M ] =_B N [ x := M' ]$.

\begin{definition}[Path Substitution]
Given terms $M_1$, \ldots, $M_n$ and $N_1$, \ldots, $N_n$; paths $P_1$, \ldots, $P_n$; term variales $x_1$, \ldots, $x_n$; and a term $L$, define the path $L \{ x_1 := P_1 : M_1 \sim N_1 , \ldots, x_n := P_n : M_n \sim N_n \}$ as follows.
\begin{align*}
x_i \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} & \eqdef P_i \\
y \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} & \eqdef \reff{y} \\
& \qquad (y \not\equiv x_1, \ldots, x_n) \\
\bot \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} & \eqdef \reff{\bot} \\
(LL') \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} \\
\omit\rlap{\qquad \qquad $\eqdef L \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \}_{L' [\vec{x} := \vec{M}] L' [\vec{x} := \vec{N}]} L' \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \}$} \\
(\lambda y:A.L) \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} & \\
\omit\rlap{\qquad\qquad $\eqdef \triplelambda e : a =_A a' . L \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} , y := e : a \sim a' \}$} \\
(\phi \supset \psi) \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} & \eqdef \phi \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} \supset^* \psi \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \}
\end{align*}
\end{definition}

\begin{code}
PathSub : Alphabet → Alphabet → Set
PathSub U V = Var U -Term → Path V
\end{code}

\AgdaHide{
\begin{code}
--TODO Is this like an OpFamily?

_∼∼_ : ∀ {U} {V} → PathSub U V → PathSub U V → Set
τ ∼∼ τ' = ∀ x → τ x ≡ τ' x

∼∼-refl : ∀ {U} {V} {τ : PathSub U V} → τ ∼∼ τ
∼∼-refl _ = refl

pathsub↑ : ∀ {U} {V} → PathSub U V → PathSub (U , -Term) (V , -Term , -Term , -Path)
pathsub↑ τ x₀ = var x₀
pathsub↑ τ (↑ x) = τ x ⇑ ⇑ ⇑

pathsub↑-cong : ∀ {U} {V} {τ τ' : PathSub U V} → τ ∼∼ τ' → pathsub↑ τ ∼∼ pathsub↑ τ'
pathsub↑-cong _ x₀ = refl
pathsub↑-cong τ∼∼τ' (↑ x) = rep-congl (rep-congl (rep-congl (τ∼∼τ' x)))

infix 70 _⟦⟦_∶_∼_⟧⟧
\end{code}
}

\begin{code}
_⟦⟦_∶_∼_⟧⟧ : ∀ {U} {V} → Term U → PathSub U V → 
  Sub U V → Sub U V → Path V
var x ⟦⟦ τ ∶ _ ∼ _ ⟧⟧ = τ x
app -bot out ⟦⟦ τ ∶ _ ∼ _ ⟧⟧ = reff ⊥
app -imp (φ ,, ψ ,, out) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ = φ ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ⊃* ψ ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧
app -appTerm (M ,, N ,, out) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ = app* (N ⟦ ρ ⟧) (N ⟦ σ ⟧) (M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧) (N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧)
app (-lamTerm A) (M ,, out) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ = λλλ A (M ⟦⟦ pathsub↑ τ ∶ sub↖ ρ ∼ sub↗ σ ⟧⟧)
\end{code}

\AgdaHide{
\begin{code}
pathsub-cong : ∀ {U} {V} M {τ τ' : PathSub U V} {ρ} {ρ'} {σ} {σ'} →
               τ ∼∼ τ' → ρ ∼ ρ' → σ ∼ σ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ≡ M ⟦⟦ τ' ∶ ρ' ∼ σ' ⟧⟧
pathsub-cong (var x) τ∼∼τ' _ _ = τ∼∼τ' x
pathsub-cong (app -bot out) _ _ _ = refl
pathsub-cong (app -imp (φ ,, ψ ,, out)) τ∼∼τ' ρ∼ρ' σ∼σ' = 
  cong₂ _⊃*_ (pathsub-cong φ τ∼∼τ' ρ∼ρ' σ∼σ') 
             (pathsub-cong ψ τ∼∼τ' ρ∼ρ' σ∼σ')
pathsub-cong (app -appTerm (M ,, N ,, out)) τ∼∼τ' ρ∼ρ' σ∼σ' = 
  cong₄ app* (sub-congr N ρ∼ρ') (sub-congr N σ∼σ') 
             (pathsub-cong M τ∼∼τ' ρ∼ρ' σ∼σ') 
             (pathsub-cong N τ∼∼τ' ρ∼ρ' σ∼σ')
pathsub-cong (app (-lamTerm A) (M ,, out)) τ∼∼τ' ρ∼ρ' σ∼σ' = 
  cong (λλλ A) (pathsub-cong M (pathsub↑-cong τ∼∼τ') 
               (sub↖-cong ρ∼ρ') (sub↗-cong σ∼σ'))

x₀::= : ∀ {V} → Path V → PathSub (V , -Term) V
(x₀::= P) x₀ = P
(x₀::= P) (↑ x) = reff (var x)
\end{code}
}

We define $M * P \eqdef \{ P / x \} (M x)$.  Thus, if $P : N =_A N'$
then $M * P : M N =_B M N'$ (Corollary \ref{cor:pathsub}).

\AgdaHide{
\begin{code}
_⋆[_∶_∼_] : ∀ {V} → Term V → Path V → Term V → Term V → Path V
--M ⋆[ P ∶ N ∼ N' ] = (appT (M ⇑) (var x₀)) ⟦⟦ x₀::= P ∶ x₀:= N ∼ x₀:= N' ⟧⟧
M ⋆[ P ∶ N ∼ N' ] = app* N N' (reff M) P
\end{code}
}