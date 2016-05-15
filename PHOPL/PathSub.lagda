\AgdaHide{
\begin{code}
module PHOPL.PathSub where
open import Prelims
open import PHOPL
open import PHOPL.Rules
\end{code}
}

\subsection{Path Substitution}

\begin{frame}[fragile]
\frametitle{Path Substitution}
Define the operation of \emph{path substitution} such that,
if $P : M =_A M'$ then $\{ P / x \} N : [M / x] N =_B [M' / x] N$.

\mode<article>{
Given paths $P_1$, \ldots, $P_n$; term variales $x_1$, \ldots, $x_n$; and a term $M$, define the path $\{ P_1 / x_1, \ldots, P_n / x_n \} M$ as follows.
\begin{align*}
\{ P_1 / x_1, \ldots, P_n / x_n \} x_i & \eqdef P_i \\
\{ P_1 / x_1, \ldots, P_n / x_n \} y & \eqdef \reff{y} & (y \not\equiv x_1, \ldots, x_n) \\
\{ P_1 / x_1, \ldots, P_n / x_n \} \bot & \eqdef \reff{\bot} \\
\{ \vec{P} / \vec{x} \} (MN) & \eqdef \{ \vec{P} / \vec{x} \} M \{ \vec{P} / \vec{x} \} N \\
\{ \vec{P} / \vec{x} \} (\lambda y : A . M) & \eqdef \triplelambda e : a =_A a' . \{ \vec{P} / \vec{x} , e / y \} M \\
\{ \vec{P} / \vec{x} \} (\phi \rightarrow \psi) & \eqdef \{ \vec{P} / \vec{x} \} \phi \rightarrow \{ \vec{P} / \vec{x} \} \psi
\end{align*}

\begin{code}
PathSub : Alphabet → Alphabet → Set
PathSub U V = Var U -Term → Path V

--REFACTOR
sub↖ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (V , -Term , -Term , -Path)
sub↖ σ _ x₀ = var x₂
sub↖ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

sub↗ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (V , -Term , -Term , -Path)
sub↗ σ _ x₀ = var x₁
sub↗ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

pathsub↑ : ∀ {U} {V} → PathSub U V → PathSub (U , -Term) (V , -Term , -Term , -Path)
pathsub↑ τ x₀ = var x₀
pathsub↑ τ (↑ x) = τ x ⇑ ⇑ ⇑

_⟦⟦_∶_⇒_⟧⟧ : ∀ {U} {V} → Term U → PathSub U V → Sub U V → Sub U V → Path V
var x ⟦⟦ τ ∶ _ ⇒ _ ⟧⟧ = τ x
app -bot out ⟦⟦ τ ∶ _ ⇒ _ ⟧⟧ = reff ⊥
app -imp (φ ,, ψ ,, out) ⟦⟦ τ ∶ ρ ⇒ σ ⟧⟧ = φ ⟦⟦ τ ∶ ρ ⇒ σ ⟧⟧ ⊃* ψ ⟦⟦ τ ∶ ρ ⇒ σ ⟧⟧
app -appTerm (M ,, N ,, out) ⟦⟦ τ ∶ ρ ⇒ σ ⟧⟧ = app* (N ⟦ ρ ⟧) (N ⟦ σ ⟧) (M ⟦⟦ τ ∶ ρ ⇒ σ ⟧⟧) (N ⟦⟦ τ ∶ ρ ⇒ σ ⟧⟧)
app -lamTerm (A ,, M ,, out) ⟦⟦ τ ∶ ρ ⇒ σ ⟧⟧ = λλλ (A ⟦ ρ ⟧) (M ⟦⟦ pathsub↑ τ ∶ sub↖ ρ ⇒ sub↗ σ ⟧⟧)
\end{code}
}

\begin{lemma}
If $\Gamma \vdash P : M =_A M'$ and $\Gamma, x : A \vdash N : B$ then
$\Gamma \vdash \{ P / x \} N : [M / x] N =_B [M' / x] N$.
\end{lemma}

\begin{code}
{-pathsub-wd : ∀ {U} {V} {ρ σ : Sub U V} {τ : Var U -Term → Path V}
  {Γ : Context U} {Δ : Context V} {M} {A} →
  ρ ∶ Γ ⇒ Δ → σ ∶ Γ ⇒ Δ →
  (∀ x → Δ ⊢ τ x ∶ ρ _ x ≡〈 close (typeof x Γ) 〈 magic 〉 〉 σ _ x) →
  Γ ⊢ M ∶ A → Δ ⊢ pathsub τ M ∶ M ⟦ ρ ⟧ ≡〈 close A 〈 magic 〉 〉 M ⟦ σ ⟧
pathsub-wd ρ∶Γ→Δ σ∶Γ→Δ τ∶ρ≡σ (varR _) = τ∶ρ≡σ _
pathsub-wd ρ∶Γ→Δ σ∶Γ→Δ τ∶ρ≡σ ⊥R = refR ⊥R
pathsub-wd ρ∶Γ→Δ σ∶Γ→Δ τ∶ρ≡σ (impR Γ⊢M∶A Γ⊢M∶A₁) = imp*R (pathsub-wd ρ∶Γ→Δ σ∶Γ→Δ τ∶ρ≡σ Γ⊢M∶A) (pathsub-wd ρ∶Γ→Δ σ∶Γ→Δ τ∶ρ≡σ Γ⊢M∶A₁)
pathsub-wd ρ∶Γ→Δ σ∶Γ→Δ τ∶ρ≡σ (appR Γ⊢M∶A Γ⊢M∶A₁) = app*R (pathsub-wd ρ∶Γ→Δ σ∶Γ→Δ τ∶ρ≡σ Γ⊢M∶A) (pathsub-wd ρ∶Γ→Δ σ∶Γ→Δ τ∶ρ≡σ Γ⊢M∶A₁)
pathsub-wd {ρ = ρ} {σ} {τ = τ} .{M = ΛT A M} ρ∶Γ→Δ σ∶Γ→Δ τ∶ρ≡σ (ΛR {A = A} {M} Γ,A⊢M∶B) = lllR (convER 
  (subst₂
     (λ D A₁ →
        D ⊢ pathsub (pathsub↑ τ) M ∶ M ⟦ sub↖ ρ ⟧ ≡〈 A₁ 〉 M ⟦ sub↗ σ ⟧)
     {!!} {!!} (pathsub-wd {!!} {!!} {!!} Γ,A⊢M∶B)) 
     (appR (ΛR {!!}) {!!}) 
     {!!} 
     {!!} 
     {!!})-}
--TODO Relabel variables
\end{code}
\end{frame}
