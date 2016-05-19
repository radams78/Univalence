\AgdaHide{
\begin{code}
module PHOPL.PathSub where
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Rules
open import PHOPL.Close
open import PHOPL.Meta
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

sub↖ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (V , -Term , -Term , -Path)
sub↖ σ _ x₀ = var x₂
sub↖ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

sub↗ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (V , -Term , -Term , -Path)
sub↗ σ _ x₀ = var x₁
sub↗ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

pathsub↑ : ∀ {U} {V} → PathSub U V → PathSub (U , -Term) (V , -Term , -Term , -Path)
pathsub↑ τ x₀ = var x₀
pathsub↑ τ (↑ x) = τ x ⇑ ⇑ ⇑

infix 70 _⟦⟦_∶_∼_⟧⟧
_⟦⟦_∶_∼_⟧⟧ : ∀ {U} {V} → Term U → PathSub U V → Sub U V → Sub U V → Path V
var x ⟦⟦ τ ∶ _ ∼ _ ⟧⟧ = τ x
app -bot out ⟦⟦ τ ∶ _ ∼ _ ⟧⟧ = reff ⊥
app -imp (φ ,, ψ ,, out) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ = φ ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ⊃* ψ ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧
app -appTerm (M ,, N ,, out) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ = app* (N ⟦ ρ ⟧) (N ⟦ σ ⟧) (M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧) (N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧)
app -lamTerm (A ,, M ,, out) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ = λλλ (A ⟦ ρ ⟧) (M ⟦⟦ pathsub↑ τ ∶ sub↖ ρ ∼ sub↗ σ ⟧⟧)
\end{code}

\begin{prop}
If $\Gamma, x : A \vdash M : B$ and $\Gamma \vdash P : N =_A N'$ then
$\Gamma \vdash \{ P / x \} M : [N / x] M =_B [N' / x] M$.
\end{prop}

\begin{code}
_∶_∼_∶_⇒_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ σ ∼ σ' ∶ Γ ⇒ Δ = ∀ x → Δ ⊢ τ x ∶ σ -Term x ≡〈 ty (typeof x Γ) 〉 σ' -Term x

pathsub↑-typed : pathsub↑ τ ∶ sub↖ ρ ∼ sub↗ σ ∶ Γ , A ⇒ Δ , ty A , ty A , var x₁ ≡〈 ty A 〉 var x₀

Substitution-ty : ∀ {U} {V} {Γ : Context U} {M : Term U} {A : Type U} {Δ : Context V} {σ} → Γ ⊢ M ∶ A → valid Δ → σ ∶ Γ ⇒ Δ → Δ ⊢ M ⟦ σ ⟧ ∶ ty A
Substitution-ty {A = A} Γ⊢M∶A validΔ σ∶Γ⇒Δ = change-type (Substitution Γ⊢M∶A validΔ σ∶Γ⇒Δ) (trans (sym close-magic) (ty-sub A))

Path-Substitution : ∀ {U} {V} {Γ : Context U} {Δ : Context V} 
  {ρ} {σ} {τ} {M} {A} →
  Γ ⊢ M ∶ A → τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ → ρ ∶ Γ ⇒ Δ → σ ∶ Γ ⇒ Δ → valid Δ → 
  Δ ⊢ M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ∶ M ⟦ ρ ⟧ ≡〈 ty A 〉 M ⟦ σ ⟧
Path-Substitution (varR x validΓ) τ∶ρ∼σ _ _ _ = τ∶ρ∼σ x
Path-Substitution (⊥R validΓ) _ _ _ validΔ = refR (⊥R validΔ)
Path-Substitution (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) τ∶ρ∼σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = ⊃*R (Path-Substitution Γ⊢φ∶Ω τ∶ρ∼σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ) (Path-Substitution Γ⊢ψ∶Ω τ∶ρ∼σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ)
Path-Substitution (appR {A = A} Γ⊢M∶A⇛B Γ⊢N∶A) τ∶σ∼σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = 
  app*R (Substitution-ty Γ⊢N∶A validΔ ρ∶Γ⇒Δ) (Substitution-ty Γ⊢N∶A validΔ σ∶Γ⇒Δ)
  (Path-Substitution Γ⊢M∶A⇛B τ∶σ∼σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ) (Path-Substitution Γ⊢N∶A τ∶σ∼σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ)
Path-Substitution {ρ = ρ} {σ} (ΛR {V} {Γ} {A} {M} {B} Γ,A⊢M∶B) τ∶σ∼σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = change-type {A = ΛT A M ⟦ ρ ⟧ ≡〈 (A ⟦ ρ ⟧) ⇛ ty B 〉 ΛT A M ⟦ σ ⟧} 
  (lllR (convER (change-type (Path-Substitution Γ,A⊢M∶B {!!} {!!} {!!} {!!}) {!!}) {!!} {!!} {!!} {!!})) {!!}

\end{code}

\AgdaHide{
\begin{code}
_∼∼_ : ∀ {U} {V} → PathSub U V → PathSub U V → Set
τ ∼∼ τ' = ∀ x → τ x ≡ τ' x

postulate ∼∼-refl : ∀ {U} {V} {τ : PathSub U V} → τ ∼∼ τ

--REFACTOR
postulate idPathSub : ∀ V → PathSub V V

infixr 75 _•RP_
_•RP_ : ∀ {U} {V} {W} → Rep V W → PathSub U V → PathSub U W
(ρ •RP τ) x = τ x 〈 ρ 〉

extendPS : ∀ {U} {V} → PathSub U V → Path V → PathSub (U , -Term) V
extendPS τ P x₀ = P
extendPS τ P (↑ x) = τ x

postulate pathsub-extendPS : ∀ {U} {V} M {τ} {P : Path V} {N : Term V} {σ : Sub U V} {N' : Term V} {σ'} →
                           M ⟦⟦ extendPS τ P ∶ x₀:= N • Sub↑ -Term σ ∼ x₀:= N' • Sub↑ -Term σ' ⟧⟧
                           ≡ M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (P ⇑ ⇑) ⟧

postulate pathsub-cong : ∀ {U} {V} M {τ τ' : PathSub U V} {ρ} {ρ'} {σ} {σ'} →
                       τ ∼∼ τ' → ρ ∼ ρ' → σ ∼ σ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ≡ M ⟦⟦ τ' ∶ ρ' ∼ σ' ⟧⟧

postulate pathsub↑-compRP : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} →
                          pathsub↑ (ρ •RP τ) ∼∼ Rep↑ -Path (Rep↑ -Term (Rep↑ -Term ρ)) •RP pathsub↑ τ

postulate sub↖-comp₁ : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
                     sub↖ (ρ •₁ σ) ∼ Rep↑ -Path (Rep↑ -Term (Rep↑ -Term ρ)) •₁ sub↖ σ

postulate sub↗-comp₁ : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
                     sub↗ (ρ •₁ σ) ∼ Rep↑ -Path (Rep↑ -Term (Rep↑ -Term ρ)) •₁ sub↗ σ

postulate Rep↑↑↑-pathsub : ∀ {U} {V} {W} M {ρ : Rep V W} {τ : PathSub U V} {σ σ' : Sub U V} →
                         M ⟦⟦ ρ •RP τ ∶ ρ •₁ σ ∼ ρ •₁ σ' ⟧⟧ ≡ M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧ 〈 ρ 〉

x₀::= : ∀ {V} → Path V → PathSub (V , -Term) V
(x₀::= P) x₀ = P
(x₀::= P) (↑ x) = reff (var x)

_⋆[_∶_∼_] : ∀ {V} → Term V → Path V → Term V → Term V → Path V
M ⋆[ P ∶ N ∼ N' ] = (appT (M ⇑) (var x₀)) ⟦⟦ x₀::= P ∶ x₀:= N ∼ x₀:= N' ⟧⟧
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

postulate pathsub↑-typed : ∀ {U} {V} {τ : PathSub U V} {ρ σ : Sub U V} {Γ} {Δ} {A} →
                           τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ → pathsub↑ τ ∶ sub↖ ρ ∼ sub↗ σ ∶ Γ , A ⇒ Δ , ty A , ty A , var x₁ ≡〈 ty A 〉 var x₀

postulate extendPS-typed : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} {P} {M} {N} {A} →
                           τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ → Δ ⊢ P ∶ M ≡〈 close A 〈 magic 〉 〉 N →
                           extendPS τ P ∶ extendSub ρ M ∼ extendSub σ N ∶ Γ , A ⇒ Δ

postulate compRP-typed : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} {σ σ' : Sub U V}
                           {Γ} {Δ} {Θ} →
                           ρ ∶ Δ ⇒R Θ → τ ∶ σ ∼ σ' ∶ Γ ⇒ Δ →
                           ρ •RP τ ∶ ρ •₁ σ ∼ ρ •₁ σ' ∶ Γ ⇒ Θ

\end{code}
\end{frame}
