\AgdaHide{
\begin{code}
--TODO Module parameters
module PHOPL.PathSub where
open import Prelims
open import PHOPL.Grammar
\end{code}
}

\subsection{Path Substitution}

Intuitively, if $N$ and $N'$ are equal then $M[x:=N]$ and $M[x:=N']$ should be equal.  To handle this syntactically,
we introduce a notion of \emph{path substitution}.  If $N$, $M$ and $M'$ are terms, $x$ a term variable, and $P$ a path, then we shall define a path $N \{ x := P : M \sim M' \}$.  The intention is that, if
$\Gamma \vdash P : M =_A M'$ and $\Gamma, x : A \vdash N : B$ then $\Gamma \vdash N \{ x := P : M \sim M' \} : N [ x:= M ] =_B N [ x := M' ]$ (see Lemma \ref{lm:pathsub}). 

\begin{definition}[Path Substitution]
Given terms $M_1$, \ldots, $M_n$ and $N_1$, \ldots, $N_n$; paths $P_1$, \ldots, $P_n$; term variables $x_1$, \ldots, $x_n$; and a term $L$, define the path $L \{ x_1 := P_1 : M_1 \sim N_1 , \ldots, x_n := P_n : M_n \sim N_n \}$ as follows.
\begin{align*}
x_i \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} & \eqdef P_i \\
y \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} & \eqdef \reff{y} \qquad (y \not\equiv x_1, \ldots, x_n) \\
\bot \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} & \eqdef \reff{\bot} \\
(LL') \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} \\
\omit\rlap{\qquad \qquad $\eqdef L \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \}_{L' [\vec{x} := \vec{M}] L' [\vec{x} := \vec{N}]} L' \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \}$} \\
(\lambda y:A.L) \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} & \\
\omit\rlap{\qquad\qquad $\eqdef \triplelambda e : a =_A a' . L \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} , y := e : a \sim a' \}$} \\
(\phi \supset \psi) \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} & \eqdef \phi \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} \supset^* \psi \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \}
\end{align*}
\end{definition}

We shall often omit the endpoints $\vec{M}$ and $\vec{N}$.

\paragraph{Note}
The case $n = 0$ is permitted, and we shall have that, if $\Gamma \vdash M : A$ then $\Gamma \vdash M \{\} : M =_A M$.  There are thus two paths from a term $M$ to itself: $\reff{M}$ and $M \{\}$.  There are not always equal; for example, $(\lambda x:A.x) \{\} \equiv \triplelambda e : x =_A y. e$, which (after we define the reduction relation) will not be convertible with $\reff{\lambda x:A.x}$.  

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

liftPathSub : ∀ {U} {V} → PathSub U V → PathSub (U , -Term) (V , -Term , -Term , -Path)
liftPathSub τ x₀ = var x₀
liftPathSub τ (↑ x) = τ x ⇑ ⇑ ⇑

liftPathSub-cong : ∀ {U} {V} {τ τ' : PathSub U V} → τ ∼∼ τ' → liftPathSub τ ∼∼ liftPathSub τ'
liftPathSub-cong _ x₀ = refl
liftPathSub-cong τ∼∼τ' (↑ x) = rep-congl (rep-congl (rep-congl (τ∼∼τ' x)))

infix 70 _⟦⟦_∶_∼_⟧⟧
\end{code}
}

\begin{code}
_⟦⟦_∶_∼_⟧⟧ : ∀ {U} {V} → Term U → PathSub U V → 
  Sub U V → Sub U V → Path V
var x ⟦⟦ τ ∶ _ ∼ _ ⟧⟧ = τ x
app -bot [] ⟦⟦ τ ∶ _ ∼ _ ⟧⟧ = reff ⊥
app -imp (φ ∷ ψ ∷ []) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ = φ ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ⊃* ψ ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧
app -appTerm (M ∷ N ∷ []) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ = app* (N ⟦ ρ ⟧) (N ⟦ σ ⟧) (M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧) (N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧)
app (-lamTerm A) (M ∷ []) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ = λλλ A (M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ∼ sub↗ σ ⟧⟧)
\end{code}

\AgdaHide{
\begin{code}
pathSub-cong : ∀ {U} {V} M {τ τ' : PathSub U V} {ρ} {ρ'} {σ} {σ'} →
               τ ∼∼ τ' → ρ ∼ ρ' → σ ∼ σ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ≡ M ⟦⟦ τ' ∶ ρ' ∼ σ' ⟧⟧
pathSub-cong (var x) τ∼∼τ' _ _ = τ∼∼τ' x
pathSub-cong (app -bot []) _ _ _ = refl
pathSub-cong (app -imp (φ ∷ ψ ∷ [])) τ∼∼τ' ρ∼ρ' σ∼σ' = 
  cong₂ _⊃*_ (pathSub-cong φ τ∼∼τ' ρ∼ρ' σ∼σ') 
             (pathSub-cong ψ τ∼∼τ' ρ∼ρ' σ∼σ')
pathSub-cong (app -appTerm (M ∷ N ∷ [])) τ∼∼τ' ρ∼ρ' σ∼σ' = 
  cong₄ app* (sub-congr N ρ∼ρ') (sub-congr N σ∼σ')
             (pathSub-cong M τ∼∼τ' ρ∼ρ' σ∼σ') 
             (pathSub-cong N τ∼∼τ' ρ∼ρ' σ∼σ')
pathSub-cong (app (-lamTerm A) (M ∷ [])) τ∼∼τ' ρ∼ρ' σ∼σ' = 
  cong (λλλ A) (pathSub-cong M (liftPathSub-cong τ∼∼τ') 
               (sub↖-cong ρ∼ρ') (sub↗-cong σ∼σ'))

x₀::= : ∀ {V} → Path V → PathSub (V , -Term) V
(x₀::= P) x₀ = P
(x₀::= P) (↑ x) = reff (var x)
\end{code}
}

\AgdaHide{
\begin{code}
_⋆[_∶_∼_] : ∀ {V} → Term V → Path V → Term V → Term V → Path V
M ⋆[ P ∶ N ∼ N' ] = app* N N' (reff M) P
\end{code}
}

\begin{lm}
\[ M \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N} \} \equiv M \{ \vec{x} := \vec{P} : \vec{M} \sim \vec{N}, y := \reff{y} : y \sim y \} \]
\end{lm}

\begin{proof}
An easy induction on $M$.
\end{proof}

The following lemma shows how substitution and path substitution interact.

\begin{lm}[Substitution]
\label{lm:subpathsub}
Let $\vec{x}$ and $\vec{y}$ be a disjoint sequences of variables.  Then
\begin{enumerate}
\item
\label{lm:subpathsubi}
$ \begin{aligned}[t]
& M [ x:= N ] \{ \vec{y} := \vec{P} : \vec{L} \sim \vec{L'} \} \\
& \equiv M \{ x := N \{ \vec{y} := \vec{P} : \vec{L} \sim \vec{L'} \} : N [ \vec{y}:= \vec{L} ] \sim N [ \vec{y} := \vec{L'} ], \vec{y} := \vec{P} : \vec{L} \sim \vec{L'} \}
\end{aligned} $
\item
\label{lm:subpathsubii}
$ \begin{aligned}[t]
& M \{ \vec{y} := \vec{P} : \vec{L} \sim \vec{L'} \} [ x := N ] \\
& \equiv M \{ \vec{y} := \vec{P} [x := N] : \vec{L} [x := N] \sim \vec{L'} [x := N], x := \reff{N} : N \sim N \}
\end{aligned} $
\end{enumerate}
\end{lm}

\begin{proof}
An easy induction on $M$ in all cases.
\end{proof}

\paragraph{Note}
The familiar substitution lemma also holds: $t [\vec{z_1} := \vec{s_1}] [\vec{z_2} := \vec{s_2}] \equiv t [\vec{z_1} := \vec{s_1}[\vec{z_2} := \vec{s_2}], 
\vec{z_2} := \vec{s_2}]$.  We cannot form a lemma about the fourth case, simplifying $M \{ \vec{x} := \vec{P} \} \{ \vec{y} := \vec{Q} \}$, because
$M \{ \vec{x} := \vec{P} \}$ is a path, and path substitution can only be applied to a term.

\begin{definition}
A \emph{path substitution} $\tau$ is a function whose domain is a finite set of term variables,
and which maps each term variable to a path.  Given a path substitution $\tau$ and substitutions $\rho$, $\sigma$
with the same domain $\{ x_1, \ldots, x_n \}$, we write
\[ M \{ \tau : \rho \sim \sigma \} \text{ for } M \{ x_1 := \tau(x_1) : \rho(x_1) \sim \sigma(x_1), \ldots, \tau(x_n) : \rho(x_n) \sim \sigma(x_n) \} \enspace . \]

Given substitutions $\sigma$, $\rho$, $\rho'$ and a path substitution $\tau$, let $\tau \bullet_{\rho, \rho'} \sigma$ be the path substitution defined by
\[ (\tau \bullet_{\rho, \rho'} \sigma)(x) \eqdef \sigma(x)\{ \tau : \rho \sim \rho' \} \]
\end{definition}

\begin{lemma}
$M[\sigma]\{ \tau : \rho \sim \rho' \} \equiv
M\{ \tau \bullet_{\rho \rho'} \sigma : \rho \circ \sigma \sim \rho' \circ \sigma \}$
\end{lemma}

\begin{proof}
An easy induction on $M$.
\end{proof}

\begin{code}
refSub : ∀ {V} → PathSub V V
refSub x = reff (var x)

_•PR_ : ∀ {U V W} → PathSub V W → Rep U V → PathSub U W
(τ •PR ρ) x = τ (ρ -Term x)

liftPathSub-•PR : ∀ {U V W} {τ : PathSub V W} {ρ : Rep U V} →
  liftPathSub (τ •PR ρ) ∼∼ (liftPathSub τ •PR liftRep _ ρ)
liftPathSub-•PR x₀ = refl
liftPathSub-•PR (↑ x) = refl

pathSub-•PR : ∀ {U V W} M {ρ : Rep U V} {τ : PathSub V W} {σ σ'} →
  M 〈 ρ 〉 ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧ ≡ M ⟦⟦ τ •PR ρ ∶ σ •SR ρ ∼ σ' •SR ρ ⟧⟧
pathSub-•PR (var x) = refl
pathSub-•PR (app -bot []) = refl
pathSub-•PR (app -imp (φ ∷ ψ ∷ [])) = cong₂ _⊃*_ (pathSub-•PR φ) (pathSub-•PR ψ)
pathSub-•PR (app (-lamTerm A) (M ∷ [])) {ρ} {τ} {σ} {σ'} = 
  cong (λλλ A) (let open ≡-Reasoning in
    M 〈 liftRep _ ρ 〉 ⟦⟦ liftPathSub τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧
  ≡⟨ pathSub-•PR M ⟩
    M ⟦⟦ liftPathSub τ •PR liftRep _ ρ ∶ sub↖ σ •SR liftRep _ ρ ∼ sub↗ σ' •SR liftRep _ ρ ⟧⟧
  ≡⟨⟨ pathSub-cong M liftPathSub-•PR sub↖-•SR sub↗-•SR ⟩⟩
    M ⟦⟦ liftPathSub (τ •PR ρ) ∶ sub↖ (σ •SR ρ) ∼ sub↗ (σ' •SR ρ) ⟧⟧
  ∎)
pathSub-•PR (app -appTerm (M ∷ N ∷ [])) = cong₄ app* (sym (sub-•SR N)) (sym (sub-•SR N)) (pathSub-•PR M) (pathSub-•PR N)

_∶_≡_•PS_ : ∀ {U V W} → PathSub V W → Sub V W → Sub V W → Sub U V → PathSub U W
(τ ∶ σ ≡ σ' •PS ρ) x = ρ _ x ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧

infixr 75 _•RP_
_•RP_ : ∀ {U} {V} {W} → Rep V W → PathSub U V → PathSub U W
(ρ •RP τ) x = τ x 〈 ρ 〉

postulate pathSub-•RP : ∀ {U} {V} {W} M {ρ : Rep V W} {τ : PathSub U V} {σ σ' : Sub U V} →
                         M ⟦⟦ ρ •RP τ ∶ ρ •RS σ ∼ ρ •RS σ' ⟧⟧ ≡ M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧ 〈 ρ 〉

liftPathSub-PS : ∀ {U V W} {τ : PathSub V W} {ρ ρ' : Sub V W} {σ : Sub U V} →
  liftPathSub (τ ∶ ρ ≡ ρ' •PS σ) ∼∼ (liftPathSub τ ∶ sub↖ ρ ≡ sub↗ ρ' •PS liftSub _ σ)
liftPathSub-PS x₀ = refl
liftPathSub-PS {τ = τ} {ρ} {ρ'} {σ} (↑ x) = let open ≡-Reasoning in
  begin
    σ _ x ⟦⟦ τ ∶ ρ ∼ ρ' ⟧⟧ ⇑ ⇑ ⇑
  ≡⟨⟨ rep-congl (rep-congl (pathSub-•RP (σ _ x))) ⟩⟩
    σ _ x ⟦⟦ upRep •RP τ ∶ upRep •RS ρ ∼ upRep •RS ρ' ⟧⟧ ⇑ ⇑
  ≡⟨⟨ rep-congl (pathSub-•RP (σ _ x)) ⟩⟩
    σ _ x ⟦⟦ upRep •RP (upRep •RP τ) ∶ upRep •RS (upRep •RS ρ) ∼ upRep •RS (upRep •RS ρ') ⟧⟧ ⇑
  ≡⟨⟨ pathSub-•RP (σ _ x) ⟩⟩
    σ _ x ⟦⟦ upRep •RP (upRep •RP (upRep •RP τ)) ∶ upRep •RS (upRep •RS (upRep •RS ρ)) ∼ upRep •RS (upRep •RS (upRep •RS ρ')) ⟧⟧
  ≡⟨⟩
    σ _ x ⟦⟦ liftPathSub τ •PR upRep ∶ sub↖ ρ •SR upRep ∼ sub↗ ρ' •SR upRep ⟧⟧
  ≡⟨⟨ pathSub-•PR (σ _ x) ⟩⟩
    σ _ x ⇑ ⟦⟦ liftPathSub τ ∶ sub↖ ρ ∼ sub↗ ρ' ⟧⟧
  ∎

pathsub-sub : ∀ {U V W} M {σ : Sub U V} {τ : PathSub V W} {ρ ρ'} →
  M ⟦ σ ⟧ ⟦⟦ τ ∶ ρ ∼ ρ' ⟧⟧ ≡ M ⟦⟦ τ ∶ ρ ≡ ρ' •PS σ ∶ ρ • σ ∼ ρ' • σ ⟧⟧
pathsub-sub (var x) = refl
pathsub-sub (app -bot []) = refl
pathsub-sub (app -imp (φ ∷ ψ ∷ [])) = cong₂ _⊃*_ (pathsub-sub φ) (pathsub-sub ψ)
pathsub-sub (app (-lamTerm A) (M ∷ [])) {σ} {τ} {ρ} {ρ'} = cong (λλλ A) (let open ≡-Reasoning in
  begin
    M ⟦ liftSub _ σ ⟧ ⟦⟦ liftPathSub τ ∶ sub↖ ρ ∼ sub↗ ρ' ⟧⟧
  ≡⟨ pathsub-sub M ⟩
    M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ ρ' •PS liftSub _ σ ∶ sub↖ ρ • liftSub _ σ ∼ sub↗ ρ' • liftSub _ σ ⟧⟧
  ≡⟨⟨ pathSub-cong M liftPathSub-PS sub↖-• sub↗-• ⟩⟩
    M ⟦⟦ liftPathSub (τ ∶ ρ ≡ ρ' •PS σ) ∶ sub↖ (ρ • σ) ∼ sub↗ (ρ' • σ) ⟧⟧
  ∎)
pathsub-sub (app -appTerm (M ∷ N ∷ [])) = cong₄ app* (sym (sub-comp N)) (sym (sub-comp N)) (pathsub-sub M) (pathsub-sub N)

extendPS : ∀ {U} {V} → PathSub U V → Path V → PathSub (U , -Term) V
extendPS τ P x₀ = P
extendPS τ P (↑ x) = τ x

•PS-botsub : ∀ {U V} {τ : PathSub U V} {ρ σ N} → (τ ∶ ρ ≡ σ •PS (x₀:= N)) ∼∼ extendPS τ (N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧)
•PS-botsub x₀ = refl
•PS-botsub (↑ _) = refl
\end{code}
