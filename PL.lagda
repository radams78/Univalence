\begin{code}
module PL where
open import Prelims
\end{code}

\section{Propositional Logic}

Fix sets of \emph{proof variables} and \emph{term variables}.

The syntax of the system is given by the following grammar.

\newcommand{\vald}{\ensuremath{\ \mathrm{valid}}}
%Changes from Marc and Thierry's system:
%Taken out the proof c of \bot
\[ \begin{array}{lrcl}
\text{Proof} & \delta & ::= & p \mid \delta \delta \mid \lambda p : \phi . \delta \\
\text{Proposition} & φ & ::= & ⊥ \mid \phi \rightarrow \phi \\
\text{Proof Context} & \Delta & ::= & \langle \rangle \mid \Delta, p : \phi \\
\text{Judgement} & \mathcal{J} & ::= & \Delta \vdash \delta : \phi
\end{array} \]
where $p$ ranges over proof variables and $x$ ranges over term variables.  The variable $p$ is bound within $\delta$ in the proof $\lambda p : \phi . \delta$,
and the variable $x$ is bound within $M$ in the term $\lambda x : A . M$.  We identify proofs and terms up to $\alpha$-conversion.

\newcommand{\FV}[1]{\mathrm{FV} \left( {#1} \right)}
\newcommand{\Proof}[1]{\mathbf{Proof} \left( {#1} \right)}
We write $\Proof{P}$ for the set of all proofs $\delta$ with $\FV{\delta} \subseteq V$.

\begin{code}
infix 75 _⇒_
data Prp : Set where
  ⊥ : Prp
  _⇒_ : Prp → Prp → Prp

infix 80 _,_
data PContext : FinSet → Set where
  〈〉 : PContext ∅
  _,_ : ∀ {P} → PContext P → Prp → PContext (Lift P)

--Proof V P is the set of all proofs with term variables among V and proof variables among P
data Proof : FinSet → Set where
  var : ∀ {P} → El P → Proof P
  app : ∀ {P} → Proof P → Proof P → Proof P
  Λ : ∀ {P} → Prp → Proof (Lift P) → Proof P
\end{code}

Let $U, V : \FinSet$.  A \emph{replacement} from $U$ to $V$ is just a function $U \rightarrow V$.  Given a term $M : \Proof{U}$
and a replacement $\rho : U \rightarrow V$, we write $M \{ \rho \} : \Proof{V}$ for the result of replacing each variable $x$ in
$M$ with $\rho(x)$.

\begin{code}
infix 60 _<_>
_<_> : ∀ {U V} → Proof U → Rep U V → Proof V
var p < ρ > = var (ρ p)
app δ ε < ρ > = app (δ < ρ >) (ε < ρ >)
Λ φ δ < ρ > = Λ φ (δ < lift ρ >)
\end{code}

With this as the action on arrows, $\Proof{}$ becomes a functor $\FinSet \rightarrow \Set$.

\begin{code}
repwd : ∀ {U V : FinSet} {ρ ρ' : El U → El V} → ρ ∼ ρ' → ∀ δ → δ < ρ > ≡ δ < ρ' >
repwd ρ-is-ρ' (var p) = wd var (ρ-is-ρ' p)
repwd ρ-is-ρ' (app δ ε) = wd2 app (repwd ρ-is-ρ' δ) (repwd ρ-is-ρ' ε)
repwd ρ-is-ρ' (Λ φ δ) = wd (Λ φ) (repwd (liftwd ρ-is-ρ') δ)

repid : ∀ {V : FinSet} δ → δ < id (El V) > ≡ δ
repid (var _) = ref
repid (app δ ε) = wd2 app (repid δ) (repid ε)
repid {V} (Λ φ δ) = wd (Λ φ) (let open Equational-Reasoning (Proof (Lift V)) in 
  ∵ δ < lift (id (El V)) >
  ≡ δ < id (El (Lift V)) >  [ repwd liftid δ ]
  ≡ δ                       [ repid δ ])

repcomp : ∀ {U V W : FinSet} (ρ : El V → El W) (σ : El U → El V) M → M < ρ ∘ σ > ≡ M < σ > < ρ >
repcomp ρ σ (var _) = ref
repcomp ρ σ (app δ ε) = wd2 app (repcomp ρ σ δ) (repcomp ρ σ ε)
repcomp {W = W} ρ σ (Λ A δ) = wd (Λ A) (let open Equational-Reasoning (Proof (Lift W)) in 
  ∵ δ < lift (ρ ∘ σ) >
  ≡ δ < lift ρ ∘ lift σ >     [ repwd liftcomp δ ]
  ≡ (δ < lift σ >) < lift ρ > [ repcomp _ _ δ ])
\end{code}

A \emph{substitution} $\sigma$ from $U$ to $V$, $\sigma : U \Rightarrow V$, is a function $\sigma : U \rightarrow \Proof{V}$.

\begin{code}
Sub : FinSet → FinSet → Set
Sub U V = El U → Proof V
\end{code}

The identity substitution $\id{V} : V \Rightarrow V$ is defined as follows.

\begin{code}
idSub : ∀ V → Sub V V
idSub _ = var
\end{code}

Given $\sigma : U \Rightarrow V$ and $M : \Proof{U}$, we want to define $M[\sigma] : \Proof{V}$, the result of applying the substitution $\sigma$ to $M$.  Only after this will we be able to define the composition of two substitutions.  However, there is some work we need to do before we are able to do this.

We can define the composition of a substitution and a replacement as follows.
\begin{code}
infix 75 _•₁_
_•₁_ : ∀ {U} {V} {W} → Rep V W → Sub U V → Sub U W
(ρ •₁ σ) u = σ u < ρ >
\end{code}

(On the other side, given $\rho : U \rightarrow V$ and $\sigma : V \Rightarrow W$, the composition is just function composition $\sigma \circ \rho : U \Rightarrow W$.)

Given a substitution $\sigma : U \Rightarrow V$,  define the substitution $\sigma + 1 :
U + 1 \Rightarrow V + 1$ as follows.

\begin{code}
liftSub : ∀ {U} {V} → Sub U V → Sub (Lift U) (Lift V)
liftSub _ ⊥ = var ⊥
liftSub σ (↑ x) = σ x < ↑ >

liftSub-wd : ∀ {U V} {σ σ' : Sub U V} → σ ∼ σ' → liftSub σ ∼ liftSub σ'
liftSub-wd σ-is-σ' ⊥ = ref
liftSub-wd σ-is-σ' (↑ x) = wd (λ x → x < ↑ >) (σ-is-σ' x)
\end{code}

\begin{lemma}
The operations $\bullet$ and $(-) + 1$ satisfiesd the following properties.
\begin{enumerate}
\item
$\id{V} + 1 = \id{V + 1}$
\item
For $\rho : V → W$ and $\sigma : U \Rightarrow V$, we have $(\rho \bullet \sigma) + 1 = (\rho + 1) \bullet (\sigma + 1)$.
\item
For $\sigma : V \Rightarrow W$ and $\rho : U \rightarrow V$, we have $(\sigma \circ \rho) + 1 = (\sigma + 1) \circ (\rho + 1)$.
\end{enumerate}
\end{lemma}

\begin{code}
liftSub-id : ∀ {V : FinSet} → liftSub (idSub V) ∼ idSub (Lift V)
liftSub-id ⊥ = ref
liftSub-id (↑ x) = ref

liftSub-comp₁ : ∀ {U V W : FinSet} (σ : Sub U V) (ρ : Rep V W) → 
  liftSub (ρ •₁ σ) ∼ lift ρ •₁ liftSub σ
liftSub-comp₁ σ ρ ⊥ = ref
liftSub-comp₁ {W = W} σ ρ (↑ x) = let open Equational-Reasoning (Proof (Lift W)) in 
   ∵ σ x < ρ > < ↑ > 
   ≡ σ x < ↑ ∘ ρ >        [[ repcomp ↑ ρ (σ x) ]]
   ≡ σ x < ↑ > < lift ρ > [ repcomp (lift ρ) ↑ (σ x) ]
--because lift ρ (↑ x) = ↑ (ρ x)

liftSub-comp₂ : ∀ {U V W : FinSet} (σ : Sub V W) (ρ : Rep U V) →
  liftSub (σ ∘ ρ) ∼ liftSub σ ∘ lift ρ
liftSub-comp₂ σ ρ ⊥ = ref
liftSub-comp₂ σ ρ (↑ x) = ref
\end{code}

Now define $M[\sigma]$ as follows.

\begin{code}
--Term is a monad with unit var and the following multiplication
infix 60 _⟦_⟧
_⟦_⟧ : ∀ {U V : FinSet} → Proof U → Sub U V → Proof V
(var x)   ⟦ σ ⟧ = σ x
(app M N) ⟦ σ ⟧ = app (M ⟦ σ ⟧) (N ⟦ σ ⟧)
(Λ A M)   ⟦ σ ⟧ = Λ A (M ⟦ liftSub σ ⟧)

subwd : ∀ {U V : FinSet} {σ σ' : Sub U V} → σ ∼ σ' → ∀ M → M ⟦ σ ⟧ ≡ M ⟦ σ' ⟧
subwd σ-is-σ' (var x) = σ-is-σ' x
subwd σ-is-σ' (app M N) = wd2 app (subwd σ-is-σ' M) (subwd σ-is-σ' N)
subwd σ-is-σ' (Λ A M) = wd (Λ A) (subwd (liftSub-wd σ-is-σ') M)
\end{code}

This interacts with our previous operations in a good way:
\begin{lemma}
\begin{enumerate}
\item
$M[\id{V}] \equiv M$
\item
$M[\rho \bullet \sigma] \equiv M [ \sigma ] \{ \rho \}$
\item
$M[\sigma \circ \rho] \equiv M < \rho > [ \sigma ]$
\end{enumerate}
\end{lemma}

\begin{code}
subid : ∀ {V : FinSet} (M : Proof V) → M ⟦ idSub V ⟧ ≡ M
subid (var x) = ref
subid (app M N) = wd2 app (subid M) (subid N)
subid {V} (Λ A M) = let open Equational-Reasoning (Proof V) in 
  ∵ Λ A (M ⟦ liftSub (idSub V) ⟧)
  ≡ Λ A (M ⟦ idSub (Lift V) ⟧)     [ wd (Λ A) (subwd liftSub-id M) ]
  ≡ Λ A M                          [ wd (Λ A) (subid M) ]

rep-sub : ∀ {U} {V} {W} (σ : Sub U V) (ρ : Rep V W) (M : Proof U) → M ⟦ σ ⟧ < ρ > ≡ M ⟦ ρ •₁ σ ⟧
rep-sub σ ρ (var x) = ref
rep-sub σ ρ (app M N) = wd2 app (rep-sub σ ρ M) (rep-sub σ ρ N)
rep-sub {W = W} σ ρ (Λ A M) = let open Equational-Reasoning (Proof W) in 
  ∵ Λ A ((M ⟦ liftSub σ ⟧) < lift ρ >) 
  ≡ Λ A (M ⟦ lift ρ •₁ liftSub σ ⟧) [ wd (Λ A) (rep-sub (liftSub σ) (lift ρ) M) ]
  ≡ Λ A (M ⟦ liftSub (ρ •₁ σ) ⟧)    [[ wd (Λ A) (subwd (liftSub-comp₁ σ ρ) M) ]]

sub-rep : ∀ {U} {V} {W} (σ : Sub V W) (ρ : Rep U V) M → M < ρ > ⟦ σ ⟧ ≡ M ⟦ σ ∘ ρ ⟧
sub-rep σ ρ (var x) = ref
sub-rep σ ρ (app M N) = wd2 app (sub-rep σ ρ M) (sub-rep σ ρ N)
sub-rep {W = W} σ ρ (Λ A M) = let open Equational-Reasoning (Proof W) in 
  ∵ Λ A ((M < lift ρ >) ⟦ liftSub σ ⟧)
  ≡ Λ A (M ⟦ liftSub σ ∘ lift ρ ⟧)      [ wd (Λ A) (sub-rep (liftSub σ) (lift ρ) M) ]
  ≡ Λ A (M ⟦ liftSub (σ ∘ ρ) ⟧)         [[ wd (Λ A) (subwd (liftSub-comp₂ σ ρ) M) ]]
\end{code}

We define the composition of two substitutions, as follows.

\begin{code}
infix 75 _•_
_•_ : ∀ {U V W : FinSet} → Sub V W → Sub U V → Sub U W
(σ • ρ) x = ρ x ⟦ σ ⟧
\end{code}

\begin{lemma}
Let $\sigma : V \Rightarrow W$ and $\rho : U \Rightarrow V$.
\begin{enumerate}
\item
$(\sigma \bullet \rho) + 1 = (\sigma + 1) \bullet (\rho + 1)$
\item
$M[\sigma \bullet \rho] \equiv M [ \rho ] [ \sigma ]$
\end{enumerate}
\end{lemma}

\begin{code}
liftSub-comp : ∀ {U} {V} {W} (σ : Sub V W) (ρ : Sub U V) →
  liftSub (σ • ρ) ∼ liftSub σ • liftSub ρ
liftSub-comp σ ρ ⊥ = ref
liftSub-comp σ ρ (↑ x) = trans (rep-sub σ ↑ (ρ x)) (sym (sub-rep (liftSub σ) ↑ (ρ x)))

subcomp : ∀ {U} {V} {W} (σ : Sub V W) (ρ : Sub U V) M → M ⟦ σ • ρ ⟧ ≡ M ⟦ ρ ⟧ ⟦ σ ⟧
subcomp σ ρ (var x) = ref
subcomp σ ρ (app M N) = wd2 app (subcomp σ ρ M) (subcomp σ ρ N)
subcomp σ ρ (Λ A M) = wd (Λ A) (trans (subwd (liftSub-comp σ ρ) M)  (subcomp (liftSub σ) (liftSub ρ) M))
\end{code}

\begin{lemma}
The finite sets and substitutions form a category under this composition.
\end{lemma}

\begin{code}
assoc : ∀ {U V W X} {ρ : Sub W X} {σ : Sub V W} {τ : Sub U V} →
  ρ • (σ • τ) ∼ (ρ • σ) • τ
assoc {U} {V} {W} {X} {ρ} {σ} {τ} x = sym (subcomp ρ σ (τ x))

subunitl : ∀ {U} {V} {σ : Sub U V} → idSub V • σ ∼ σ
subunitl {U} {V} {σ} x = subid (σ x)

subunitr : ∀ {U} {V} {σ : Sub U V} → σ • idSub U ∼ σ
subunitr _ = ref

-- The second monad law

rep-is-sub : ∀ {U} {V} {ρ : El U → El V} M → M < ρ > ≡ M ⟦ var ∘ ρ ⟧
rep-is-sub (var x) = ref
rep-is-sub (app M N) = wd2 app (rep-is-sub M) (rep-is-sub N)
rep-is-sub {V = V} {ρ} (Λ A M) = let open Equational-Reasoning (Proof V) in 
  ∵ Λ A (M < lift ρ >)
  ≡ Λ A (M ⟦ var ∘ lift ρ ⟧)         [ wd (Λ A) (rep-is-sub M) ]
  ≡ Λ A (M ⟦ liftSub var ∘ lift ρ ⟧) [[ wd (Λ A) (subwd (λ x → liftSub-id (lift ρ x)) M) ]]
  ≡ Λ A (M ⟦ liftSub (var ∘ ρ) ⟧)    [[ wd (Λ A) (subwd (liftSub-comp₂ var ρ) M) ]]
--wd (Λ A) (trans (rep-is-sub M) (subwd {!!} M))

propof : ∀ {P} → El P → PContext P → Prp
propof ⊥ (_ , φ) = φ
propof (↑ p) (Γ , _) = propof p Γ

liftSub-var' : ∀ {U} {V} (ρ : El U → El V) → liftSub (var ∘ ρ) ∼ var ∘ lift ρ
liftSub-var' ρ ⊥ = ref
liftSub-var' ρ (↑ x) = ref

botsub : ∀ {V} → Proof V → Sub (Lift V) V
botsub δ ⊥ = δ
botsub _ (↑ x) = var x

sub-botsub : ∀ {U} {V} (σ : Sub U V) (M : Proof U) (x : El (Lift U)) →
  botsub M x ⟦ σ ⟧ ≡ liftSub σ x ⟦ botsub (M ⟦ σ ⟧) ⟧
sub-botsub σ M ⊥ = ref
sub-botsub σ M (↑ x) = let open Equational-Reasoning (Proof _) in 
  ∵ σ x
  ≡ σ x ⟦ idSub _ ⟧                    [[ subid (σ x) ]]
  ≡ σ x < ↑ > ⟦ botsub (M ⟦ σ ⟧) ⟧     [[ sub-rep (botsub (M ⟦ σ ⟧)) ↑ (σ x) ]]

rep-botsub : ∀ {U} {V} (ρ : El U → El V) (M : Proof U) (x : El (Lift U)) →
  botsub M x < ρ > ≡ botsub (M < ρ >) (lift ρ x)
rep-botsub ρ M x = trans (rep-is-sub (botsub M x)) 
  (trans (sub-botsub (var ∘ ρ) M x) (trans (subwd (λ x₁ → wd (λ y → botsub y x₁) (sym (rep-is-sub M))) (liftSub (λ z → var (ρ z)) x)) 
  (wd (λ x → x ⟦ botsub (M < ρ >)⟧) (liftSub-var' ρ x))))
--TODO Inline this?

subbot : ∀ {V} → Proof (Lift V) → Proof V → Proof V
subbot M N = M ⟦ botsub N ⟧
\end{code}

We write $M ≃ N$ iff the terms $M$ and $N$ are $\beta$-convertible, and similarly for proofs.

\begin{code}
data _↠_ : ∀ {V} → Proof V → Proof V → Set where
  β : ∀ {V} A (M : Proof (Lift V)) N → app (Λ A M) N ↠ subbot M N
  ref : ∀ {V} {M : Proof V} → M ↠ M
  ↠trans : ∀ {V} {M N P : Proof V} → M ↠ N → N ↠ P → M ↠ P
  app : ∀ {V} {δ δ' ε ε' : Proof V} → δ ↠ δ' → ε ↠ ε' → app δ ε ↠ app δ' ε'
  ξ : ∀ {V} {M N : Proof (Lift V)} {A} → M ↠ N → Λ A M ↠ Λ A N

repred : ∀ {U} {V} {ρ : El U → El V} {M N : Proof U} → M ↠ N → M < ρ > ↠ N < ρ >
repred {U} {V} {ρ} (β A M N) = subst (λ x → app (Λ A (M < lift ρ > )) (N < ρ >) ↠ x) (sym (trans (rep-sub (botsub N) ρ M) (sym (trans (sub-rep _ _ M) (subwd (λ x → sym (rep-botsub ρ N x)) M))))) (β A (M < lift _ >) (N < _ >))
repred ref = ref
repred (↠trans M↠N N↠P) = ↠trans (repred M↠N) (repred N↠P)
repred (app M↠N M'↠N') = app (repred M↠N) (repred M'↠N')
repred (ξ M↠N) = ξ (repred M↠N)

liftSub-red : ∀ {U} {V} {ρ σ : Sub U V} → (∀ x → ρ x ↠ σ x) → (∀ x → liftSub ρ x ↠ liftSub σ x)
liftSub-red ρ↠σ ⊥ = ref
liftSub-red ρ↠σ (↑ x) = repred (ρ↠σ x)

subred : ∀ {U} {V} {ρ σ : Sub U V} (M : Proof U) → (∀ x → ρ x ↠ σ x) → M ⟦ ρ ⟧ ↠ M ⟦ σ ⟧
subred (var x) ρ↠σ = ρ↠σ x
subred (app δ ε) ρ↠σ = app (subred δ ρ↠σ) (subred ε ρ↠σ)
subred (Λ φ δ) ρ↠σ = ξ (subred δ (liftSub-red ρ↠σ))

subsub : ∀ {U} {V} {W} (σ : Sub V W) (ρ : Sub U V) M → M ⟦ ρ ⟧ ⟦ σ ⟧ ≡ M ⟦ σ • ρ ⟧
subsub σ ρ (var x) = ref
subsub σ ρ (app M N) = wd2 app (subsub σ ρ M) (subsub σ ρ N)
subsub σ ρ (Λ A M) = wd (Λ A) (trans (subsub (liftSub σ) (liftSub ρ) M) 
  (subwd (λ x → sym (liftSub-comp σ ρ x)) M))

subredr : ∀ {U} {V} {σ : Sub U V} {M N : Proof U} → M ↠ N → M ⟦ σ ⟧ ↠ N ⟦ σ ⟧
subredr {U} {V} {σ} (β A M N) = subst (λ x → app (Λ A (M ⟦ liftSub σ ⟧)) (N ⟦ σ ⟧) ↠ x) (sym (trans (subsub σ (botsub N) M) 
  (sym (trans (subsub (botsub (N ⟦ σ ⟧)) (liftSub σ) M) (subwd (λ x → sym (sub-botsub σ N x)) M))))) (β A (M ⟦ liftSub σ ⟧) (N ⟦ σ ⟧))
subredr ref = ref
subredr (↠trans M↠N N↠P) = ↠trans (subredr M↠N) (subredr N↠P)
subredr (app M↠M' N↠N') = app (subredr M↠M') (subredr N↠N')
subredr (ξ δ↠δ') = ξ (subredr δ↠δ')

data _≃_ : ∀ {V} → Proof V → Proof V → Set₁ where
  β : ∀ {V} {A} {M : Proof (Lift V)} {N} → app (Λ A M) N ≃ subbot M N
  ref : ∀ {V} {M : Proof V} → M ≃ M
  ≃sym : ∀ {V} {M N : Proof V} → M ≃ N → N ≃ M
  ≃trans : ∀ {V} {M N P : Proof V} → M ≃ N → N ≃ P → M ≃ P
  app : ∀ {V} {M M' N N' : Proof V} → M ≃ M' → N ≃ N' → app M N ≃ app M' N'
  Λ : ∀ {V} {M N : Proof (Lift V)} {A} → M ≃ N → Λ A M ≃ Λ A N
\end{code}

The \emph{strongly normalizable} terms are defined inductively as follows.

\begin{code}
data SN {V} : Proof V → Set₁ where
  SNI : ∀ {M} → (∀ N → M ↠ N → SN N) → SN M
\end{code}

\begin{lemma}
\begin{enumerate}
\item
If $MN \in SN$ then $M \in SN$ and $N \in SN$.
\item
If $M[x:=N] \in SN$ then $M \in SN$.
\item
If $M \in SN$ and $M \rhd N$ then $N \in SN$.
\item
If $M[x:=N]\vec{P} \in SN$ and $N \in SN$ then $(\lambda x M) N \vec{P} \in SN$.
\end{enumerate}
\end{lemma}

\begin{code}
SNappl : ∀ {V} {M N : Proof V} → SN (app M N) → SN M
SNappl {V} {M} {N} (SNI MN-is-SN) = SNI (λ P M▷P → SNappl (MN-is-SN (app P N) (app M▷P ref)))

SNappr : ∀ {V} {M N : Proof V} → SN (app M N) → SN N
SNappr {V} {M} {N} (SNI MN-is-SN) = SNI (λ P N▷P → SNappr (MN-is-SN (app M P) (app ref N▷P)))

SNsub : ∀ {V} {M : Proof (Lift V)} {N} → SN (subbot M N) → SN M
SNsub {V} {M} {N} (SNI MN-is-SN) = SNI (λ P M▷P → SNsub (MN-is-SN (P ⟦ botsub N ⟧) (subredr M▷P)))
\end{code}

The rules of deduction of the system are as follows.

\[ \infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald} \]

\[ \infer{\Gamma \vdash \delta \epsilon : \psi}{\Gamma \vdash \delta : \phi \rightarrow \psi}{\Gamma \vdash \epsilon : \phi} \]

\[ \infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \rightarrow \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]


\begin{code}
data _⊢_∶∶_ : ∀ {P} → PContext P → Proof P → Prp → Set₁ where
  var : ∀ {P} {Γ : PContext P} {p} → Γ ⊢ var p ∶∶ propof p Γ
  app : ∀ {P} {Γ : PContext P} {δ} {ε} {φ} {ψ} → Γ ⊢ δ ∶∶ φ ⇒ ψ → Γ ⊢ ε ∶∶ φ → Γ ⊢ app δ ε ∶∶ ψ
  Λ : ∀ {P} {Γ : PContext P} {φ} {δ} {ψ} → Γ , φ ⊢ δ ∶∶ ψ → Γ ⊢ Λ φ δ ∶∶ φ ⇒ ψ
\end{code}



