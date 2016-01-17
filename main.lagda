\documentclass{article}

\title{Type Theories with Computation Rules for the Univalence Axiom}
\author{Robin Adams}

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}
\usepackage{fancyvrb}
\usepackage{proof}

\DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
\DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
\DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}
\DeclareUnicodeCharacter{9001}{\ensuremath{\langle}}
\DeclareUnicodeCharacter{9002}{\ensuremath{\rangle}}
\DeclareUnicodeCharacter{9655}{\ensuremath{\rhd}}
\DeclareUnicodeCharacter{10219}{\ensuremath{\rangle\rangle}}
\renewcommand{\textbeta}{\ensuremath{\beta}}
\renewcommand{\textGamma}{\ensuremath{\Gamma}}
\renewcommand{\textdelta}{\ensuremath{\delta}}
\renewcommand{\textepsilon}{\ensuremath{\epsilon}}
\renewcommand{\textLambda}{\ensuremath{\Lambda}}
\renewcommand{\textlambda}{\ensuremath{\lambda}}
\renewcommand{\textphi}{\ensuremath{\phi}}
\renewcommand{\textpsi}{\ensuremath{\psi}}
\renewcommand{\textsigma}{\ensuremath{\sigma}}
\renewcommand{\textrho}{\ensuremath{\rho}}
\renewcommand{\textOmega}{\ensuremath{\Omega}}

\DefineVerbatimEnvironment{code}{Verbatim}{}

\newtheorem{lemma}{Lemma}

\newcommand{\Set}{\mathbf{Set}}

\begin{document}

\maketitle

\begin{code}
module main where
\end{code}

\input{Prelims.lagda}
\begin{code}
open import Prelims
\end{code}

\section{Predicative Higher-Order Propositional Logic}

Fix sets of \emph{proof variables} and \emph{term variables}.

The syntax of the system is given by the following grammar.

\newcommand{\vald}{\ensuremath{\ \mathrm{valid}}}
%Changes from Marc and Thierry's system:
%Taken out the proof c of \bot
\[ \begin{array}{lrcl}
\text{Proof} & \delta & ::= & p \mid \delta \delta \mid \lambda p : \phi . \delta \\
\text{Term} & M, \phi & ::= & x \mid \bot \mid M M \mid \phi \rightarrow \phi \mid \lambda x : A . M \\
\text{Type} & A & ::= & \Omega \mid A \rightarrow A \\
\text{Context} & \Gamma & ::= & \langle \rangle \mid \Gamma, p : \phi \mid \Gamma , x : A \\
\text{Judgement} & \mathcal{J} & ::= & \Gamma \vald \mid \Gamma \vdash \delta : \phi \mid \Gamma \vdash M : A
\end{array} \]
where $p$ ranges over proof variables and $x$ ranges over term variables.  The variable $p$ is bound within $\delta$ in the proof $\lambda p : \phi . \delta$,
and the variable $x$ is bound within $M$ in the term $\lambda x : A . M$.  We identify proofs and terms up to $\alpha$-conversion.

\newcommand{\Term}[1]{\mathbf{Term} \left( #1 \right)}
In the implementation, we write $\Term{V}$ for the set of all terms with free variables a subset of $V$, where $V : \FinSet$.

\begin{code}
infix 80 _⇒_
data Type : Set where
  Ω : Type
  _⇒_ : Type → Type → Type

--Term V is the set of all terms M with FV(M) ⊆ V
data Term : FinSet → Set where
  var : ∀ {V} → El V → Term V
  ⊥ : ∀ {V} → Term V
  app : ∀ {V} → Term V → Term V → Term V
  Λ : ∀ {V} → Type → Term (Lift V) → Term V
  _⇒_ : ∀ {V} → Term V → Term V → Term V

--Proof V P is the set of all proofs with term variables among V and proof variables among P
data Proof (V : FinSet) : FinSet → Set₁ where
  var : ∀ {P} → El P → Proof V P
  app : ∀ {P} → Proof V P → Proof V P → Proof V P
  Λ : ∀ {P} → Term V → Proof V (Lift P) → Proof V P

--Context V P is the set of all contexts whose domain consists of the term variables in V and the proof variables in P
infix 80 _,_
infix 80 _,,_
data Context : FinSet → FinSet → Set₁ where
  〈〉 : Context ∅ ∅
  _,_ : ∀ {V} {P} → Context V P → Type → Context (Lift V) P
  _,,_ : ∀ {V} {P} → Context V P → Term V → Context V (Lift P)
\end{code}

Let $U, V : \FinSet$.  A \emph{replacement} from $U$ to $V$ is just a function $U \rightarrow V$.  Given a term $M : \Term{U}$
and a replacement $\rho : U \rightarrow V$, we write $M \{ \rho \} : \Term{V}$ for the result of replacing each variable $x$ in
$M$ with $\rho(x)$.

\begin{code}
rep : ∀ {U V : FinSet} → (El U → El V) → Term U → Term V
rep ρ (var x) = var (ρ x)
rep ρ ⊥ = ⊥
rep ρ (app M N) = app (rep ρ M) (rep ρ N)
rep ρ (Λ A M) = Λ A (rep (lift ρ) M)
rep ρ (φ ⇒ ψ) = rep ρ φ ⇒ rep ρ ψ
\end{code}

With this as the action on arrows, $\Term{}$ becomes a functor $\FinSet \rightarrow \Set$.

\begin{code}
repwd : ∀ {U V : FinSet} {ρ ρ' : El U → El V} → ρ ∼ ρ' → rep ρ ∼ rep ρ'
repwd ρ-is-ρ' (var x) = wd var (ρ-is-ρ' x)
repwd ρ-is-ρ' ⊥ = ref
repwd ρ-is-ρ' (app M N)= wd2 app (repwd ρ-is-ρ' M) (repwd ρ-is-ρ' N)
repwd ρ-is-ρ' (Λ A M) = wd (Λ A) (repwd (liftwd ρ-is-ρ') M)
repwd ρ-is-ρ' (φ ⇒ ψ) = wd2 _⇒_ (repwd ρ-is-ρ' φ) (repwd ρ-is-ρ' ψ)

repid : ∀ {V : FinSet} → rep (id (El V)) ∼ id (Term V)
repid (var x) = ref
repid ⊥ = ref
repid (app M N) = wd2 app (repid M) (repid N)
repid (Λ A M) = wd (Λ A) (trans (repwd liftid M) (repid M))
repid (φ ⇒ ψ) = wd2 _⇒_ (repid φ) (repid ψ)

repcomp : ∀ {U V W : FinSet} (σ : El V → El W) (ρ : El U → El V) → rep (σ ∘ ρ) ∼ rep σ ∘ rep ρ
repcomp ρ σ (var x) = ref
repcomp ρ σ ⊥ = ref
repcomp ρ σ (app M N) = wd2 app (repcomp ρ σ M) (repcomp ρ σ N)
repcomp ρ σ (Λ A M) = wd (Λ A) (trans (repwd liftcomp M) (repcomp (lift ρ) (lift σ) M))
repcomp ρ σ (φ ⇒ ψ) = wd2 _⇒_ (repcomp ρ σ φ) (repcomp ρ σ ψ)

Sub : FinSet → FinSet → Set
Sub U V = El U → Term V

idSub : ∀ V → Sub V V
idSub V = var

liftSub : ∀ {U} {V} → Sub U V → Sub (Lift U) (Lift V)
liftSub _ ⊥ = var ⊥
liftSub σ (↑ x) = rep ↑ (σ x)

liftSub-wd : ∀ {U V} {σ σ' : Sub U V} → σ ∼ σ' → liftSub σ ∼ liftSub σ'
liftSub-wd σ-is-σ' ⊥ = ref
liftSub-wd σ-is-σ' (↑ x) = wd (rep ↑) (σ-is-σ' x)

liftSub-id : ∀ {V : FinSet} → liftSub (idSub V) ∼ idSub (Lift V)
liftSub-id ⊥ = ref
liftSub-id (↑ x) = ref

liftSub-rep : ∀ {U V W : FinSet} (σ : Sub U V) (ρ : El V → El W) (x : El (Lift U)) → liftSub (λ x → rep ρ (σ x)) x ≡ rep (lift ρ) (liftSub σ x)
liftSub-rep σ ρ ⊥ = ref
liftSub-rep σ ρ (↑ x) = trans (sym (repcomp ↑ ρ (σ x))) (repcomp (lift ρ) ↑ (σ x))

liftSub-lift : ∀ {U V W : FinSet} (σ : Sub V W) (ρ : El U → El V) (x : El (Lift U)) →
  liftSub σ (lift ρ x) ≡ liftSub (λ x → σ (ρ x)) x
liftSub-lift σ ρ ⊥ = ref
liftSub-lift σ ρ (↑ x) = ref

var-lift : ∀ {U V : FinSet} {ρ : El U → El V} → var ∘ lift ρ ∼ liftSub (var ∘ ρ)
var-lift ⊥ = ref
var-lift (↑ x) = ref

--Term is a monad with unit var and the following multiplication
sub : ∀ {U V : FinSet} → Sub U V → Term U → Term V
sub σ (var x) = σ x
sub σ ⊥ = ⊥
sub σ (app M N) = app (sub σ M) (sub σ N)
sub σ (Λ A M) = Λ A (sub (liftSub σ) M)
sub σ (φ ⇒ ψ) = sub σ φ ⇒ sub σ ψ

subwd : ∀ {U V : FinSet} {σ σ' : Sub U V} → σ ∼ σ' → sub σ ∼ sub σ'
subwd σ-is-σ' (var x) = σ-is-σ' x
subwd σ-is-σ' ⊥ = ref
subwd σ-is-σ' (app M N) = wd2 app (subwd σ-is-σ' M) (subwd σ-is-σ' N)
subwd σ-is-σ' (Λ A M) = wd (Λ A) (subwd (liftSub-wd σ-is-σ') M)
subwd σ-is-σ' (φ ⇒ ψ) = wd2 _⇒_ (subwd σ-is-σ' φ) (subwd σ-is-σ' ψ)

--The first monad law

subvar : ∀ {V : FinSet} (M : Term V) → sub var M ≡ M
subvar (var x) = ref
subvar ⊥ = ref
subvar (app M N) = wd2 app (subvar M) (subvar N)
subvar (Λ A M) = wd (Λ A) (trans (subwd liftSub-id M) (subvar M))
subvar (φ ⇒ ψ) = wd2 _⇒_ (subvar φ) (subvar ψ)

infix 75 _•_
_•_ : ∀ {U V W : FinSet} → Sub V W → Sub U V → Sub U W
(σ • ρ) x = sub σ (ρ x)

rep-sub : ∀ {U} {V} {W} (σ : Sub U V) (ρ : El V → El W) → rep ρ ∘ sub σ ∼ sub (rep ρ ∘ σ)
rep-sub σ ρ (var x) = ref
rep-sub σ ρ ⊥ = ref
rep-sub σ ρ (app M N) = wd2 app (rep-sub σ ρ M) (rep-sub σ ρ N)
rep-sub σ ρ (Λ A M) = wd (Λ A) (trans (rep-sub (liftSub σ) (lift ρ) M) (subwd (λ x → sym (liftSub-rep σ ρ x)) M))
rep-sub σ ρ (φ ⇒ ψ) = wd2 _⇒_ (rep-sub σ ρ φ) (rep-sub σ ρ ψ) 

sub-rep : ∀ {U} {V} {W} (σ : Sub V W) (ρ : El U → El V) →
  sub σ ∘ rep ρ ∼ sub (σ ∘ ρ)
sub-rep σ ρ (var x) = ref
sub-rep σ ρ ⊥ = ref
sub-rep σ ρ (app M N) = wd2 app (sub-rep σ ρ M) (sub-rep σ ρ N)
sub-rep σ ρ (Λ A M) = wd (Λ A) (trans (sub-rep (liftSub σ) (lift ρ) M) (subwd (liftSub-lift σ ρ) M))
sub-rep σ ρ (φ ⇒ ψ) = wd2 _⇒_ (sub-rep σ ρ φ) (sub-rep σ ρ ψ)

liftSub-comp : ∀ {U} {V} {W} (σ : Sub V W) (ρ : Sub U V) →
  liftSub (σ • ρ) ∼ liftSub σ • liftSub ρ
liftSub-comp σ ρ ⊥ = ref
liftSub-comp σ ρ (↑ x) = trans (rep-sub σ ↑ (ρ x)) (sym (sub-rep (liftSub σ) ↑ (ρ x)))

-- The second monad law

subcomp : ∀ {U} {V} {W} (σ : Sub V W) (ρ : Sub U V) →
  sub (σ • ρ) ∼ sub σ ∘ sub ρ
subcomp σ ρ (var x) = ref
subcomp σ ρ ⊥ = ref
subcomp σ ρ (app M N) = wd2 app (subcomp σ ρ M) (subcomp σ ρ N)
subcomp σ ρ (Λ A M) = wd (Λ A) (trans (subwd (liftSub-comp σ ρ) M)  (subcomp (liftSub σ) (liftSub ρ) M))
subcomp σ ρ (φ ⇒ ψ) = wd2 _⇒_ (subcomp σ ρ φ) (subcomp σ ρ ψ)

rep-is-sub : ∀ {U} {V} {ρ : El U → El V} → rep ρ ∼ sub (var ∘ ρ)
rep-is-sub (var x) = ref
rep-is-sub ⊥ = ref
rep-is-sub (app M N) = wd2 app (rep-is-sub M) (rep-is-sub N)
rep-is-sub (Λ A M) = wd (Λ A) (trans (rep-is-sub M) (subwd var-lift M))
rep-is-sub (φ ⇒ ψ) = wd2 _⇒_ (rep-is-sub φ) (rep-is-sub ψ)

typeof : ∀ {V} {P} → El V → Context V P → Type
typeof () 〈〉
typeof ⊥ (_ , A) = A
typeof (↑ x) (Γ , _) = typeof x Γ
typeof x (Γ ,, _) = typeof x Γ

propof : ∀ {V} {P} → El P → Context V P → Term V
propof () 〈〉
propof p (Γ , _) = rep ↑ (propof p Γ)
propof p (_ ,, φ) = φ

liftSub-var' : ∀ {U} {V} (ρ : El U → El V) → liftSub (var ∘ ρ) ∼ var ∘ lift ρ
liftSub-var' ρ ⊥ = ref
liftSub-var' ρ (↑ x) = ref

botsub : ∀ {V} → Term V → Sub (Lift V) V
botsub M ⊥ = M
botsub _ (↑ x) = var x

sub-botsub : ∀ {U} {V} (σ : Sub U V) (M : Term U) (x : El (Lift U)) →
  sub σ (botsub M x) ≡ sub (botsub (sub σ M)) (liftSub σ x)
sub-botsub σ M ⊥ = ref
sub-botsub σ M (↑ x) = let open Equational-Reasoning (Term _) in 
  ∵ σ x
  ≡ sub var (σ x)                        [[ subvar (σ x) ]]
  ≡ sub (botsub (sub σ M)) (rep ↑ (σ x)) [[ sub-rep (botsub (sub σ M)) ↑ (σ x) ]]

rep-botsub : ∀ {U} {V} (ρ : El U → El V) (M : Term U) (x : El (Lift U)) →
  rep ρ (botsub M x) ≡ botsub (rep ρ M) (lift ρ x)
rep-botsub ρ M x = trans (rep-is-sub (botsub M x)) 
  (trans (sub-botsub (var ∘ ρ) M x) (trans (subwd (λ x₁ → wd (λ y → botsub y x₁) (sym (rep-is-sub M))) (liftSub (λ z → var (ρ z)) x)) (wd (sub (botsub (rep ρ M))) (liftSub-var' ρ x))))
--TODO Inline this?

subbot : ∀ {V} → Term (Lift V) → Term V → Term V
subbot M N = sub (botsub N) M
\end{code}

We write $M ≃ N$ iff the terms $M$ and $N$ are $\beta$-convertible, and similarly for proofs.

\begin{code}
data _↠_ : ∀ {V} → Term V → Term V → Set where
  β : ∀ {V} A (M : Term (Lift V)) N → app (Λ A M) N ↠ subbot M N
  ref : ∀ {V} {M : Term V} → M ↠ M
  ↠trans : ∀ {V} {M N P : Term V} → M ↠ N → N ↠ P → M ↠ P
  app : ∀ {V} {M M' N N' : Term V} → M ↠ M' → N ↠ N' → app M N ↠ app M' N'
  Λ : ∀ {V} {M N : Term (Lift V)} {A} → M ↠ N → Λ A M ↠ Λ A N
  imp : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ↠ φ' → ψ ↠ ψ' → φ ⇒ ψ ↠ φ' ⇒ ψ'

repred : ∀ {U} {V} {ρ : El U → El V} {M N : Term U} → M ↠ N → rep ρ M ↠ rep ρ N
repred {U} {V} {ρ} (β A M N) = subst (λ x → app (Λ A (rep (lift ρ) M)) (rep ρ N) ↠ x) (sym (trans (rep-sub (botsub N) ρ M) (sym (trans (sub-rep _ _ M) (subwd (λ x → sym (rep-botsub ρ N x)) M))))) (β A (rep (lift _) M) (rep _ N))
repred ref = ref
repred (↠trans M↠N N↠P) = ↠trans (repred M↠N) (repred N↠P)
repred (app M↠N M'↠N') = app (repred M↠N) (repred M'↠N')
repred (Λ M↠N) = Λ (repred M↠N)
repred (imp φ↠φ' ψ↠ψ') = imp (repred φ↠φ') (repred ψ↠ψ')

liftSub-red : ∀ {U} {V} {ρ σ : Sub U V} → (∀ x → ρ x ↠ σ x) → (∀ x → liftSub ρ x ↠ liftSub σ x)
liftSub-red ρ↠σ ⊥ = ref
liftSub-red ρ↠σ (↑ x) = repred (ρ↠σ x)

subred : ∀ {U} {V} {ρ σ : Sub U V} (M : Term U) → (∀ x → ρ x ↠ σ x) → sub ρ M ↠ sub σ M
subred (var x) ρ↠σ = ρ↠σ x
subred ⊥ ρ↠σ = ref
subred (app M N) ρ↠σ = app (subred M ρ↠σ) (subred N ρ↠σ)
subred (Λ A M) ρ↠σ = Λ (subred M (liftSub-red ρ↠σ))
subred (φ ⇒ ψ) ρ↠σ = imp (subred φ ρ↠σ) (subred ψ ρ↠σ)

subsub : ∀ {U} {V} {W} (σ : Sub V W) (ρ : Sub U V) → sub σ ∘ sub ρ ∼ sub (σ • ρ)
subsub σ ρ (var x) = ref
subsub σ ρ ⊥ = ref
subsub σ ρ (app M N) = wd2 app (subsub σ ρ M) (subsub σ ρ N)
subsub σ ρ (Λ A M) = wd (Λ A) (trans (subsub (liftSub σ) (liftSub ρ) M) 
  (subwd (λ x → sym (liftSub-comp σ ρ x)) M))
subsub σ ρ (φ ⇒ ψ) = wd2 _⇒_ (subsub σ ρ φ) (subsub σ ρ ψ)

subredr : ∀ {U} {V} {σ : Sub U V} {M N : Term U} → M ↠ N → sub σ M ↠ sub σ N
subredr {U} {V} {σ} (β A M N) = subst (λ x → app (Λ A (sub (liftSub σ) M)) (sub σ N) ↠ x) (sym (trans (subsub σ (botsub N) M) 
  (sym (trans (subsub (botsub (sub σ N)) (liftSub σ) M) (subwd (λ x → sym (sub-botsub σ N x)) M))))) (β A (sub (liftSub σ) M) (sub σ N))
subredr ref = ref
subredr (↠trans M↠N N↠P) = ↠trans (subredr M↠N) (subredr N↠P)
subredr (app M↠M' N↠N') = app (subredr M↠M') (subredr N↠N')
subredr (Λ M↠N) = Λ (subredr M↠N)
subredr (imp φ↠φ' ψ↠ψ') = imp (subredr φ↠φ') (subredr ψ↠ψ')

data _≃_ : ∀ {V} → Term V → Term V → Set₁ where
  β : ∀ {V} {A} {M : Term (Lift V)} {N} → app (Λ A M) N ≃ subbot M N
  ref : ∀ {V} {M : Term V} → M ≃ M
  ≃sym : ∀ {V} {M N : Term V} → M ≃ N → N ≃ M
  ≃trans : ∀ {V} {M N P : Term V} → M ≃ N → N ≃ P → M ≃ P
  app : ∀ {V} {M M' N N' : Term V} → M ≃ M' → N ≃ N' → app M N ≃ app M' N'
  Λ : ∀ {V} {M N : Term (Lift V)} {A} → M ≃ N → Λ A M ≃ Λ A N
  imp : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ≃ φ' → ψ ≃ ψ' → φ ⇒ ψ ≃ φ' ⇒ ψ'
\end{code}

The \emph{strongly normalizable} terms are defined inductively as follows.

\begin{code}
data SN {V} : Term V → Set₁ where
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
SNappl : ∀ {V} {M N : Term V} → SN (app M N) → SN M
SNappl {V} {M} {N} (SNI MN-is-SN) = SNI (λ P M▷P → SNappl (MN-is-SN (app P N) (app M▷P ref)))

SNappr : ∀ {V} {M N : Term V} → SN (app M N) → SN N
SNappr {V} {M} {N} (SNI MN-is-SN) = SNI (λ P N▷P → SNappr (MN-is-SN (app M P) (app ref N▷P)))

SNsub : ∀ {V} {M : Term (Lift V)} {N} → SN (subbot M N) → SN M
SNsub {V} {M} {N} (SNI MN-is-SN) = SNI (λ P M▷P → SNsub (MN-is-SN (sub (botsub N) P) (subredr M▷P)))
\end{code}

The rules of deduction of the system are as follows.

\[ \infer{\langle \rangle \vald}{} \qquad
\infer{\Gamma, x : A \vald}{\Gamma \vald} \qquad 
\infer{\Gamma, p : \phi \vald}{\Gamma \vdash \phi : \Omega} \]

\[ \infer[(x : A \in \Gamma)]{\Gamma \vdash x : A}{\Gamma \vald} \qquad
\infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald} \]

\[ \infer{\Gamma \vdash \bot : \Omega}{\Gamma \vald} \qquad
\infer{\Gamma \vdash \phi \rightarrow \psi : \Omega}{\Gamma \vdash \phi : \Omega \quad \Gamma \vdash \psi : \Omega} \]

\[ \infer{\Gamma \vdash M N : B} {\Gamma \vdash M : A \rightarrow B \quad \Gamma \vdash N : A} \qquad
\infer{\Gamma \vdash \delta \epsilon : \psi} {\Gamma \vdash \delta : \phi \rightarrow \psi \quad \Gamma \vdash \epsilon : \phi} \]

\[ \infer{\Gamma \vdash \lambda x:A.M : A \rightarrow B}{\Gamma, x : A \vdash M : B} \qquad
\infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \rightarrow \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]

\[ \infer[(\phi \simeq \phi)]{\Gamma \vdash \delta : \psi}{\Gamma \vdash \delta : \phi \quad \Gamma \vdash \psi : \Omega} \]

\begin{code}
mutual
  data valid : ∀ {V} {P} → Context V P → Set₁ where
    〈〉 : valid 〈〉
    ctxV : ∀ {V} {P} {Γ : Context V P} {A} → valid Γ → valid (Γ , A)
    ctxP : ∀ {V} {P} {Γ : Context V P} {φ} → Γ ⊢ φ ∶ Ω → valid (Γ ,, φ)

  data _⊢_∶_ : ∀ {V} {P} → Context V P → Term V → Type → Set₁ where
    var : ∀ {V} {P} {Γ : Context V P} {x} → valid Γ → Γ ⊢ var x ∶ typeof x Γ
    ⊥ : ∀ {V} {P} {Γ : Context V P} → valid Γ → Γ ⊢ ⊥ ∶ Ω
    imp : ∀ {V} {P} {Γ : Context V P} {φ} {ψ} → Γ ⊢ φ ∶ Ω → Γ ⊢ ψ ∶ Ω → Γ ⊢ φ ⇒ ψ ∶ Ω
    app : ∀ {V} {P} {Γ : Context V P} {M} {N} {A} {B} → Γ ⊢ M ∶ A ⇒ B → Γ ⊢ N ∶ A → Γ ⊢ app M N ∶ B
    Λ : ∀ {V} {P} {Γ : Context V P} {A} {M} {B} → Γ , A ⊢ M ∶ B → Γ ⊢ Λ A M ∶ A ⇒ B

data _⊢_∶∶_ : ∀ {V} {P} → Context V P → Proof V P → Term V → Set₁ where
  var : ∀ {V} {P} {Γ : Context V P} {p} → valid Γ → Γ ⊢ var p ∶∶ propof p Γ
  app : ∀ {V} {P} {Γ : Context V P} {δ} {ε} {φ} {ψ} → Γ ⊢ δ ∶∶ φ ⇒ ψ → Γ ⊢ ε ∶∶ φ → Γ ⊢ app δ ε ∶∶ ψ
  Λ : ∀ {V} {P} {Γ : Context V P} {φ} {δ} {ψ} → Γ ,, φ ⊢ δ ∶∶ ψ → Γ ⊢ Λ φ δ ∶∶ φ ⇒ ψ
  conv : ∀ {V} {P} {Γ : Context V P} {δ} {φ} {ψ} → Γ ⊢ δ ∶∶ φ → Γ ⊢ ψ ∶ Ω → φ ≃ ψ → Γ ⊢ δ ∶∶ ψ
\end{code}

\end{document}
