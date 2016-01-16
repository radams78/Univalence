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

\begin{document}

\maketitle

\begin{code}
module main where

postulate Level : Set
postulate zero : Level
postulate suc : Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO zero #-}
{-# BUILTIN LEVELSUC suc #-}
\end{code}

\section{Preliminaries}

\subsection{Functions}

\begin{code}
infix 75 _∘_
_∘_ : ∀ {i} {j} {k} {A : Set i} {B : Set j} {C : Set k} → 
  (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)
\end{code}

\subsection{Equality}

\begin{code}
data _≡_ {i} {A : Set i} (a : A) : A → Set where
  ref : a ≡ a

subst : ∀ {i} {A : Set i} (P : A → Set₁) {a} {b} → a ≡ b → P a → P b
subst P ref Pa = Pa

sym : ∀ {i} {A : Set i} {a b : A} → a ≡ b → b ≡ a
sym ref = ref

trans : ∀ {i} {A : Set i} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans ref ref = ref

wd : ∀ {i} {j} {A : Set i} {B : Set j} (f : A → B) {a a' : A} → a ≡ a' → f a ≡ f a'
wd _ ref = ref

wd2 : ∀ {i} {A B C : Set i} (f : A → B → C) {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
wd2 _ ref ref = ref

infix 50 _∼_
_∼_ : ∀ {i} {j} {A : Set i} {B : Set j} → (A → B) → (A → B) → Set _
f ∼ g = ∀ x → f x ≡ g x
\end{code}

\section{Datatypes}

\begin{code}
data ∅ : Set where

data Lift (A : Set) : Set where
  ⊥ : Lift A
  ↑ : A → Lift A

lift : ∀ {A} {B} → (A → B) → Lift A → Lift B
lift f ⊥ = ⊥
lift f (↑ x) = ↑ (f x)

liftwd : ∀ {A} {B} {f g : A → B} → f ∼ g → lift f ∼ lift g
liftwd f-is-g ⊥ = ref
liftwd f-is-g (↑ x) = wd ↑ (f-is-g x)

lift-comp : ∀ {A} {B} {C} {f : A → B} {g : B → C} → lift (g ∘ f) ∼ lift g ∘ lift f
lift-comp ⊥ = ref
lift-comp (↑ x) = ref
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

\begin{code}
infix 80 _⇒_
data Type : Set where
  Ω : Type
  _⇒_ : Type → Type → Type

--Term V is the set of all terms M with FV(M) ⊆ V
data Term : Set → Set₁ where
  var : ∀ {V} → V → Term V
  ⊥ : ∀ {V} → Term V
  app : ∀ {V} → Term V → Term V → Term V
  Λ : ∀ {V} → Type → Term (Lift V) → Term V
  _⇒_ : ∀ {V} → Term V → Term V → Term V

rep : ∀ {U} {V} → (U → V) → Term U → Term V
rep ρ (var x) = var (ρ x)
rep ρ ⊥ = ⊥
rep ρ (app M N) = app (rep ρ M) (rep ρ N)
rep ρ (Λ A M) = Λ A (rep (lift ρ) M)
rep ρ (φ ⇒ ψ) = rep ρ φ ⇒ rep ρ ψ

repwd : ∀ {U} {V} {ρ ρ' : U → V} → ρ ∼ ρ' → rep ρ ∼ rep ρ'
repwd ρ-is-ρ' (var x) = wd var (ρ-is-ρ' x)
repwd ρ-is-ρ' ⊥ = ref
repwd ρ-is-ρ' (app M N)= wd2 app (repwd ρ-is-ρ' M) (repwd ρ-is-ρ' N)
repwd ρ-is-ρ' (Λ A M) = wd (Λ A) (repwd (liftwd ρ-is-ρ') M)
repwd ρ-is-ρ' (φ ⇒ ψ) = wd2 _⇒_ (repwd ρ-is-ρ' φ) (repwd ρ-is-ρ' ψ)

rep-comp : ∀ {U V W : Set zero} (σ : V → W) (ρ : U → V) → rep (σ ∘ ρ) ∼ rep σ ∘ rep ρ
rep-comp ρ σ (var x) = ref
rep-comp ρ σ ⊥ = ref
rep-comp ρ σ (app M N) = wd2 app (rep-comp ρ σ M) (rep-comp ρ σ N)
rep-comp ρ σ (Λ A M) = wd (Λ A) (trans (repwd lift-comp M) (rep-comp (lift ρ) (lift σ) M))
rep-comp ρ σ (φ ⇒ ψ) = wd2 _⇒_ (rep-comp ρ σ φ) (rep-comp ρ σ ψ)
--TODO Refactor: Equational Reasoning

liftTerm : ∀ {V} → Term V → Term (Lift V)
liftTerm = rep ↑

--Proof V P is the set of all proofs with term variables among V and proof variables among P
data Proof (V : Set) : Set → Set₁ where
  var : ∀ {P} → P → Proof V P
  app : ∀ {P} → Proof V P → Proof V P → Proof V P
  Λ : ∀ {P} → Term V → Proof V (Lift P) → Proof V P

--Context V P is the set of all contexts whose domain consists of the term variables in V and the proof variables in P
infix 80 _,_
infix 80 _,,_
data Context : Set → Set → Set₁ where
  〈〉 : Context ∅ ∅

  _,_ : ∀ {V} {P} → Context V P → Type → Context (Lift V) P
  _,,_ : ∀ {V} {P} → Context V P → Term V → Context V (Lift P)

typeof : ∀ {V} {P} → V → Context V P → Type
typeof () 〈〉
typeof ⊥ (_ , A) = A
typeof (↑ x) (Γ , _) = typeof x Γ
typeof x (Γ ,, _) = typeof x Γ

propof : ∀ {V} {P} → P → Context V P → Term V
propof () 〈〉
propof p (Γ , _) = liftTerm (propof p Γ)
propof p (_ ,, φ) = φ

liftSub : ∀ {U} {V} → (U → Term V) → Lift U → Term (Lift V)
liftSub _ ⊥ = var ⊥
liftSub σ (↑ x) = liftTerm (σ x)

liftSub-wd : ∀ {U} {V} {σ σ' : U → Term V} → σ ∼ σ' → liftSub σ ∼ liftSub σ'
liftSub-wd σ-is-σ' ⊥ = ref
liftSub-wd σ-is-σ' (↑ x) = wd (rep ↑) (σ-is-σ' x)

liftSub-id : ∀ {V} (x : Lift V) → liftSub var x ≡ var x
liftSub-id ⊥ = ref
liftSub-id (↑ x) = ref

liftSub-lift : ∀ {U} {V} {W} (σ : V → Term W) (ρ : U → V) (x : Lift U) →
  liftSub σ (lift ρ x) ≡ liftSub (λ x → σ (ρ x)) x
liftSub-lift σ ρ ⊥ = ref
liftSub-lift σ ρ (↑ x) = ref

liftSub-var : ∀ {U} {V} (ρ : U → V) → liftSub (var ∘ ρ) ∼ var ∘ lift ρ
liftSub-var ρ ⊥ = ref
liftSub-var ρ (↑ x) = ref

liftSub-rep : ∀ {U} {V} {W} (σ : U → Term V) (ρ : V → W) (x : Lift U) → liftSub (λ x → rep ρ (σ x)) x ≡ rep (lift ρ) (liftSub σ x)
liftSub-rep σ ρ ⊥ = ref
liftSub-rep σ ρ (↑ x) = trans (sym (rep-comp ↑ ρ (σ x))) (rep-comp (lift ρ) ↑ (σ x))

var-lift : ∀ {U} {V} {ρ : U → V} → var ∘ lift ρ ∼ liftSub (var ∘ ρ)
var-lift ⊥ = ref
var-lift (↑ x) = ref

sub : ∀ {U} {V} → (U → Term V) → Term U → Term V
sub σ (var x) = σ x
sub σ ⊥ = ⊥
sub σ (app M N) = app (sub σ M) (sub σ N)
sub σ (Λ A M) = Λ A (sub (liftSub σ) M)
sub σ (φ ⇒ ψ) = sub σ φ ⇒ sub σ ψ

infix 75 _•_
_•_ : ∀ {i} {U : Set i} {V} {W} → (V → Term W) → (U → Term V) → U → Term W
(σ • ρ) x = sub σ (ρ x)

subwd : ∀ {U} {V} {σ σ' : U → Term V} → σ ∼ σ' → sub σ ∼ sub σ'
subwd σ-is-σ' (var x) = σ-is-σ' x
subwd σ-is-σ' ⊥ = ref
subwd σ-is-σ' (app M N) = wd2 app (subwd σ-is-σ' M) (subwd σ-is-σ' N)
subwd σ-is-σ' (Λ A M) = wd (Λ A) (subwd (liftSub-wd σ-is-σ') M)
subwd σ-is-σ' (φ ⇒ ψ) = wd2 _⇒_ (subwd σ-is-σ' φ) (subwd σ-is-σ' ψ)

subid : ∀ {V} (M : Term V) → sub var M ≡ M
subid (var x) = ref
subid ⊥ = ref
subid (app M N) = wd2 app (subid M) (subid N)
subid (Λ A M) = wd (Λ A) (trans (subwd liftSub-id M) (subid M))
subid (φ ⇒ ψ) = wd2 _⇒_ (subid φ) (subid ψ)

rep-sub : ∀ {U} {V} {W} (σ : U → Term V) (ρ : V → W) → rep ρ ∘ sub σ ∼ sub (rep ρ ∘ σ)
rep-sub σ ρ (var x) = ref
rep-sub σ ρ ⊥ = ref
rep-sub σ ρ (app M N) = wd2 app (rep-sub σ ρ M) (rep-sub σ ρ N)
rep-sub σ ρ (Λ A M) = wd (Λ A) (trans (rep-sub (liftSub σ) (lift ρ) M) (subwd (λ x → sym (liftSub-rep σ ρ x)) M))
rep-sub σ ρ (φ ⇒ ψ) = wd2 _⇒_ (rep-sub σ ρ φ) (rep-sub σ ρ ψ) 

sub-rep : ∀ {U} {V} {W} (σ : V → Term W) (ρ : U → V) (M : Term U) →
  sub σ (rep ρ M) ≡ sub (λ x → σ (ρ x)) M
sub-rep σ ρ (var x) = ref
sub-rep σ ρ ⊥ = ref
sub-rep σ ρ (app M N) = wd2 app (sub-rep σ ρ M) (sub-rep σ ρ N)
sub-rep σ ρ (Λ A M) = wd (Λ A) (trans (sub-rep (liftSub σ) (lift ρ) M) (subwd (liftSub-lift σ ρ) M))
sub-rep σ ρ (φ ⇒ ψ) = wd2 _⇒_ (sub-rep σ ρ φ) (sub-rep σ ρ ψ)

liftSub-comp : ∀ {U} {V} {W} (σ : V → Term W) (ρ : U → Term V) →
  liftSub (σ • ρ) ∼ liftSub σ • liftSub ρ
liftSub-comp σ ρ ⊥ = ref
liftSub-comp σ ρ (↑ x) = trans (rep-sub σ ↑ (ρ x)) (sym (sub-rep (liftSub σ) ↑ (ρ x)))

subcomp : ∀ {U} {V} {W} (σ : V → Term W) (ρ : U → Term V) →
  sub (σ • ρ) ∼ sub σ ∘ sub ρ
subcomp σ ρ (var x) = ref
subcomp σ ρ ⊥ = ref
subcomp σ ρ (app M N) = wd2 app (subcomp σ ρ M) (subcomp σ ρ N)
subcomp σ ρ (Λ A M) = wd (Λ A) (trans (subwd (liftSub-comp σ ρ) M)  (subcomp (liftSub σ) (liftSub ρ) M))
subcomp σ ρ (φ ⇒ ψ) = wd2 _⇒_ (subcomp σ ρ φ) (subcomp σ ρ ψ)

rep-is-sub : ∀ {U} {V} {ρ : U → V} → rep ρ ∼ sub (var ∘ ρ)
rep-is-sub (var x) = ref
rep-is-sub ⊥ = ref
rep-is-sub (app M N) = wd2 app (rep-is-sub M) (rep-is-sub N)
rep-is-sub (Λ A M) = wd (Λ A) (trans (rep-is-sub M) (subwd var-lift M))
rep-is-sub (φ ⇒ ψ) = wd2 _⇒_ (rep-is-sub φ) (rep-is-sub ψ)

botsub : ∀ {V} → Term V → Lift V → Term V
botsub M ⊥ = M
botsub _ (↑ x) = var x

botsub-liftTerm : ∀ {V} (M N : Term V) → sub (botsub M) (liftTerm N) ≡ N
botsub-liftTerm M (var x) = ref
botsub-liftTerm M ⊥ = ref
botsub-liftTerm M (app N P) = wd2 app (botsub-liftTerm M N) (botsub-liftTerm M P)
botsub-liftTerm M (Λ A N) = wd (Λ A) (trans (sub-rep _ _ N) (trans (subwd (λ x → trans (liftSub-lift (botsub M) ↑ x) (liftSub-id x)) N) (subid N)))
botsub-liftTerm M (φ ⇒ ψ) = wd2 _⇒_ (botsub-liftTerm M φ) (botsub-liftTerm M ψ)

sub-botsub : ∀ {U} {V} (σ : U → Term V) (M : Term U) (x : Lift U) →
  sub σ (botsub M x) ≡ sub (botsub (sub σ M)) (liftSub σ x)
sub-botsub σ M ⊥ = ref
sub-botsub σ M (↑ x) = sym (botsub-liftTerm (sub σ M) (σ x))

rep-botsub : ∀ {U} {V} (ρ : U → V) (M : Term U) (x : Lift U) →
  rep ρ (botsub M x) ≡ botsub (rep ρ M) (lift ρ x)
rep-botsub ρ M x = trans (rep-is-sub (botsub M x)) 
  (trans (sub-botsub (var ∘ ρ) M x) (trans (subwd (λ x₁ → wd (λ y → botsub y x₁) (sym (rep-is-sub M))) (liftSub (λ z → var (ρ z)) x)) (wd (sub (botsub (rep ρ M))) (liftSub-var ρ x))))
--TODO Inline this?

subbot : ∀ {V} → Term (Lift V) → Term V → Term V
subbot M N = sub (botsub N) M
\end{code}

We write $M ≃ N$ iff the terms $M$ and $N$ are $\beta$-convertible, and similarly for proofs.

\begin{code}
data _↠_ : ∀ {V} → Term V → Term V → Set₁ where
  β : ∀ {V} A (M : Term (Lift V)) N → app (Λ A M) N ↠ subbot M N
  ref : ∀ {V} {M : Term V} → M ↠ M
  ↠trans : ∀ {V} {M N P : Term V} → M ↠ N → N ↠ P → M ↠ P
  app : ∀ {V} {M M' N N' : Term V} → M ↠ M' → N ↠ N' → app M N ↠ app M' N'
  Λ : ∀ {V} {M N : Term (Lift V)} {A} → M ↠ N → Λ A M ↠ Λ A N
  imp : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ↠ φ' → ψ ↠ ψ' → φ ⇒ ψ ↠ φ' ⇒ ψ'

repred : ∀ {U} {V} {ρ : U → V} {M N : Term U} → M ↠ N → rep ρ M ↠ rep ρ N
repred {U} {V} {ρ} (β A M N) = subst (λ x → app (Λ A (rep (lift ρ) M)) (rep ρ N) ↠ x) (sym (trans (rep-sub (botsub N) ρ M) (sym (trans (sub-rep _ _ M) (subwd (λ x → sym (rep-botsub ρ N x)) M))))) (β A (rep (lift _) M) (rep _ N))
repred ref = ref
repred (↠trans M↠N N↠P) = ↠trans (repred M↠N) (repred N↠P)
repred (app M↠N M'↠N') = app (repred M↠N) (repred M'↠N')
repred (Λ M↠N) = Λ (repred M↠N)
repred (imp φ↠φ' ψ↠ψ') = imp (repred φ↠φ') (repred ψ↠ψ')

liftSub-red : ∀ {U} {V} {ρ σ : U → Term V} → (∀ x → ρ x ↠ σ x) → (∀ x → liftSub ρ x ↠ liftSub σ x)
liftSub-red ρ↠σ ⊥ = ref
liftSub-red ρ↠σ (↑ x) = repred (ρ↠σ x)

subred : ∀ {U} {V} {ρ σ : U → Term V} (M : Term U) → (∀ x → ρ x ↠ σ x) → sub ρ M ↠ sub σ M
subred (var x) ρ↠σ = ρ↠σ x
subred ⊥ ρ↠σ = ref
subred (app M N) ρ↠σ = app (subred M ρ↠σ) (subred N ρ↠σ)
subred (Λ A M) ρ↠σ = Λ (subred M (liftSub-red ρ↠σ))
subred (φ ⇒ ψ) ρ↠σ = imp (subred φ ρ↠σ) (subred ψ ρ↠σ)

subsub : ∀ {U} {V} {W} (σ : V → Term W) (ρ : U → Term V) (M : Term U) →
  sub σ (sub ρ M) ≡ sub (λ x → sub σ (ρ x)) M
subsub σ ρ (var x) = ref
subsub σ ρ ⊥ = ref
subsub σ ρ (app M N) = wd2 app (subsub σ ρ M) (subsub σ ρ N)
subsub σ ρ (Λ A M) = wd (Λ A) (trans (subsub (liftSub σ) (liftSub ρ) M) 
  (subwd (λ x → sym (liftSub-comp σ ρ x)) M))
subsub σ ρ (φ ⇒ ψ) = wd2 _⇒_ (subsub σ ρ φ) (subsub σ ρ ψ)

subredr : ∀ {U} {V} {σ : U → Term V} {M N : Term U} → M ↠ N → sub σ M ↠ sub σ N
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
