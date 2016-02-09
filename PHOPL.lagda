\begin{code}
module PHOPL where
open import Prelims hiding (⊥)
open import Grammar
\end{code}

\section{Predicative Higher-Order Propositional Logic}

Fix sets of \emph{proof variables} and \emph{term variables}.

The syntax of the system is given by the following grammar.

%Changes from Marc and Thierry's system:
%Taken out the proof c of \bot
\[ \begin{array}{lrcl}
\text{Proof} & \delta & ::= & p \mid \delta \delta \mid \lambda p : \phi . \delta \\
\text{Term} & M, \phi & ::= & x \mid \bot \mid M M \mid \lambda x : A . M \mid \phi \rightarrow \phi \\
\text{Type} & A & ::= & \Omega \mid A \rightarrow A \\
\text{Term Context} & \Gamma & ::= & \langle \rangle \mid \Gamma , x : A \\
\text{Proof Context} & \Delta & ::= & \langle \rangle \mid \Delta, p : \phi \\
\text{Judgement} & \mathcal{J} & ::= & \Gamma \vald \mid \Gamma \vdash M : A \mid \Gamma, \Delta \vald \mid \Gamma, \Delta \vdash \delta : \phi 
\end{array} \]
where $p$ ranges over proof variables and $x$ ranges over term variables.  The variable $p$ is bound within $\delta$ in the proof $\lambda p : \phi . \delta$,
and the variable $x$ is bound within $M$ in the term $\lambda x : A . M$.  We identify proofs and terms up to $\alpha$-conversion.

\newcommand{\Term}[1]{\mathbf{Term} \left( #1 \right)}
In the implementation, we write $\Term{V}$ for the set of all terms with free variables a subset of $V$, where $V : \FinSet$.

\begin{code}
data PHOPLkind : Set where
  -Proof : PHOPLkind
  -Term  : PHOPLkind
  -Type  : PHOPLkind

data PHOPLcon : ∀ {K : PHOPLkind} → ConstructorKind K → Set where
  -appProof : PHOPLcon (Π (out -Proof) (Π (out -Proof) (out {K = -Proof})))
  -lamProof : PHOPLcon (Π (out -Term) (Π (Π -Proof (out -Proof)) (out {K = -Proof})))
  -bot : PHOPLcon (out {K = -Term})
  -imp : PHOPLcon (Π (out -Term) (Π (out -Term) (out {K = -Term})))
  -appTerm : PHOPLcon (Π (out -Term) (Π (out -Term) (out {K = -Term})))
  -lamTerm : PHOPLcon (Π (out -Type) (Π (Π -Term (out -Term)) (out {K = -Term})))
  -Omega : PHOPLcon (out {K = -Type})
  -func  : PHOPLcon (Π (out -Type) (Π (out -Type) (out {K = -Type})))

data PHOPLparent : PHOPLkind → PHOPLkind → Set where
  ProofTerm : PHOPLparent -Proof -Term
  TermType  : PHOPLparent -Term -Type

PHOPL : Grammar
PHOPL = record { 
  ExpressionKind = PHOPLkind; 
  Constructor = PHOPLcon; 
  parent = PHOPLparent }

module PHOPL where
  open Grammar.Grammar PHOPL

  Type : Set
  Type = Expression ∅ -Type

  liftType : ∀ {V} → Type → Expression V -Type
  liftType (var ())
  liftType (app -Omega out) = app -Omega out
  liftType (app -func (app (out A) (app (out B) out))) = app -func (app (out (liftType A)) (app (out (liftType B)) out)) 

  Ω : Type
  Ω = app -Omega out

  _⇒_ : Type → Type → Type
  φ ⇒ ψ = app -func (app (out φ) (app (out ψ) out))

  VAlphabet : FinSet → Alphabet
  VAlphabet ∅ = ∅
  VAlphabet (Lift X) = VAlphabet X , -Term

  inVar : ∀ {V} → El V → Var (VAlphabet V) -Term
  inVar Prelims.⊥ = x₀
  inVar (↑ x) = ↑ (inVar x)

  lowerType : ∀ {V} → Expression (VAlphabet V) -Type → Type
  lowerType {∅} (var ())
  lowerType {Lift V} (var (↑ x)) = lowerType {V} (var x)
  lowerType (app -Omega out) = Ω
  lowerType (app -func (app (out φ) (app (out ψ) out))) = lowerType φ ⇒ lowerType ψ

  data TContext : FinSet → Set where
    〈〉 : TContext ∅
    _,_ : ∀ {V} → TContext V → Type → TContext (Lift V)

  Term : FinSet → Set
  Term V = Expression (VAlphabet V) -Term

  ⊥ : ∀ {V} → Term V
  ⊥ = app -bot out

  appTerm : ∀ {V} → Term V → Term V → Term V
  appTerm M N = app -appTerm (app (out M) (app (out N) out))

  ΛTerm : ∀ {V} → Type → Term (Lift V) → Term V
  ΛTerm A M = app -lamTerm (app (out (liftType A)) (app (Λ (out M)) out))

  _⊃_ : ∀ {V} → Term V → Term V → Term V
  φ ⊃ ψ = app -imp (app (out φ) (app (out ψ) out))

  PAlphabet : FinSet → Alphabet → Alphabet
  PAlphabet ∅ A = A
  PAlphabet (Lift P) A = PAlphabet P A , -Proof

  liftVar : ∀ {A} {K} P → Var A K → Var (PAlphabet P A) K
  liftVar ∅ x = x
  liftVar (Lift P) x = ↑ (liftVar P x)

  liftVar' : ∀ {A} P → El P → Var (PAlphabet P A) -Proof
  liftVar' (Lift P) Prelims.⊥ = x₀
  liftVar' (Lift P) (↑ x) = ↑ (liftVar' P x)

  liftExp : ∀ {V} {K} P → Expression (VAlphabet V) K → Expression (PAlphabet P (VAlphabet V)) K
  liftExp P E = E 〈 (λ _ → liftVar P) 〉

  data PContext' (V : FinSet) : FinSet → Set where
    〈〉 : PContext' V ∅
    _,_ : ∀ {P} → PContext' V P → Term V → PContext' V (Lift P)

  PContext : FinSet → FinSet → Set
  PContext V P = Context (VAlphabet V) → Context (PAlphabet P (VAlphabet V))

  P〈〉 : ∀ {V} → PContext V ∅
  P〈〉 Γ = Γ

  _P,_ : ∀ {V} {P} → PContext V P → Term V → PContext V (Lift P)
  _P,_ {V} {P} Δ φ Γ = _,_ {PAlphabet P (VAlphabet V)} { -Proof} { -Term} {ProofTerm} (Δ Γ) (liftExp P φ)

  Proof : FinSet → FinSet → Set
  Proof V P = Expression (PAlphabet P (VAlphabet V)) -Proof

  varP : ∀ {V} {P} → El P → Proof V P
  varP {P = P} x = var (liftVar' P x)

  appP : ∀ {V} {P} → Proof V P → Proof V P → Proof V P
  appP δ ε = app -appProof (app (out δ) (app (out ε) out))

  ΛP : ∀ {V} {P} → Term V → Proof V (Lift P) → Proof V P
  ΛP {P = P} φ δ = app -lamProof (app (out (liftExp P φ)) (app (Λ (out δ)) out))

  typeof' : ∀ {V} → El V → TContext V → Type
  typeof' Prelims.⊥ (_ , A) = A
  typeof' (↑ x) (Γ , _) = typeof' x Γ

  propof : ∀ {V} {P} → El P → PContext' V P → Term V
  propof Prelims.⊥ (_ , φ) = φ
  propof (↑ x) (Γ , _) = propof x Γ

  data β : ∀ {V} {K} → Expression V K → Expression V K → Set where
    βI : ∀ {V} A (M : Term (Lift V)) N → β (appTerm (ΛTerm A M) N) (M ⟦ x₀:= N ⟧)
{-
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
SNsub {V} {M} {N} (SNI MN-is-SN) = SNI (λ P M▷P → SNsub (MN-is-SN (P ⟦ botsub N ⟧) (subredr M▷P)))
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
  data Tvalid : ∀ {V} → TContext V → Set₁ where
    〈〉 : Tvalid 〈〉
    _,_ : ∀ {V} {Γ : TContext V} → Tvalid Γ → ∀ A → Tvalid (Γ , A)

  data _⊢_∶_ : ∀ {V} → TContext V → Term V → Type → Set₁ where
    var : ∀ {V} {Γ : TContext V} {x} → Tvalid Γ → Γ ⊢ var x ∶ typeof x Γ
    ⊥ : ∀ {V} {Γ : TContext V} → Tvalid Γ → Γ ⊢ ⊥ ∶ Ω
    imp : ∀ {V} {Γ : TContext V} {φ} {ψ} → Γ ⊢ φ ∶ Ω → Γ ⊢ ψ ∶ Ω → Γ ⊢ φ ⇒ ψ ∶ Ω
    app : ∀ {V} {Γ : TContext V} {M} {N} {A} {B} → Γ ⊢ M ∶ A ⇒ B → Γ ⊢ N ∶ A → Γ ⊢ app M N ∶ B
    Λ : ∀ {V} {Γ : TContext V} {A} {M} {B} → Γ , A ⊢ M ∶ B → Γ ⊢ Λ A M ∶ A ⇒ B

data Pvalid : ∀ {V} {P} → TContext V → PContext V P → Set₁ where
  〈〉 : ∀ {V} {Γ : TContext V} → Tvalid Γ → Pvalid Γ 〈〉
  _,_ : ∀ {V} {P} {Γ : TContext V} {Δ : PContext V P} {φ : Term V} → Pvalid Γ Δ → Γ ⊢ φ ∶ Ω → Pvalid Γ (Δ , φ)

data _,,_⊢_∶∶_ : ∀ {V} {P} → TContext V → PContext V P → Proof V P → Term V → Set₁ where
  var : ∀ {V} {P} {Γ : TContext V} {Δ : PContext V P} {p} → Pvalid Γ Δ → Γ ,, Δ ⊢ var p ∶∶ propof p Δ
  app : ∀ {V} {P} {Γ : TContext V} {Δ : PContext V P} {δ} {ε} {φ} {ψ} → Γ ,, Δ ⊢ δ ∶∶ φ ⇒ ψ → Γ ,, Δ ⊢ ε ∶∶ φ → Γ ,, Δ ⊢ app δ ε ∶∶ ψ
  Λ : ∀ {V} {P} {Γ : TContext V} {Δ : PContext V P} {φ} {δ} {ψ} → Γ ,, Δ , φ ⊢ δ ∶∶ ψ → Γ ,, Δ ⊢ Λ φ δ ∶∶ φ ⇒ ψ
  conv : ∀ {V} {P} {Γ : TContext V} {Δ : PContext V P} {δ} {φ} {ψ} → Γ ,, Δ ⊢ δ ∶∶ φ → Γ ⊢ ψ ∶ Ω → φ ≃ ψ → Γ ,, Δ ⊢ δ ∶∶ ψ -}
\end{code}
