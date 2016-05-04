\begin{code}
module PHOPL where

open import Data.List
open import Data.Nat
open import Data.Fin
open import Prelims
open import Grammar using (Taxonomy)
open import Grammar.Grammar2
import Reduction2
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
\newcommand{\FinSet}{\mathbf{FinSet}}
In the implementation, we write $\Term{V}$ for the set of all terms with free variables a subset of $V$, where $V : \FinSet$.

\begin{code}
data PHOPLVarKind : Set where
  -Proof : PHOPLVarKind
  -Term : PHOPLVarKind

data PHOPLNonVarKind : Set where
  -Type : PHOPLNonVarKind

PHOPLTaxonomy : Taxonomy
PHOPLTaxonomy = record { 
  VarKind = PHOPLVarKind; 
  NonVarKind = PHOPLNonVarKind }

module PHOPLGrammar where
  open Taxonomy PHOPLTaxonomy

  data PHOPLcon : ∀ {K : ExpressionKind} → Kind' (-Constructor K) → Set where
    -appProof : PHOPLcon (Π [] (varKind -Proof) (Π [] (varKind -Proof) (out {K = varKind -Proof})))
    -lamProof : PHOPLcon (Π [] (varKind -Term) (Π [ -Proof ] (varKind -Proof) (out {K = varKind -Proof})))
    -bot : PHOPLcon (out {K = varKind -Term})
    -imp : PHOPLcon (Π [] (varKind -Term) (Π [] (varKind -Term) (out {K = varKind -Term})))
    -appTerm : PHOPLcon (Π [] (varKind -Term) (Π [] (varKind -Term) (out {K = varKind -Term})))
    -lamTerm : PHOPLcon (Π [] (nonVarKind -Type) (Π [ -Term ] (varKind -Term) (out {K = varKind -Term})))
    -Omega : PHOPLcon (out {K = nonVarKind -Type})
    -func  : PHOPLcon (Π [] (nonVarKind -Type) (Π [] (nonVarKind -Type) (out {K = nonVarKind -Type})))

  PHOPLparent : PHOPLVarKind → ExpressionKind
  PHOPLparent -Proof = varKind -Term
  PHOPLparent -Term = nonVarKind -Type

  PHOPL : Grammar'
  PHOPL = record { 
    taxonomy = PHOPLTaxonomy;
    toGrammar = record { 
      Constructor = PHOPLcon; 
      parent = PHOPLparent } }

module PHOPL where
  open PHOPLGrammar using (PHOPLcon;-appProof;-lamProof;-bot;-imp;-appTerm;-lamTerm;-Omega;-func)
  open Grammar' PHOPLGrammar.PHOPL

  Type : Set
  Type = Expression ∅ (nonVarKind -Type)

  liftType : ∀ {V} → Type → Expression V (nonVarKind -Type)
  liftType (app -Omega out) = app -Omega out
  liftType (app -func (A ,, B ,, out)) = app -func (liftType A ,, liftType B ,, out) 

  Ω : Type
  Ω = app -Omega out

  infix 75 _⇛_
  _⇛_ : Type → Type → Type
  φ ⇛ ψ = app -func (φ ,,  ψ ,, out)

  lowerType : ∀ {V} → Expression V (nonVarKind -Type) → Type
  lowerType (app -Omega ou) = Ω
  lowerType (app -func (φ ,, ψ ,, out)) = lowerType φ ⇛ lowerType ψ

{-  infix 80 _,_
  data TContext : Alphabet → Set where
    〈〉 : TContext ∅
    _,_ : ∀ {V} → TContext V → Type → TContext (V , -Term) -}

  TContext : Alphabet → Set
  TContext = Context -Term

  Term : Alphabet → Set
  Term V = Expression V (varKind -Term)

  ⊥ : ∀ {V} → Term V
  ⊥ = app -bot out

  appTerm : ∀ {V} → Term V → Term V → Term V
  appTerm M N = app -appTerm (M ,, N ,, out)

  ΛTerm : ∀ {V} → Type → Term (V , -Term) → Term V
  ΛTerm A M = app -lamTerm (liftType A ,,  M ,, out)

  _⊃_ : ∀ {V} → Term V → Term V → Term V
  φ ⊃ ψ = app -imp (φ ,, ψ ,, out)

  PAlphabet : ℕ → Alphabet → Alphabet
  PAlphabet zero A = A
  PAlphabet (suc P) A = PAlphabet P A , -Proof

  liftVar : ∀ {A} {K} P → Var A K → Var (PAlphabet P A) K
  liftVar zero x = x
  liftVar (suc P) x = ↑ (liftVar P x)

  liftVar' : ∀ {A} P → Fin P → Var (PAlphabet P A) -Proof
  liftVar' (suc P) zero = x₀
  liftVar' (suc P) (suc x) = ↑ (liftVar' P x)

  liftExp : ∀ {V} {K} P → Expression V K → Expression (PAlphabet P V) K
  liftExp P E = E 〈 (λ _ → liftVar P) 〉

  data PContext' (V : Alphabet) : ℕ → Set where
    〈〉 : PContext' V zero
    _,_ : ∀ {P} → PContext' V P → Term V → PContext' V (suc P)

  PContext : Alphabet → ℕ → Set
  PContext V = Context' V -Proof

  P〈〉 : ∀ {V} → PContext V zero
  P〈〉 = 〈〉

  _P,_ : ∀ {V} {P} → PContext V P → Term V → PContext V (suc P)
  _P,_ {V} {P} Δ φ = Δ , φ 〈 embedl {V} { -Proof} {P} 〉

  Proof : Alphabet → ℕ → Set
  Proof V P = Expression (PAlphabet P V) (varKind -Proof)

  varP : ∀ {V} {P} → Fin P → Proof V P
  varP {P = P} x = var (liftVar' P x)

  appP : ∀ {V} {P} → Proof V P → Proof V P → Proof V P
  appP δ ε = app -appProof (δ ,, ε ,, out)

  ΛP : ∀ {V} {P} → Term V → Proof V (suc P) → Proof V P
  ΛP {P = P} φ δ = app -lamProof (liftExp P φ ,, δ ,, out)

--  typeof' : ∀ {V} → Var V -Term → TContext V → Type
--  typeof' x₀ (_ , A) = A
--  typeof' (↑ x) (Γ , _) = typeof' x Γ

  propof : ∀ {V} {P} → Fin P → PContext' V P → Term V
  propof zero (_ , φ) = φ
  propof (suc x) (Γ , _) = propof x Γ

  data β : ∀ {V} {K} {C} → Constructor C → Subexpression V (-Constructor K) C → Expression V K → Set where
    βI : ∀ {V} A (M : Term (V , -Term)) N → β -appTerm (ΛTerm A M ,, N ,, out) (M ⟦ x₀:= N ⟧)
  open Reduction2 PHOPLGrammar.PHOPL β
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
  infix 10 _⊢_∶_
  data _⊢_∶_ : ∀ {V} → TContext V → Term V → Expression V (nonVarKind -Type) → Set₁ where
    var : ∀ {V} {Γ : TContext V} {x} → Γ ⊢ var x ∶ typeof x Γ
    ⊥R : ∀ {V} {Γ : TContext V} → Γ ⊢ ⊥ ∶ Ω 〈 (λ _ ()) 〉
    imp : ∀ {V} {Γ : TContext V} {φ} {ψ} → Γ ⊢ φ ∶ Ω 〈 (λ _ ()) 〉 → Γ ⊢ ψ ∶ Ω 〈 (λ _ ()) 〉 → Γ ⊢ φ ⊃ ψ ∶ Ω 〈 (λ _ ()) 〉
    app : ∀ {V} {Γ : TContext V} {M} {N} {A} {B} → Γ ⊢ M ∶ app -func (A ,, B ,, out) → Γ ⊢ N ∶ A → Γ ⊢ appTerm M N ∶ B
    Λ : ∀ {V} {Γ : TContext V} {A} {M} {B} → Γ , A ⊢ M ∶ liftE B → Γ ⊢ app -lamTerm (A ,, M ,, out) ∶ app -func (A ,, B ,, out)

  data Pvalid : ∀ {V} {P} → TContext V → PContext' V P → Set₁ where
    〈〉 : ∀ {V} {Γ : TContext V} → Pvalid Γ 〈〉
    _,_ : ∀ {V} {P} {Γ : TContext V} {Δ : PContext' V P} {φ : Term V} → Pvalid Γ Δ → Γ ⊢ φ ∶ Ω 〈 (λ _ ()) 〉 → Pvalid Γ (Δ , φ)

  infix 10 _,,_⊢_∶∶_
  data _,,_⊢_∶∶_ : ∀ {V} {P} → TContext V → PContext' V P → Proof V P → Term V → Set₁ where
    var : ∀ {V} {P} {Γ : TContext V} {Δ : PContext' V P} {p} → Pvalid Γ Δ → Γ ,, Δ ⊢ varP p ∶∶ propof p Δ 
    app : ∀ {V} {P} {Γ : TContext V} {Δ : PContext' V P} {δ} {ε} {φ} {ψ} → Γ ,, Δ ⊢ δ ∶∶ φ ⊃ ψ → Γ ,, Δ ⊢ ε ∶∶ φ → Γ ,, Δ ⊢ appP {V} {P} δ ε ∶∶ ψ
    Λ : ∀ {V} {P} {Γ : TContext V} {Δ : PContext' V P} {φ} {δ} {ψ} → Γ ,, Δ , φ ⊢ δ ∶∶ ψ → Γ ,, Δ ⊢ ΛP {V} {P} φ δ ∶∶ φ ⊃ ψ
    convR : ∀ {V} {P} {Γ : TContext V} {Δ : PContext' V P} {δ} {φ} {ψ} → Γ ,, Δ ⊢ δ ∶∶ φ → Γ ⊢ ψ ∶ Ω 〈 (λ _ ()) 〉 → φ ≃ ψ → Γ ,, Δ ⊢ δ ∶∶ ψ
\end{code}
