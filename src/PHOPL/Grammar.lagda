\AgdaHide{
\begin{code}
module PHOPL.Grammar where

open import Data.Empty renaming (⊥ to Empty)
open import Data.List
open import Data.Vec
open import Prelims
open import Grammar.Taxonomy
open import Grammar.Base
\end{code}
}

\subsection{Syntax}

Fix three disjoint, infinite sets of variables, which we shall call \emph{term variables}, \emph{proof variables}
and \emph{path variables}.  We shall use $x$ and $y$ as term variables, $p$ and $q$ as proof variables,
$e$ as a path variable, and $z$ for a variable that may come from any of these three sets.

The syntax of $\lambda o e$ is given by the grammar:

\[
\begin{array}{lrcl}
\text{Type} & A,B,C & ::= & \Omega \mid A \rightarrow B \\
\text{Term} & L,M,N, \phi,\psi,\chi & ::= & x \mid \bot \mid \phi \supset \psi \mid \lambda x:A.M \mid MN \\
\text{Proof} & \delta, \epsilon & ::= & p \mid \lambda p:\phi.\delta \mid \delta \epsilon \mid P^+ \mid P^- \\
\text{Path} & P, Q & ::= & e \mid \reff{M} \mid P \supset^* Q \mid \univ{\phi}{\psi}{P}{Q} \mid \\
& & & \triplelambda e : x =_A y. P \mid P_{MN} Q \\
\text{Context} & \Gamma, \Delta, \Theta & ::= & \langle \rangle \mid \Gamma, x : A \mid \Gamma, p : \phi \mid \Gamma, e : M =_A N \\
\text{Judgement} & \mathbf{J} & ::= & \Gamma \vald \mid \Gamma \vdash M : A \mid \Gamma \vdash \delta : \phi \mid \\
& & & \Gamma \vdash P : M =_A N
\end{array}
\]

In the path $\triplelambda e : x =_A y . P$, the term variables $x$ and $y$ must be distinct.  (We also have $x \not\equiv e \not\equiv y$, thanks to our
stipulation that term variables and path variables are disjoint.)  The term variable $x$ is bound within $M$ in the term $\lambda x:A.M$,
and the proof variable $p$ is bound within $\delta$ in $\lambda p:\phi.\delta$.  The three variables $e$, $x$ and $y$ are bound within $P$ in the path
$\triplelambda e:x =_A y.P$.  We identify terms, proofs and paths up to $\alpha$-conversion.

We shall use the word 'expression' to mean either a type, term, proof, path, or equation (an equation having the form $M =_A N$).  We shall use $r$, $s$, $t$, $S$ and $T$ as metavariables that range over expressions.

Note that we use both Roman letters $M$, $N$ and Greek letters $\phi$, $\psi$, $\chi$ to range over terms.  Intuitively, a term is understood as either a proposition or a function,
and we shall use Greek letters for terms that are intended to be propositions.  Formally, there is no significance to which letter we choose.

Note also that the types of $\lambda o e$ are just the simple types over $\Omega$; therefore, no variable can occur in a type.

The intuition behind the new expressions is as follows (see also the rules of deduction in Figure \ref{fig:lambdaoe}).  For any object $M : A$, there is the trivial path $\reff{M} : M =_A M$.  The constructor $\supset^*$ ensures congruence for $\supset$ --- if $P : \phi =_\Omega \phi'$ and $Q : \psi =_\Omega \psi'$ then $P \supset^* Q : \phi \supset \psi =_\Omega \phi' \supset \psi'$.  The constructor $\mathsf{univ}$ gives univalence for our propositions: if $\delta : \phi \supset \psi$ and $\epsilon : \psi \supset \phi$, then $\univ{\phi}{\psi}{\delta}{\epsilon}$ is a path of type $\phi =_\Omega \psi$.  The constructors $^+$ and $^-$ are the converses: if $P$ is a path of type $\phi =_\Omega \psi$, then $P^+$ is a proof of $\phi \supset \psi$, and $P^-$ is a proof of $\psi \supset \phi$.

The constructor $\triplelambda$ gives functional extensionality.  Let $F$ and $G$ be functions of type $A \rightarrow B$.  If $F x =_B G y$ whenever $x =_A y$, then $F =_{A \rightarrow B} G$.  More formally, if $P$ is a path of type $Fx =_B Gy$ that depends on $x : A$, $y : A$ and $e : x =_A y$, then $\triplelambda e : x =_A y . P$ is a path of type $F =_{A \rightarrow B} G$.

Finally, if $P$ is a path of type $F =_{A \rightarrow B} G$, and $Q$ is a path $M =_A N$, then $P_{MN} Q$ is a path $FM =_B G N$.

\begin{code}
data PHOPLVarKind : Set where
  -Proof : PHOPLVarKind
  -Term : PHOPLVarKind
  -Path : PHOPLVarKind

data PHOPLNonVarKind : Set where
  -Type : PHOPLNonVarKind
  -Equation : PHOPLNonVarKind

PHOPLTaxonomy : Taxonomy
PHOPLTaxonomy = record { 
  VarKind = PHOPLVarKind; 
  NonVarKind = PHOPLNonVarKind }

module PHOPLgrammar where
  open Taxonomy PHOPLTaxonomy

  -vProof : ExpKind
  -vProof = varKind -Proof

  -vTerm : ExpKind
  -vTerm = varKind -Term

  -vPath : ExpKind
  -vPath = varKind -Path

  -nvType : ExpKind
  -nvType = nonVarKind -Type

  -nvEq : ExpKind
  -nvEq = nonVarKind -Equation

  data Type : Set where
    Ω : Type
    _⇛_ : Type → Type → Type

  data PHOPLcon : ConKind → Set where
    -ty : Type → PHOPLcon (-nvType ✧)
    -appProof : PHOPLcon (-vProof ✧ ⟶ -vProof ✧ ⟶ -vProof ✧)
    -lamProof : PHOPLcon (-vTerm ✧ ⟶ (-Proof ⟶ -vProof ✧) ⟶ -vProof ✧)
    -bot : PHOPLcon (-vTerm ✧)
    -imp : PHOPLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -vTerm ✧)
    -appTerm : PHOPLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -vTerm ✧)
    -lamTerm : Type → PHOPLcon ((-Term ⟶ -vTerm ✧) ⟶ -vTerm ✧)
    -ref : PHOPLcon (-vTerm ✧ ⟶ -vPath ✧)
    -imp* : PHOPLcon (-vPath ✧ ⟶ -vPath ✧ ⟶ -vPath ✧)
    -univ : PHOPLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -vProof ✧ ⟶ -vProof ✧ ⟶ -vPath ✧)
    -lll : Type → PHOPLcon ((-Term ⟶ -Term ⟶ -Path ⟶ -vPath ✧) ⟶ -vPath ✧)
    -app* : PHOPLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -vPath ✧ ⟶ -vPath ✧ ⟶ -vPath ✧)
    -plus : PHOPLcon (-vPath ✧ ⟶ -vProof ✧)
    -minus : PHOPLcon (-vPath ✧ ⟶ -vProof ✧)
    -eq : Type → PHOPLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -nvEq ✧)

  PHOPLparent : PHOPLVarKind → ExpKind
  PHOPLparent -Proof = -vTerm
  PHOPLparent -Term = -nvType
  PHOPLparent -Path = -nvEq

  PHOPL : Grammar
  PHOPL = record { 
    taxonomy = PHOPLTaxonomy;
    isGrammar = record { 
      Constructor = PHOPLcon; 
      parent = PHOPLparent } }

open PHOPLgrammar public
open import Grammar PHOPL public

Proof : Alphabet → Set
Proof V = Expression V -vProof

Term : Alphabet → Set
Term V = Expression V -vTerm

Path : Alphabet → Set
Path V = Expression V -vPath

Equation : Alphabet → Set
Equation V = Expression V -nvEq

appP : ∀ {V} → Proof V → Proof V → Proof V
appP δ ε = app -appProof (δ ∷ ε ∷ [])

ΛP : ∀ {V} → Term V → Proof (V , -Proof) → Proof V
ΛP φ δ = app -lamProof (φ ∷ δ ∷ [])

⊥ : ∀ {V} → Term V
⊥ = app -bot []

infix 65 _⊃_
_⊃_ : ∀ {V} → Term V → Term V → Term V
φ ⊃ ψ = app -imp (φ ∷ ψ ∷ [])

appT : ∀ {V} → Term V → Term V → Term V
appT M N = app -appTerm (M ∷ N ∷ [])

appT-injl : ∀ {V} {M M' N N' : Term V} → appT M N ≡ appT M' N' → M ≡ M'
appT-injl refl = refl

ΛT : ∀ {V} → Type → Term (V , -Term) → Term V
ΛT A M = app (-lamTerm A) (M ∷ [])

reff : ∀ {V} → Term V → Path V
reff M = app -ref (M ∷ [])

infix 15 _⊃*_
_⊃*_ : ∀ {V} → Path V → Path V → Path V
P ⊃* Q = app -imp* (P ∷ Q ∷ [])

univ : ∀ {V} → Term V → Term V → Proof V → Proof V → Path V
univ φ ψ P Q = app -univ (φ ∷ ψ ∷ P ∷ Q ∷ [])

λλλ : ∀ {V} → Type → Path (V , -Term , -Term , -Path) → Path V
λλλ A P = app (-lll A) (P ∷ [])

app* : ∀ {V} → Term V → Term V → Path V → Path V → Path V
app* M N P Q = app -app* (M ∷ N ∷ P ∷ Q ∷ [])

plus : ∀ {V} → Path V → Proof V
plus P = app -plus (P ∷ [])

minus : ∀ {V} → Path V → Proof V
minus P = app -minus (P ∷ [])

ty : ∀ {V} → Type → Expression V (nonVarKind -Type)
ty A = app (-ty A) []

yt : ∀ {V} → Expression V (nonVarKind -Type) → Type
yt (app (-ty A) []) = A

ty-yt : ∀ {V} {A : Expression V (nonVarKind -Type)} → ty (yt A) ≡ A
ty-yt {A = app (-ty _) []} = refl

Pi : ∀ {n} → snocVec Type n → Type → Type
Pi [] B = B
Pi (AA snoc A) B = Pi AA (A ⇛ B)

APP : ∀ {V n} → Term V → snocVec (Term V) n → Term V
APP M [] = M
APP M (NN snoc N) = appT (APP M NN) N

APPP : ∀ {V} {n} → Proof V → Vec (Proof V) n → Proof V
APPP δ [] = δ
APPP δ (ε ∷ εε) = APPP (appP δ ε) εε

APP* : ∀ {V n} → snocVec (Term V) n → snocVec (Term V) n → Path V → snocVec (Path V) n → Path V
APP* [] [] P [] = P
APP* (MM snoc M) (NN snoc N) P (QQ snoc Q) = app* M N (APP* MM NN P QQ) Q

infix 60 _≡〈_〉_
_≡〈_〉_ : ∀ {V} → Term V → Type → Term V → Equation V
M ≡〈 A 〉 N = app (-eq A) (M ∷ N ∷ [])

infixl 59 _,T_
_,T_ : ∀ {V} → Context V → Type → Context (V , -Term)
Γ ,T A = Γ , ty A

infixl 59 _,P_
_,P_ : ∀ {V} → Context V → Term V → Context (V , -Proof)
_,P_ = _,_

infixl 59 _,E_
_,E_ : ∀ {V} → Context V → Equation V → Context (V , -Path)
_,E_ = _,_
\end{code}

\AgdaHide{
\begin{code}
typeof' : ∀ {V} → Var V -Term → Context V → Type
typeof' x Γ  = yt (typeof x Γ)

typeof-typeof' : ∀ {V} {x : Var V -Term} {Γ} → typeof x Γ ≡ ty (typeof' x Γ)
typeof-typeof' = sym ty-yt

addpath : ∀ {V} → Context V → Type → Context (V , -Term , -Term , -Path)
addpath Γ A = Γ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀

sub↖ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (V , -Term , -Term , -Path)
sub↖ σ _ x₀ = var x₂
sub↖ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

postulate sub↖-cong : ∀ {U} {V} {ρ σ : Sub U V} → ρ ∼ σ → sub↖ ρ ∼ sub↖ σ

postulate sub↖-comp₁ : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
                     sub↖ (ρ •RS σ) ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↖ σ

sub↗ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (V , -Term , -Term , -Path)
sub↗ σ _ x₀ = var x₁
sub↗ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

postulate sub↗-cong : ∀ {U} {V} {ρ σ : Sub U V} → ρ ∼ σ → sub↗ ρ ∼ sub↗ σ

postulate sub↗-comp₁ : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
                     sub↗ (ρ •RS σ) ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↗ σ

--REFACTOR Duplication

var-not-Λ : ∀ {V} {x : Var V -Term} {A} {M : Term (V , -Term)} → var x ≡ ΛT A M → Empty
var-not-Λ ()

app-not-Λ : ∀ {V} {M N : Term V} {A} {P : Term (V , -Term)} → appT M N ≡ ΛT A P → Empty
app-not-Λ ()

appT-injr : ∀ {V} {M N P Q : Term V} → appT M N ≡ appT P Q → N ≡ Q
appT-injr refl = refl

imp-injl : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ≡ φ' ⊃ ψ' → φ ≡ φ'
imp-injl refl = refl

imp-injr : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ≡ φ' ⊃ ψ' → ψ ≡ ψ'
imp-injr refl = refl
--REFACTOR General pattern
\end{code}
}

\paragraph{Substitution}

We write $t[z:=s]$ for the result of substituting $s$ for $z$ in $t$,
renaming bound variables to avoid capture.  We write $s[z_1 := t_1, \ldots, z_n := t_n]$
or $s[\vec{z} := \vec{t}]$ for the result of simultaneously substituting
each $t_i$ for $z_i$ in $s$.

A \emph{substitution} $\sigma$ is a function whose domain is a finite set of variables, and
which maps term variables to terms, proof variables to proofs, and path variables to paths.
Given a substitution $\sigma$ and an expression $t$, we write $t[\sigma]$ for the result
of simultaneously substituting $\sigma(z)$ for $z$ within $t$, for each variable $z$ in the domain of $\sigma$.

Given two substitutions $\sigma$ and $\rho$, we define their \emph{composition} $\sigma \circ \rho$ to
be the substitution with the same domain an $\rho$, such that
\[ (\sigma \circ \rho)(x) \eqdef \rho(x)[\sigma] \enspace . \]
An easy induction on $t$ shows that we have $t [\sigma \circ \rho] \equiv t [ \rho ] [ \sigma ]$.
