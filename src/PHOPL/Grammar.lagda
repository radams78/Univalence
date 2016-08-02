\AgdaHide{
\begin{code}
module PHOPL.Grammar where

open import Data.Empty renaming (⊥ to Empty)
open import Data.List
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
\text{Path} & P, Q & ::= & e \mid \reff{M} \mid P \sup^* Q \mid \univ{\phi}{\psi}{P}{Q} \mid \triplelambda e : x =_A y. P \mid P_{MN} Q \\
\text{Context} & \Gamma, \Delta, \Theta & ::= & \langle \rangle \mid \Gamma, x : A \mid \Gamma, p : \phi \mid \Gamma, e : M =_A N \\
\text{Judgement} & \mathcal{J} & ::= & \Gamma \vald \mid \Gamma \vdash M : A \mid \Gamma \vdash \delta : \phi \mid \Gamma \vdash P : M =_A N
\end{array}
\]


In the path $\triplelambda e : x =_A y . P$, the term variables $x$ and $y$ must be distinct.  The term variable $x$ is bound within $M$ in the term $\lambda x:A.M$,
and the proof variable $p$ is bound within $\delta$ in $\lambda p:\phi.\delta$.  The three variables $e$, $x$ and $y$ are bound within $P$ in the path
$\triplelambda e:x =_A y.P$.  We identify terms, proofs and paths up to $\alpha$-conversion.

We shall use the word 'expression' to mean either a type, term, proof or path.  We shall use $s$, $t$, $S$ and $T$ as metavariables that range over expressions.

Note that we use both Roman letters $M$, $N$ and Greek letters $\phi$, $\psi$, $\chi$ to range over terms.  Intuitively, a term is understood as either a proposition or a function,
and we shall use Greek letters for terms that are intended to be propositions.  Formally, there is no significance to which letter we choose.

\todo{Give the intuition}.

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

  data Type : Set where
    Ω : Type
    _⇛_ : Type → Type → Type

  data PHOPLcon : ∀ {K : ExpressionKind} → 
    Kind (-Constructor K) → Set where
    -ty : Type → PHOPLcon (out (nonVarKind -Type))
    -appProof : PHOPLcon (Π (Π _ (varKind -Proof ●)) (Π (Π _ (varKind -Proof ●)) (out (varKind -Proof))))
    -lamProof : PHOPLcon (Π (Π _ (varKind -Term ●))
      (Π (Π _ (-Proof ⟶ varKind -Proof ●)) (out (varKind -Proof))))
    -bot : PHOPLcon (out (varKind -Term))
    -imp : PHOPLcon (Π (Π _ (varKind -Term ●)) (Π (Π _ (varKind -Term ●)) (out (varKind -Term))))
    -appTerm : PHOPLcon (Π (Π _ (varKind -Term ●)) (Π (Π _ (varKind -Term ●)) (out (varKind -Term))))
    -lamTerm : Type → PHOPLcon (Π (Π _ (-Term ⟶ varKind -Term ●)) (out (varKind -Term)))
    -ref : PHOPLcon (Π (Π _ (varKind -Term ●)) (out (varKind -Path)))
    -imp* : PHOPLcon (Π (Π _ (varKind -Path ●)) (Π (Π _ (varKind -Path ●)) (out (varKind -Path))))
    -univ : PHOPLcon (Π (Π _ (varKind -Term ●)) (Π (Π _ (varKind -Term ●)) (Π (Π _ (varKind -Proof ●)) (Π (Π _ (varKind -Proof ●)) (out (varKind -Path))))))
    -lll : Type → PHOPLcon (Π (Π _ (-Term ⟶ -Term ⟶ -Path ⟶ varKind -Path ●)) (out (varKind -Path)))
    -app* : PHOPLcon (Π (Π _ (varKind -Term ●)) (Π (Π _ (varKind -Term ●)) (Π (Π _ (varKind -Path ●)) (Π (Π _ (varKind -Path ●)) (out (varKind -Path))))))
    -plus : PHOPLcon (Π (Π _ (varKind -Path ●)) (out (varKind -Proof)))
    -minus : PHOPLcon (Π (Π _ (varKind -Path ●)) (out (varKind -Proof)))
    -eq : Type → PHOPLcon (Π (Π _ (varKind -Term ●)) (Π (Π _ (varKind -Term ●)) (out (nonVarKind -Equation))))

  PHOPLparent : PHOPLVarKind → ExpressionKind
  PHOPLparent -Proof = varKind -Term
  PHOPLparent -Term = nonVarKind -Type
  PHOPLparent -Path = nonVarKind -Equation

  PHOPL : Grammar
  PHOPL = record { 
    taxonomy = PHOPLTaxonomy;
    isGrammar = record { 
      Constructor = PHOPLcon; 
      parent = PHOPLparent } }

open PHOPLgrammar public
open import Grammar PHOPL public

Proof : Alphabet → Set
Proof V = Expression V (varKind -Proof)

Term : Alphabet → Set
Term V = Expression V (varKind -Term)

Path : Alphabet → Set
Path V = Expression V (varKind -Path)

Equation : Alphabet → Set
Equation V = Expression V (nonVarKind -Equation)

appP : ∀ {V} → Proof V → Proof V → Proof V
appP δ ε = app -appProof (δ ,, ε ,, out)

ΛP : ∀ {V} → Term V → Proof (V , -Proof) → Proof V
ΛP φ δ = app -lamProof (φ ,, δ ,, out)

⊥ : ∀ {V} → Term V
⊥ = app -bot out

infix 65 _⊃_
_⊃_ : ∀ {V} → Term V → Term V → Term V
φ ⊃ ψ = app -imp (φ ,, ψ ,, out)

appT : ∀ {V} → Term V → Term V → Term V
appT M N = app -appTerm (M ,, N ,, out)

appT-injl : ∀ {V} {M M' N N' : Term V} → appT M N ≡ appT M' N' → M ≡ M'
appT-injl refl = refl

ΛT : ∀ {V} → Type → Term (V , -Term) → Term V
ΛT A M = app (-lamTerm A) (M ,, out)

reff : ∀ {V} → Term V → Path V
reff M = app -ref (M ,, out)

infix 15 _⊃*_
_⊃*_ : ∀ {V} → Path V → Path V → Path V
P ⊃* Q = app -imp* (P ,, Q ,, out)

univ : ∀ {V} → Term V → Term V → Proof V → Proof V → Path V
univ φ ψ P Q = app -univ (φ ,, ψ ,, P ,, Q ,, out)

λλλ : ∀ {V} → Type → Path (V , -Term , -Term , -Path) → Path V
λλλ A P = app (-lll A) (P ,, out)

app* : ∀ {V} → Term V → Term V → Path V → Path V → Path V
app* M N P Q = app -app* (M ,, N ,, P ,, Q ,, out)

plus : ∀ {V} → Path V → Proof V
plus P = app -plus (P ,, out)

minus : ∀ {V} → Path V → Proof V
minus P = app -minus (P ,, out)

ty : ∀ {V} → Type → Expression V (nonVarKind -Type)
ty A = app (-ty A) out

yt : ∀ {V} → Expression V (nonVarKind -Type) → Type
yt (app (-ty A) out) = A

ty-yt : ∀ {V} {A : Expression V (nonVarKind -Type)} → ty (yt A) ≡ A
ty-yt {A = app (-ty _) out} = refl

infix 60 _≡〈_〉_
_≡〈_〉_ : ∀ {V} → Term V → Type → Term V → Equation V
M ≡〈 A 〉 N = app (-eq A) (M ,, N ,, out)

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

APP : ∀ {V} → Term V → List (Term V) → Term V
APP M [] = M
APP M (N ∷ NN) = APP (appT M N) NN
--REFACTOR Remove this?

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
