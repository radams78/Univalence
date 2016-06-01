\AgdaHide{
\begin{code}
module PHOPL.Grammar where

open import Data.List
open import Data.Nat
open import Data.Fin
open import Prelims
open import Grammar.Taxonomy
open import Grammar.Base

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
\end{code}
}

\mode<beamer>{
\begin{frame}[fragile]
\frametitle{Simply-Typed Lambda Calculus}
We begin with the simply-typed lambda calculus (no surprises so far):

$$
\begin{array}{lrcl}
\text{Type} & A & ::= & \Omega \mid A \rightarrow A \\
\text{Term} & M,\phi & ::= & x \mid \lambda x:A.M \mid M M
\end{array}
$$

\[ \infer{\Gamma \vdash \lambda x:A.M : A \rightarrow B}{\Gamma, x : A \vdash M : B} \qquad
\infer{\Gamma \vdash M N : B} {\Gamma \vdash M : A \rightarrow B \quad \Gamma \vdash N : A} \]
}
\end{frame}
}

\mode<article>
We call the following type theory $\lambda o$, or \emph{predicative higher-order propositional logic}.  Its
syntax is given by the grammar:

\[
\begin{array}{lrcl}
\text{Type} & A & ::= & \Omega \mid A \rightarrow A \\
\text{Term} & M, \phi & ::= & x \mid \bot \mid \phi \sup \phi \mid \lambda x:A.M \mid MM \\
\text{Proof} & \delta & ::= & p \mid \lambda x:\phi.\delta \mid \delta \delta
\end{array}
\]

where $p$ is a \emph{proof variable} and $x$ is a \emph{term variable}.
Its rules of deduction are

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

\subsection{Extensional Equality}

On top of this system, we add an extensional equality relation.  We extend the grammar with

\[
\begin{array}{lrcl}
\text{Path} & P & ::= & e \mid \reff{M} \mid P \supset P \mid \univ{\phi}{\phi}{\delta}{\delta} \mid \triplelambda e : x =_A x . P \mid P P\\
\text{Proof} & \delta & ::= & \cdots \mid P^+ \mid P^- \\
\text{Context} & \Gamma & ::= & \cdots \mid \Gamma, e : M =_A M \\
\text{Judgement} & \mathcal{J} & ::= & \cdots \mid \Gamma \vdash P : M =_A M
\end{array}
\]

Note that, in the path $\triplelambda e : x =_A y . P$, the term variables $x$ and $y$ and the proof variable $e$ are all bound within $P$.

We add the following rules of deduction

\[ \infer{\Gamma, e : M =_A N \vald}{\Gamma \vdash M : A \quad \Gamma \vdash N : A}
\qquad
\infer[e : M =_A N \in \Gamma]{\Gamma \vdash e : M =_A N}{\Gamma \vald} \]

\[ \infer{\Gamma \vdash \reff{M} : M =_A M}{\Gamma \vdash M : A}
\qquad
\infer{\Gamma \vdash P \rightarrow Q : \phi \rightarrow \psi =_\Omega \phi' \rightarrow \psi´}{\Gamma \vdash P : \phi =_\Omega \phi´ \quad \Gamma \vdash Q : \psi =_\Omega \psi´} \]

\[ \infer{\Gamma \vdash \univ{\phi}{\psi}{\delta}{\epsilon} : \phi =_\Omega \psi}{\Gamma \vdash \delta : \phi \rightarrow \psi \quad \Gamma \vdash \epsilon : \psi \rightarrow \phi} 
\qquad
\infer{\Gamma \vdash P^+ : \phi \rightarrow \psi}{\Gamma \vdash P : \phi =_\Omega \psi}
\qquad
\infer{\Gamma \vdash P^- : \psi \rightarrow \phi}{\Gamma \vdash P : \psi =_\Omega \psi} \]

\[ \infer{\Gamma \vdash \triplelambda e : x =_A y . P : M =_{A \rightarrow B} N}{\Gamma, x : A, y : A, e : x =_A y \vdash M x =_B N y} \]

\[ \infer{\Gamma \vdash PQ : MN =_B M' N'}{\Gamma \vdash P : M =_{A \rightarrow B} M' \quad \Gamma \vdash Q : N =_A N'} \]

\[ \infer[(M \simeq_\beta M', N \simeq_\beta N')]{\Gamma \vdash P : M' =_A N'}{\Gamma \vdash P : M =_A N \quad \Gamma \vdash M' : A \quad \Gamma \vdash N' : A} \]

\AgdaHide{
\begin{code}
  data PHOPLcon : ∀ {K : ExpressionKind} → 
    Kind (-Constructor K) → Set where
    -ty : Type → PHOPLcon (out (nonVarKind -Type))
    -appProof : PHOPLcon (Π [] (varKind -Proof) 
      (Π [] (varKind -Proof) (out (varKind -Proof))))
    -lamProof : PHOPLcon (Π [] (varKind -Term) 
      (Π [ -Proof ] (varKind -Proof) (out (varKind -Proof))))
    -bot : PHOPLcon (out (varKind -Term))
    -imp : PHOPLcon (Π [] (varKind -Term) (Π [] (varKind -Term) (out (varKind -Term))))
    -appTerm : PHOPLcon (Π [] (varKind -Term) (Π [] (varKind -Term) (out (varKind -Term))))
    -lamTerm : Type → PHOPLcon (Π [ -Term ] (varKind -Term) (out (varKind -Term)))
    -ref : PHOPLcon (Π [] (varKind -Term) (out (varKind -Path)))
    -imp* : PHOPLcon (Π [] (varKind -Path) (Π [] (varKind -Path) (out (varKind -Path))))
    -univ : PHOPLcon (Π [] (varKind -Term) (Π [] (varKind -Term) (Π [] (varKind -Proof) (Π [] (varKind -Proof) (out (varKind -Path))))))
    -lll : Type → PHOPLcon (Π (-Term ∷ -Term ∷ [ -Path ]) (varKind -Path) (out (varKind -Path)))
    -app* : PHOPLcon (Π [] (varKind -Term) (Π [] (varKind -Term) (Π [] (varKind -Path) (Π [] (varKind -Path) (out (varKind -Path))))))
    -plus : PHOPLcon (Π [] (varKind -Path) (out (varKind -Proof)))
    -minus : PHOPLcon (Π [] (varKind -Path) (out (varKind -Proof)))
    -eq : Type → PHOPLcon (Π [] (varKind -Term) (Π [] (varKind -Term) (out (nonVarKind -Equation))))

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
                     sub↖ (ρ •RS σ) ∼ Rep↑ -Path (Rep↑ -Term (Rep↑ -Term ρ)) •RS sub↖ σ

sub↗ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (V , -Term , -Term , -Path)
sub↗ σ _ x₀ = var x₁
sub↗ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

postulate sub↗-cong : ∀ {U} {V} {ρ σ : Sub U V} → ρ ∼ σ → sub↗ ρ ∼ sub↗ σ

postulate sub↗-comp₁ : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
                     sub↗ (ρ •RS σ) ∼ Rep↑ -Path (Rep↑ -Term (Rep↑ -Term ρ)) •RS sub↗ σ

--REFACTOR Duplication
\end{code}
}
