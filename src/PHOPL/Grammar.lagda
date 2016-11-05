\AgdaHide{
\begin{code}
module PHOPL.Grammar where

open import Data.Nat
open import Data.Empty renaming (⊥ to Empty)
open import Data.List hiding (replicate)
open import Data.Vec hiding (replicate)
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

  data Dir : Set where
    -plus : Dir
    -minus : Dir

  pathDom : List VarKind
  pathDom = -Term ∷ -Term ∷ -Path ∷ []

  data PHOPLcon : ConKind → Set where
    -ty : Type → PHOPLcon (-nvType ✧)
    -bot : PHOPLcon (-vTerm ✧)
    -imp : PHOPLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -vTerm ✧)
    -lamTerm : Type → PHOPLcon ((-Term ⟶ -vTerm ✧) ⟶ -vTerm ✧)
    -appTerm : PHOPLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -vTerm ✧)
    -lamProof : PHOPLcon (-vTerm ✧ ⟶ (-Proof ⟶ -vProof ✧) ⟶ -vProof ✧)
    -appProof : PHOPLcon (-vProof ✧ ⟶ -vProof ✧ ⟶ -vProof ✧)
    -dir : Dir → PHOPLcon (-vPath ✧ ⟶ -vProof ✧)
    -ref : PHOPLcon (-vTerm ✧ ⟶ -vPath ✧)
    -imp* : PHOPLcon (-vPath ✧ ⟶ -vPath ✧ ⟶ -vPath ✧)
    -univ : PHOPLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -vProof ✧ ⟶ -vProof ✧ ⟶ -vPath ✧)
    -lll : Type → PHOPLcon (SK pathDom -vPath ⟶ -vPath ✧)
    -app* : PHOPLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -vPath ✧ ⟶ -vPath ✧ ⟶ -vPath ✧)
    -eq : Type → PHOPLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -nvEq ✧)

  PHOPLparent : PHOPLVarKind → ExpKind
  PHOPLparent -Proof = -vTerm
  PHOPLparent -Term = -nvType
  PHOPLparent -Path = -nvEq

  PHOPL : Grammar
  PHOPL = record { 
    taxonomy = PHOPLTaxonomy;
    isGrammar = record { 
      Con = PHOPLcon; 
      parent = PHOPLparent } }
\end{code}

\AgdaHide{
\begin{code}
open PHOPLgrammar public
open import Grammar PHOPL public
\end{code}
}

\begin{code}
Proof : Alphabet → Set
Proof V = Expression V -vProof

Term : Alphabet → Set
Term V = Expression V -vTerm

Path : Alphabet → Set
Path V = Expression V -vPath

Equation : Alphabet → Set
Equation V = Expression V -nvEq

ty : ∀ {V} → Type → Expression V (nonVarKind -Type)
ty A = app (-ty A) []

⊥ : ∀ {V} → Term V
⊥ = app -bot []

infix 65 _⊃_
_⊃_ : ∀ {V} → Term V → Term V → Term V
φ ⊃ ψ = app -imp (φ ∷ ψ ∷ [])

ΛT : ∀ {V} → Type → Term (V , -Term) → Term V
ΛT A M = app (-lamTerm A) (M ∷ [])

appT : ∀ {V} → Term V → Term V → Term V
appT M N = app -appTerm (M ∷ N ∷ [])

ΛP : ∀ {V} → Term V → Proof (V , -Proof) → Proof V
ΛP φ δ = app -lamProof (φ ∷ δ ∷ [])

appP : ∀ {V} → Proof V → Proof V → Proof V
appP δ ε = app -appProof (δ ∷ ε ∷ [])

dir : ∀ {V} → Dir → Path V → Proof V
dir d P = app (-dir d) (P ∷ [])

plus : ∀ {V} → Path V → Proof V
plus P = dir -plus P

minus : ∀ {V} → Path V → Proof V
minus P = dir -minus P

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
yt : ∀ {V} → Expression V (nonVarKind -Type) → Type
yt (app (-ty A) []) = A

typeof' : ∀ {V} → Var V -Term → Context V → Type
typeof' x Γ  = yt (typeof x Γ)

⊃-injl : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ≡ φ' ⊃ ψ' → φ ≡ φ'
⊃-injl refl = refl

⊃-injr : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ≡ φ' ⊃ ψ' → ψ ≡ ψ'
⊃-injr refl = refl

appT-injl : ∀ {V} {M M' N N' : Term V} → appT M N ≡ appT M' N' → M ≡ M'
appT-injl refl = refl

appT-injr : ∀ {V} {M N P Q : Term V} → appT M N ≡ appT P Q → N ≡ Q
appT-injr refl = refl
\end{code}
}

We define the operation which, given a vector of $n$ types $A_1$, \ldots, $A_n$ and a type $B$, forms the type $A_1 \rightarrow \cdots \rightarrow A_n \rightarrow B$.  Likewise we define operations for applying a vector of terms, and a vector of proofs.

\begin{code}
Pi : ∀ {n} → snocVec Type n → Type → Type
Pi [] B = B
Pi (AA snoc A) B = Pi AA (A ⇛ B)

APP : ∀ {V n} → Term V → snocVec (Term V) n → Term V
APP M [] = M
APP M (NN snoc N) = appT (APP M NN) N
\end{code}

\AgdaHide{
\begin{code}
APP-rep : ∀ {U V n M} (NN : snocVec (Term U) n) {ρ : Rep U V} →
  (APP M NN) 〈 ρ 〉 ≡ APP (M 〈 ρ 〉) (snocVec-rep NN ρ)
APP-rep [] = refl
APP-rep (NN snoc N) {ρ} = cong (λ x → appT x (N 〈 ρ 〉)) (APP-rep NN)
\end{code}
}

\begin{code}
APPP : ∀ {V} {n} → Proof V → snocVec (Proof V) n → Proof V
APPP δ [] = δ
APPP δ (εε snoc ε) = appP (APPP δ εε) ε
\end{code}

\AgdaHide{
\begin{code}
APPP-rep : ∀ {U V n δ} (εε : snocVec (Proof U) n) {ρ : Rep U V} →
  (APPP δ εε) 〈 ρ 〉 ≡ APPP (δ 〈 ρ 〉) (snocVec-rep εε ρ)
APPP-rep [] = refl
APPP-rep (εε snoc ε) {ρ} = cong (λ x → appP x (ε 〈 ρ 〉)) (APPP-rep εε)
\end{code}
}

\begin{code}
APPP' : ∀ {V} → Proof V → List (Proof V) → Proof V
APPP' δ [] = δ
APPP' δ (ε ∷ εε) = APPP' (appP δ ε) εε

APP* : ∀ {V n} → snocVec (Term V) n → snocVec (Term V) n → Path V → snocVec (Path V) n → Path V
APP* [] [] P [] = P
APP* (MM snoc M) (NN snoc N) P (QQ snoc Q) = app* M N (APP* MM NN P QQ) Q
\end{code}

\AgdaHide{
\begin{code}
APP*-rep : ∀ {U V n} MM {NN : snocVec (Term U) n} {P QQ} {ρ : Rep U V} →
  (APP* MM NN P QQ) 〈 ρ 〉 ≡ APP* (snocVec-rep MM ρ) (snocVec-rep NN ρ) (P 〈 ρ 〉) (snocVec-rep QQ ρ)
APP*-rep [] {[]} {QQ = []} = refl
APP*-rep (MM snoc M) {NN snoc N} {QQ = QQ snoc Q} {ρ = ρ} = 
  cong (λ x → app* (M 〈 ρ 〉) (N 〈 ρ 〉) x (Q 〈 ρ 〉)) (APP*-rep MM)
\end{code}
}

We define the context\AgdaKeyword{addpath} \, $\Gamma$ \, $A$ to be $\Gamma, x : A, y : A, e : x =_A y$.

\begin{code}
addpath : ∀ {V} → Context V → Type → Context (V , -Term , -Term , -Path)
addpath Γ A = Γ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀
\end{code}

Given a substitution $\sigma : U \rightarrow V$, we introduce abbreviations for the substitutions $(\sigma, z := x)$ and $(\sigma , z := y) : U \cup \{ z \} \rightarrow V \cup \{ x , y , e \}$.

\begin{code}
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

toSnocTypes : ∀ {V n} → snocVec Type n → snocTypes V (replicate n -Term)
toSnocTypes [] = []
toSnocTypes (AA snoc A) = toSnocTypes AA snoc ty A

toSnocTypes-rep : ∀ {U V n} {AA : snocVec Type n} {ρ : Rep U V} → snocTypes-rep (toSnocTypes AA) ρ ≡ toSnocTypes AA
toSnocTypes-rep {AA = []} = refl
toSnocTypes-rep {AA = AA snoc A} = cong (λ x → x snoc ty A) toSnocTypes-rep

eqmult : ∀ {V n} → snocVec (Term V) n → snocVec Type n → snocVec (Term V) n → snocTypes V (Prelims.replicate n -Path)
eqmult [] [] [] = []
eqmult {n = suc n} (MM snoc M) (AA snoc A) (NN snoc N) = eqmult MM AA NN snoc (_⇑⇑ {KK = Prelims.replicate n -Path} M) ≡〈 A 〉 (_⇑⇑ {KK = Prelims.replicate n -Path} N)

eqmult-rep : ∀ {U V n} {MM : snocVec (Term U) n} {AA NN} {ρ : Rep U V} →
  snocTypes-rep (eqmult MM AA NN) ρ ≡ eqmult (snocVec-rep MM ρ) AA (snocVec-rep NN ρ)
eqmult-rep {MM = []} {[]} {[]} = refl
eqmult-rep {n = suc n} {MM = MM snoc M} {AA snoc A} {NN snoc N} = cong₃ (λ a b c → a snoc b ≡〈 A 〉 c) 
  eqmult-rep 
  (liftsnocRep-ups (Prelims.replicate n -Path) M) (liftsnocRep-ups (Prelims.replicate n -Path) N)

toSnocListExp : ∀ {V K n} → snocVec (Expression V (varKind K)) n → snocListExp V (replicate n K)
toSnocListExp [] = []
toSnocListExp (MM snoc M) = toSnocListExp MM snoc M

toSnocListExp-rep : ∀ {U V K n} {MM : snocVec (Expression U (varKind K)) n} {ρ : Rep U V} →
  snocListExp-rep (toSnocListExp MM) ρ ≡ toSnocListExp (snocVec-rep MM ρ)
toSnocListExp-rep {MM = []} = refl
toSnocListExp-rep {MM = MM snoc M} {ρ} = cong (λ x → x snoc M 〈 ρ 〉) toSnocListExp-rep
\end{code}
}
