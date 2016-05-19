\AgdaHide{
\begin{code}
module PHOPL where

open import Data.List
open import Data.Nat
open import Data.Fin
open import Prelims
open import Grammar.Taxonomy
open import Grammar.Base
\end{code}
}

\begin{frame}
\frametitle{Syntax}
The syntax of the system is given by the following grammar.

\[ \begin{array}{lrcl}
\text{Proof} & \delta & ::= & p \mid \delta \delta \mid \lambda p : \phi . \delta \\
\text{Term} & M, \phi & ::= & x \mid \bot \mid M M \mid \lambda x : A . M \mid \phi \supset \phi \\
\text{Type} & A & ::= & \Omega \mid A \rightarrow A \\
\end{array} \]
\end{frame}

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

  data PHOPLcon : ∀ {K : ExpressionKind} → Kind (-Constructor K) → Set where
    -appProof : PHOPLcon (Π [] (varKind -Proof) (Π [] (varKind -Proof) (out (varKind -Proof))))
    -lamProof : PHOPLcon (Π [] (varKind -Term) (Π [ -Proof ] (varKind -Proof) (out (varKind -Proof))))
    -bot : PHOPLcon (out (varKind -Term))
    -imp : PHOPLcon (Π [] (varKind -Term) (Π [] (varKind -Term) (out (varKind -Term))))
    -appTerm : PHOPLcon (Π [] (varKind -Term) (Π [] (varKind -Term) (out (varKind -Term))))
    -lamTerm : PHOPLcon (Π [] (nonVarKind -Type) (Π [ -Term ] (varKind -Term) (out (varKind -Term))))
    -Omega : PHOPLcon (out (nonVarKind -Type))
    -func  : PHOPLcon (Π [] (nonVarKind -Type) (Π [] (nonVarKind -Type) (out (nonVarKind -Type))))
    -ref : PHOPLcon (Π [] (varKind -Term) (out (varKind -Path)))
    -imp* : PHOPLcon (Π [] (varKind -Path) (Π [] (varKind -Path) (out (varKind -Path))))
    -univ : PHOPLcon (Π [] (varKind -Term) (Π [] (varKind -Term) (Π [] (varKind -Proof) (Π [] (varKind -Proof) (out (varKind -Path))))))
    -lll : PHOPLcon (Π [] (nonVarKind -Type) (Π (-Term ∷ -Term ∷ [ -Path ]) (varKind -Path) (out (varKind -Path))))
    -app* : PHOPLcon (Π [] (varKind -Term) (Π [] (varKind -Term) (Π [] (varKind -Path) (Π [] (varKind -Path) (out (varKind -Path))))))
    -eq   : PHOPLcon (Π [] (varKind -Term) (Π [] (varKind -Term) (Π [] (nonVarKind -Type)
      (out (nonVarKind -Equation)))))
    -plus : PHOPLcon (Π [] (varKind -Path) (out (varKind -Proof)))
    -minus : PHOPLcon (Π [] (varKind -Path) (out (varKind -Proof)))

  PHOPLparent : PHOPLVarKind → ExpressionKind
  PHOPLparent -Proof = varKind -Term
  PHOPLparent -Term = nonVarKind -Type
  PHOPLparent -Poth = nonVarKind -Equation

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

Type : Alphabet → Set
Type V = Expression V (nonVarKind -Type)

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

ΛT : ∀ {V} → Type V → Term (V , -Term) → Term V
ΛT A M = app -lamTerm (A ,,  M ,, out)

Ω : ∀ {V} → Type V
Ω = app -Omega out

infix 75 _⇛_
_⇛_ : ∀ {V} → Type V → Type V → Type V
φ ⇛ ψ = app -func (φ ,,  ψ ,, out)

reff : ∀ {V} → Term V → Path V
reff M = app -ref (M ,, out)

infix 15 _⊃*_
_⊃*_ : ∀ {V} → Path V → Path V → Path V
P ⊃* Q = app -imp* (P ,, Q ,, out)

univ : ∀ {V} → Term V → Term V → Proof V → Proof V → Path V
univ φ ψ P Q = app -univ (φ ,, ψ ,, P ,, Q ,, out)

λλλ : ∀ {V} → Type V → Path (V , -Term , -Term , -Path) → Path V
λλλ A P = app -lll (A ,, P ,, out)

app* : ∀ {V} → Term V → Term V → Path V → Path V → Path V
app* M N P Q = app -app* (M ,, N ,, P ,, Q ,, out)

infix 60 _≡〈_〉_
_≡〈_〉_ : ∀ {V} → Term V → Type V → Term V → Equation V
M ≡〈 A 〉 N = app -eq (M ,, N ,, A ,, out)

plus : ∀ {V} → Path V → Proof V
plus P = app -plus (P ,, out)

minus : ∀ {V} → Path V → Proof V
minus P = app -minus (P ,, out)

infixl 20 _,T_
_,T_ : ∀ {V} → Context V → Type V → Context (V , -Term)
_,T_ = _,_

infixl 20 _,P_
_,P_ : ∀ {V} → Context V → Term V → Context (V , -Proof)
_,P_ = _,_

infixl 20 _,E_
_,E_ : ∀ {V} → Context V → Equation V → Context (V , -Path)
_,E_ = _,_

data β {V} : ∀ {K} {C : Kind (-Constructor K)} → 
  Constructor C → Body V C → Expression V K → Set where
  βI : ∀ {A} {M} {N} → β -appTerm (ΛT A M ,, N ,, out) (M ⟦ x₀:= N ⟧)
open import Reduction.Base PHOPL β public

APP : ∀ {V} → Term V → List (Term V) → Term V
APP M [] = M
APP M (N ∷ NN) = APP (appT M N) NN
\end{code}