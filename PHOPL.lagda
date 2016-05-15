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
    -app* : PHOPLcon (Π [] (varKind -Path) (Π [] (varKind -Path) (out (varKind -Path))))
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

Type : Alphabet → Set
Type V = Expression V (nonVarKind -Type)

Ω : ∀ {V} → Type V
Ω = app -Omega out

infix 75 _⇛_
_⇛_ : ∀ {V} → Type V → Type V → Type V
φ ⇛ ψ = app -func (φ ,,  ψ ,, out)

lowerType : ∀ {V} → Type V → Type ∅
lowerType (app -Omega ou) = Ω
lowerType (app -func (φ ,, ψ ,, out)) = lowerType φ ⇛ lowerType ψ

Term : Alphabet → Set
Term V = Expression V (varKind -Term)

⊥ : ∀ {V} → Term V
⊥ = app -bot out

appTerm : ∀ {V} → Term V → Term V → Term V
appTerm M N = app -appTerm (M ,, N ,, out)

ΛTerm : ∀ {V} → Type V → Term (V , -Term) → Term V
ΛTerm A M = app -lamTerm (A ,,  M ,, out)

_⊃_ : ∀ {V} → Term V → Term V → Term V
φ ⊃ ψ = app -imp (φ ,, ψ ,, out)

Proof : Alphabet → Set
Proof V = Expression V (varKind -Proof)

appP : ∀ {V} → Proof V → Proof V → Proof V
appP δ ε = app -appProof (δ ,, ε ,, out)

ΛP : ∀ {V} → Term V → Proof (V , -Proof) → Proof V
ΛP φ δ = app -lamProof (φ ,, δ ,, out)

_,P_ : ∀ {V} → Context V → Term V → Context (V , -Proof)
_,P_ = _,_

data β : ∀ {V} {K} {C} → Constructor C → Subexpression V (-Constructor K) C → Expression V K → Set where
  βI : ∀ {V} A (M : Term (V , -Term)) N → β -appTerm (ΛTerm A M ,, N ,, out) (M ⟦ x₀:= N ⟧)
open import Reduction PHOPL β public
\end{code}

