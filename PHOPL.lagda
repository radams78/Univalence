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

Ω : ∀ {V} → Type V
Ω = app -Omega out

infix 75 _⇛_
_⇛_ : ∀ {V} → Type V → Type V → Type V
φ ⇛ ψ = app -func (φ ,,  ψ ,, out)

⊥ : ∀ {V} → Term V
⊥ = app -bot out

appT : ∀ {V} → Term V → Term V → Term V
appT M N = app -appTerm (M ,, N ,, out)

ΛT : ∀ {V} → Type V → Term (V , -Term) → Term V
ΛT A M = app -lamTerm (A ,,  M ,, out)

_⊃_ : ∀ {V} → Term V → Term V → Term V
φ ⊃ ψ = app -imp (φ ,, ψ ,, out)

appP : ∀ {V} → Proof V → Proof V → Proof V
appP δ ε = app -appProof (δ ,, ε ,, out)

ΛP : ∀ {V} → Term V → Proof (V , -Proof) → Proof V
ΛP φ δ = app -lamProof (φ ,, δ ,, out)

infix 60 _≡〈_〉_
_≡〈_〉_ : ∀ {V} → Term V → Type V → Term V → Equation V
M ≡〈 A 〉 N = app -eq (M ,, N ,, A ,, out)

λλλ : ∀ {V} → Type V → Path (V , -Term , -Term , -Path) → Path V
λλλ A P = app -lll (A ,, P ,, out)

--TODO Finish the list

close : ∀ {V} → Type V → Type ∅
close (app -Omega out) = Ω
close (app -func (A ,, B ,, out)) = close A ⇛ close B

_,P_ : ∀ {V} → Context V → Term V → Context (V , -Proof)
_,P_ = _,_

data β {V} : ∀ {K} {C : Kind (-Constructor K)} → 
  Constructor C → Body V C → Expression V K → Set where
  βI : ∀ {A} {M} {N} → β -appTerm (ΛT A M ,, N ,, out) (M ⟦ x₀:= N ⟧)
open import Reduction PHOPL β public
\end{code}

