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

\section{Predicative Higher-Order Propositional Logic}

Fix sets of \emph{proof variables} and \emph{term variables}.

The syntax of the system is given by the following grammar.

%Changes from Marc and Thierry's system:
%Taken out the proof c of \bot
\[ \begin{array}{lrcl}
\text{Proof} & \delta & ::= & p \mid \delta \delta \mid \lambda p : \phi . \delta \\
\text{Term} & M, \phi & ::= & x \mid \bot \mid M M \mid \lambda x : A . M \mid \phi \rightarrow \phi \\
\text{Type} & A & ::= & \Omega \mid A \rightarrow A \\
\end{array} \]

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

  PHOPLparent : PHOPLVarKind → ExpressionKind
  PHOPLparent -Proof = varKind -Term
  PHOPLparent -Term = nonVarKind -Type

  PHOPL : Grammar
  PHOPL = record { 
    taxonomy = PHOPLTaxonomy;
    isGrammar = record { 
      Constructor = PHOPLcon; 
      parent = PHOPLparent } }

open PHOPLgrammar public
open import Grammar PHOPL public

Type : Set
Type = Expression ∅ (nonVarKind -Type)

liftType : ∀ {V} → Type → Expression V (nonVarKind -Type)
liftType (app -Omega out) = app -Omega out
liftType (app -func (A ,, B ,, out)) = app -func (liftType A ,, liftType B ,, out) 

Ω : Type
Ω = app -Omega out

infix 75 _⊃_
_⇛_ : Type → Type → Type
φ ⇛ ψ = app -func (φ ,,  ψ ,, out)

lowerType : ∀ {V} → Expression V (nonVarKind -Type) → Type
lowerType (app -Omega ou) = Ω
lowerType (app -func (φ ,, ψ ,, out)) = lowerType φ ⇛ lowerType ψ

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

Proof : Alphabet → ℕ → Set
Proof V P = Expression (PAlphabet P V) (varKind -Proof)

varP : ∀ {V} {P} → Fin P → Proof V P
varP {P = P} x = var (liftVar' P x)

appP : ∀ {V} {P} → Proof V P → Proof V P → Proof V P
appP δ ε = app -appProof (δ ,, ε ,, out)

ΛP : ∀ {V} {P} → Term V → Proof V (suc P) → Proof V P
ΛP {P = P} φ δ = app -lamProof (liftExp P φ ,, δ ,, out)

propof : ∀ {V} {P} → Fin P → PContext' V P → Term V
propof zero (_ , φ) = φ
propof (suc x) (Γ , _) = propof x Γ

data β : ∀ {V} {K} {C} → Constructor C → Subexpression V (-Constructor K) C → Expression V K → Set where
  βI : ∀ {V} A (M : Term (V , -Term)) N → β -appTerm (ΛTerm A M ,, N ,, out) (M ⟦ x₀:= N ⟧)
open import Reduction PHOPL β public
\end{code}
