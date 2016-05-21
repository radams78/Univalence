\AgdaHide{
\begin{code}
module PHOPL.Grammar where

open import Data.List
open import Data.Nat
open import Data.Fin
open import Prelims
open import Grammar.Taxonomy
open import Grammar.Base
\end{code}
}

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

  data PHOPLcon : ∀ {K : ExpressionKind} → Kind (-Constructor K) → Set where
    -ty : Type → PHOPLcon (out (nonVarKind -Type))
    -appProof : PHOPLcon (Π [] (varKind -Proof) (Π [] (varKind -Proof) (out (varKind -Proof))))
    -lamProof : PHOPLcon (Π [] (varKind -Term) (Π [ -Proof ] (varKind -Proof) (out (varKind -Proof))))
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

data β {V} : ∀ {K} {C : Kind (-Constructor K)} → 
     Constructor C → Body V C → Expression V K → Set where
     βI : ∀ {A} {M} {N} → β -appTerm (ΛT A M ,, N ,, out) (M ⟦ x₀:= N ⟧)
open import Reduction.Base PHOPL β public

APP : ∀ {V} → Term V → List (Term V) → Term V
APP M [] = M
APP M (N ∷ NN) = APP (appT M N) NN
--REFACTOR Remove this?

addpath : ∀ {V} → Context V → Type → Context (V , -Term , -Term , -Path)
addpath Γ A = Γ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀

postulate eq-resp-conv : ∀ {V} {M M' N N' : Term V} {A : Type} →
                       M ≃ M' → N ≃ N' → M ≡〈 A 〉 N ≃ M' ≡〈 A 〉 N'
\end{code}
