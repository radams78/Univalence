\AgdaHide{
\begin{code}
open import Function
open import Data.List
open import Prelims
open import Grammar.Taxonomy

module Grammar.Base where
\end{code}
}

\begin{code}
record IsGrammar (T : Taxonomy) : Set₁ where
  open Taxonomy T
  field
    Constructor    : ∀ {K} → ConstructorKind K → Set
    parent         : VarKind → ExpressionKind
\end{code}

\AgdaHide{
\begin{code}
record Grammar : Set₁ where
  field
    taxonomy : Taxonomy
    isGrammar : IsGrammar taxonomy
  open Taxonomy taxonomy public
  open IsGrammar isGrammar public
\end{code}
}

We can now define the set of expressions over a grammar:

\begin{code}
  data Subexpression : Alphabet → ∀ C → Kind C → Set
  Expression : Alphabet → ExpressionKind → Set
  VExpression : Alphabet → VarKind → Set
  dom : Alphabet → ∀ {K} → AbstractionKind K → Alphabet
  Abstraction : Alphabet → ∀ {K} → AbstractionKind K → Set
  Body : Alphabet → ∀ {K} → ConstructorKind K → Set

  Expression V K = Subexpression V -Expression K
  VExpression V K = Expression V (varKind K)
  dom V (K ✧) = V
  dom V (K abs A) = dom (V , K) A
  Abstraction V {K} A = Expression (dom V A) K
  Body V {K} C = Subexpression V (-Constructor K) C

  infixr 50 _,,_
  data Subexpression where
    var : ∀ {V} {K} → Var V K → VExpression V K
    app : ∀ {V} {K} {C} → Constructor C → Body V {K} C → Expression V K
    out : ∀ {V} {K} → Body V (K ●)
    _,,_ : ∀ {V} {L} {A} {K} {C} → Abstraction V {L} A → Body V {K} C → Body V (A ⟶ C)
\end{code}

\AgdaHide{
\begin{code}
  var-inj : ∀ {V} {K} {x y : Var V K} → var x ≡ var y → x ≡ y
  var-inj refl = refl

  Reduction : Set₁
  Reduction = ∀ {V} {K} {C} → 
    Constructor C → Body V {K} C → Expression V K → Set
--TODO Delete
\end{code}
}
