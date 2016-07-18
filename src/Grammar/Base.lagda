\AgdaHide{
\begin{code}
open import Function
open import Data.List
open import Prelims
open import Grammar.Taxonomy

module Grammar.Base where

record IsGrammar (T : Taxonomy) : Set₁ where
  open Taxonomy T
  field
    Constructor    : ∀ {K} → ConstructorKind K → Set
    parent         : VarKind → ExpressionKind

record Grammar : Set₁ where
  field
    taxonomy : Taxonomy
    isGrammar : IsGrammar taxonomy
  open Taxonomy taxonomy public
  open IsGrammar isGrammar public
\end{code}
}

%<*Expression>
\begin{code}
  data Subexpression : Alphabet → ∀ C → Kind C → Set
  Expression : Alphabet → ExpressionKind → Set
  VExpression : Alphabet → VarKind → Set
  dom : Alphabet → AbstractionKind' → Alphabet
  cod : AbstractionKind' → ExpressionKind
  Abstraction : Alphabet → AbstractionKind' → Set
  Body : Alphabet → ∀ {K} → ConstructorKind K → Set

  Expression V K = Subexpression V -Expression (base K)
  VExpression V K = Expression V (varKind K)
  dom V (Π _ (_ ●)) = V
  dom V (Π _ (K ⟶ A)) = dom (V , K) (Π _ A)
  cod (Π _ (K ●)) = K
  cod (Π _ (_ ⟶ A)) = cod (Π _ A)
  Abstraction V A = Expression (dom V A) (cod A)
  Body V {K} C = Subexpression V (-Constructor K) C

  infixr 50 _,,_
  data Subexpression where
    var : ∀ {V} {K} → Var V K → VExpression V K
    app : ∀ {V} {K} {C} → Constructor C → Body V {K} C → 
      Expression V K

    out : ∀ {V} {K} → Body V (out K)
    _,,_ : ∀ {V} {K} {A} {C} → Abstraction V A → Body V {K} C → Body V (Π A C)
\end{code}
%</Expression>


\AgdaHide{
\begin{code}
  var-inj : ∀ {V} {K} {x y : Var V K} → var x ≡ var y → x ≡ y
  var-inj refl = refl

  infixl 20 _snoc_
  data ExpList V : snocList VarKind → Set where
    [] : ExpList V []
    _snoc_ : ∀ {A} {K} → ExpList V A → Expression V (varKind K) → ExpList V (A snoc K)

  Reduction : Set₁
  Reduction = ∀ {V} {K} {C : Kind (-Constructor K)} → 
    Constructor C → Body V C → Expression V K → Set
\end{code}
}
