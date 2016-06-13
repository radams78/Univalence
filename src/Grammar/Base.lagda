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
    Constructor    : ∀ {K} → Kind (-Constructor K) → Set
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
  Body : Alphabet → ∀ {K} → Kind (-Constructor K) → Set

  Expression V K = Subexpression V -Expression (base K)
  Body V {K} C = Subexpression V (-Constructor K) C

  infixr 50 _,,_
  data Subexpression where
    var : ∀ {V} {K} → Var V K → Expression V (varKind K)
    app : ∀ {V} {K} {C} → Constructor C → Body V {K} C → 
      Expression V K

    out : ∀ {V} {K} → Body V (out K)
    _,,_ : ∀ {V} {K} {A} {L} {C} → Expression (extend V A) L → 
      Body V {K} C → Body V (Π A L C)
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
