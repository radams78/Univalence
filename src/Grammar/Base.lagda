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
    Constructor    : ConKind → Set
    parent         : VarKind → ExpKind

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
  data Subexpression (V : Alphabet) : ∀ C → Kind C → Set
  Expression : Alphabet → ExpKind → Set
  VExpression : Alphabet → VarKind → Set
  Abstraction : Alphabet → AbsKind → Set
  Body : Alphabet → List AbsKind → Set

  Expression V K = Subexpression V -Expression K
  VExpression V K = Expression V (varKind K)
  Abstraction V (SK VV K) = Expression (extend V VV) K
  Body V AA = Subexpression V -ListAbs AA

  infixr 5 _∷_
  data Subexpression V where
    var : ∀ {K} → Var V K → VExpression V K
    app : ∀ {AA} {K} → Constructor (SK AA K) → Body V AA → Expression V K
    [] : Body V []
    _∷_ : ∀ {A} {AA} → Abstraction V A → Body V AA → Body V (A ∷ AA)
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
  Reduction = ∀ {V} {AA} {K} → Constructor (SK AA K) → Body V AA → Expression V K → Set
\end{code}
}
