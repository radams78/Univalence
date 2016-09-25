\AgdaHide{
\begin{code}
{- Metavariable conventions:
  A, B    range over abstraction kinds
  C       range over kind classes
  AA, BB  range over lists of abstraction kinds
  E, F, G range over subexpressions
  K, L    range over expression kinds including variable kinds
  M, N, P range over expressions
  U, V, W range over alphabets -}
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
  ListAbs : Alphabet → List AbsKind → Set

  Expression V K = Subexpression V -Expression K
  VExpression V K = Expression V (varKind K)
  Abstraction V (SK AA K) = Expression (extend V AA) K
  ListAbs V AA = Subexpression V -ListAbs AA

  infixr 5 _∷_
  data Subexpression V where
    var : ∀ {K} → Var V K → VExpression V K
    app : ∀ {AA} {K} → Constructor (SK AA K) → ListAbs V AA → Expression V K
    [] : ListAbs V []
    _∷_ : ∀ {A} {AA} → Abstraction V A → ListAbs V AA → ListAbs V (A ∷ AA)
\end{code}
%</Expression>

We prove that the constructor \AgdaRef{var} is injective.

\begin{code}
  var-inj : ∀ {V} {K} {x y : Var V K} → var x ≡ var y → x ≡ y
  var-inj refl = refl
\end{code}

For the future, we also define the type of all snoc-lists of expressions $(M_1, \ldots, M_n)$
such that $M_i$ is of type $K_i$, given a snoc-list of variable kinds $(K_1, \ldots, K_n)$.

\begin{code}
  infixl 20 _snoc_
  data snocListExp V : snocList VarKind → Set where
    [] : snocListExp V []
    _snoc_ : ∀ {A} {K} → snocListExp V A → Expression V (varKind K) → snocListExp V (A snoc K)
\end{code}

A \emph{reduction} is a relation $\rhd$ between expressions such that, if $E \rhd F$,
then $E$ is not a variable.  It is given by a term $R : \AgdaRef{Reduction}$ such that
$R\, c\, MM\, N$ iff $c[MM] \rhd N$.

\begin{code}
  Reduction : Set₁
  Reduction = ∀ {V} {AA} {K} → Constructor (SK AA K) → ListAbs V AA → Expression V K → Set
\end{code}
}
