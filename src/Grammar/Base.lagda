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
    Constructor    : PiExp AbstractionKind ExpressionKind → Set
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
{-  data Subexpression : Alphabet VarKind → ∀ C → Kind C → Set
  Expression : Alphabet VarKind → ExpressionKind → Set
  VExpression : Alphabet VarKind → VarKind → Set
  Abstraction : Alphabet VarKind → AbstractionKind → Set
  Body : Alphabet VarKind → List AbstractionKind → Set

  Expression V K = Subexpression V -Expression K
  VExpression V K = Expression V (varKind K)
  Abstraction V (AA ⟶ K) = Expression (extend V AA) K
  Body V AA = Subexpression V -Constructor AA

  infixr 50 _,,_
  data Subexpression where
    var : ∀ {V} {K} → Var V K → VExpression V K
    app : ∀ {V} {AA} {K} → Constructor (AA ⟶ K) → Body V AA → Expression V K
    out : ∀ {V} → Body V []
    _,,_ : ∀ {V} {A} {AA} → Abstraction V A → Body V AA → Body V (A ∷ AA) -}
\end{code}
%</Expression>


\AgdaHide{
\begin{code}
  VK2AK : VarKind → AbstractionKind
  VK2AK x = [] ⟶ varKind x

  liftAlphabet : Alphabet VarKind → Alphabet AbstractionKind
  liftAlphabet ∅ = ∅
  liftAlphabet (V , A) = liftAlphabet V , VK2AK A

  liftVar : ∀ {V K} → Var V K → Var (liftAlphabet V) (VK2AK K)
  liftVar x₀ = x₀
  liftVar (↑ x) = ↑ (liftVar x)

  lowerVar : ∀ {V K} → Var (liftAlphabet V) (VK2AK K) → Var V K
  lowerVar {∅} ()
  lowerVar {_ , _} x₀ = x₀
  lowerVar {_ , _} (↑ x) = ↑ (lowerVar x)

  ↑-inj : ∀ {S} {V : Alphabet S} {K} {L} {x y : Var V L} → ↑ {A = S} {K = K} {L = L} x ≡ ↑ y → x ≡ y
  ↑-inj refl = refl

  liftVar-inj : ∀ {V} {K} {x y : Var V K} → liftVar x ≡ liftVar y → x ≡ y
  liftVar-inj {x = x₀} {x₀} x = refl
  liftVar-inj {x = x₀} {↑ y} ()
  liftVar-inj {x = ↑ x} {x₀} ()
  liftVar-inj {x = ↑ x} {↑ y} x₁ = cong ↑ (liftVar-inj (↑-inj x₁))

  data Subexpressionn A : Alphabet (AKind A) → ∀ C → Kind C → Set where
    var : ∀ {V} {AA} {K} → Var V (AA ⟶ K) → Subexpressionn A V (-List A) AA → Subexpressionn A V -Expression (toExp K)

  data Subexpression2 : Alphabet AbstractionKind → ∀ C → Kind C → Set where
    var2 : ∀ {V} {AA} {K} → Var V (AA ⟶ K) → Subexpression2 V -Abstraction AA → Subexpression2 V -Expression K
    app : ∀ {V} {AA} {K} → Constructor (AA ⟶ K) → Subexpression2 V -Constructor AA → Subexpression2 V -Expression K
    []1 : ∀ {V} → Subexpression2 V -Abstraction []
    _∷1_ : ∀ {V} {K} {AA} → Subexpression2 V -Expression (varKind K) → Subexpression2 V -Abstraction (K ∷ AA)
    []  : ∀ {V} → Subexpression2 V -Constructor []
    _∷_ : ∀ {V} {BB} {K} {AA} → Subexpression2 (extend V (map VK2AK BB)) -Expression K → Subexpression2 V -Constructor AA → 
      Subexpression2 V -Constructor (BB ⟶ K ∷ AA)

{-  var2-inj : ∀ {V} {AA} {K} {x y : Var V (AA ⟶ K)} {EE} {FF} → var2 x EE ≡ var2 y FF → x ≡ y
  var2-inj refl = refl

  Subexpression V = Subexpression2 (liftAlphabet V)

  Expression : Alphabet VarKind → ExpressionKind → Set
  Expression V K = Subexpression V -Expression K

  VExpression : Alphabet VarKind → VarKind → Set
  VExpression V K = Expression V (varKind K)

  var : ∀ {K} {V : Alphabet VarKind} → Var V K → VExpression V K
  var x = var2 (liftVar x) []

  var-inj : ∀ {V} {K} {x y : Var V K} → var x ≡ var y → x ≡ y
  var-inj δ = liftVar-inj (var2-inj δ)

  Abstraction : Alphabet VarKind → AbstractionKind → Set
  Abstraction V (AA ⟶ K) = Expression (extend V AA) K

  Body : Alphabet VarKind → List AbstractionKind → Set
  Body V AA = Subexpression V -Constructor AA

  infixl 20 _snoc_
  data ExpList V : Alphabet VarKind → Set where
    [] : ExpList V ∅
    _snoc_ : ∀ {A} {K} → ExpList V A → Expression V (varKind K) → ExpList V (A , K)

  Reduction : Set₁
  Reduction = ∀ {V} {AA} {K} → Constructor (AA ⟶ K) → Body V AA → Expression V K → Set -}
--TODO Delete
\end{code}
}
