\begin{code}
open import Function
open import Data.List
open import Prelims
open import Grammar.Taxonomy

module Grammar.Base where

record ToGrammar (T : Taxonomy) : Set₁ where
  open Taxonomy T
  field
    Constructor    : ∀ {K} → Kind (-Constructor K) → Set
    parent         : VarKind → ExpressionKind

  data Subexpression : Alphabet → ∀ C → Kind C → Set
  Expression : Alphabet → ExpressionKind → Set
  Body : Alphabet → ∀ {K} → Kind (-Constructor K) → Set

  Expression V K = Subexpression V -Expression (base K)
  Body V {K} C = Subexpression V (-Constructor K) C

  infixr 50 _,,_
  data Subexpression where
    var : ∀ {V} {K} → Var V K → Expression V (varKind K)
    app : ∀ {V} {K} {C} → Constructor C → Body V {K} C → Expression V K
    out : ∀ {V} {K} → Body V {K} out
    _,,_ : ∀ {V} {K} {A} {L} {C} → Expression (extend' V A) L → Body V {K} C → Body V (Π A L C)

  var-inj : ∀ {V} {K} {x y : Var V K} → var x ≡ var y → x ≡ y
  var-inj refl = refl

  record PreOpFamily : Set₂ where
    field
      Op : Alphabet → Alphabet → Set
      apV : ∀ {U} {V} {K} → Op U V → Var U K → Expression V (varKind K)
      up : ∀ {V} {K} → Op V (V , K)
      apV-up : ∀ {V} {K} {L} {x : Var V K} → apV (up {K = L}) x ≡ var (↑ x)
      idOp : ∀ V → Op V V
      apV-idOp : ∀ {V} {K} (x : Var V K) → apV (idOp V) x ≡ var x

    _∼op_ : ∀ {U} {V} → Op U V → Op U V → Set
    _∼op_ {U} {V} ρ σ = ∀ {K} (x : Var U K) → apV ρ x ≡ apV σ x
    
    ∼-refl : ∀ {U} {V} {σ : Op U V} → σ ∼op σ
    ∼-refl _ = refl
    
    ∼-sym : ∀ {U} {V} {σ τ : Op U V} → σ ∼op τ → τ ∼op σ
    ∼-sym σ-is-τ x = sym (σ-is-τ x)

    ∼-trans : ∀ {U} {V} {ρ σ τ : Op U V} → ρ ∼op σ → σ ∼op τ → ρ ∼op τ
    ∼-trans ρ-is-σ σ-is-τ x = trans (ρ-is-σ x) (σ-is-τ x)

    OP : Alphabet → Alphabet →  Setoid _ _
    OP U V = record { 
      Carrier = Op U V ; 
      _≈_ = _∼op_ ; 
      isEquivalence = record { 
        refl = ∼-refl ; 
        sym = ∼-sym ; 
        trans = ∼-trans } }

    record Lifting : Set₁ where
      field
        liftOp : ∀ {U} {V} K → Op U V → Op (U , K) (V , K)
        liftOp-cong : ∀ {V} {W} {K} {ρ σ : Op V W} → ρ ∼op σ → liftOp K ρ ∼op liftOp K σ
\end{code}

Given an operation $\sigma : U \rightarrow V$ and an abstraction kind $(x_1 : A_1 , \ldots , x_n : A_n) B$, define
the \emph{repeated lifting} $\sigma^A$ to be $((\cdots(\sigma , A_1) , A_2) , \cdots ) , A_n)$.

\begin{code}
      liftOp' : ∀ {U} {V} A → Op U V → Op (extend' U A) (extend' V A)
      liftOp' [] σ = σ
      liftOp' (K ∷ A) σ = liftOp' A (liftOp K σ)

      liftOp'-cong : ∀ {U} {V} A {ρ σ : Op U V} → ρ ∼op σ → liftOp' A ρ ∼op liftOp' A σ
      liftOp'-cong [] ρ-is-σ = ρ-is-σ
      liftOp'-cong (_ ∷ A) ρ-is-σ = liftOp'-cong A (liftOp-cong ρ-is-σ)

      ap : ∀ {U} {V} {C} {K} → Op U V → Subexpression U C K → Subexpression V C K
      ap ρ (var x) = apV ρ x
      ap ρ (app c EE) = app c (ap ρ EE)
      ap _ out = out
      ap ρ (_,,_ {A = A} {L = L} E EE) = _,,_ (ap (liftOp' A ρ) E) (ap ρ EE)

      ap-congl : ∀ {U} {V} {C} {K} {ρ σ : Op U V} (E : Subexpression U C K) →
        ρ ∼op σ → ap ρ E ≡ ap σ E
      ap-congl (var x) ρ-is-σ = ρ-is-σ x
      ap-congl (app c E) ρ-is-σ = cong (app c) (ap-congl E ρ-is-σ)
      ap-congl out _ = refl
      ap-congl (_,,_ {A = A} E F) ρ-is-σ = cong₂ _,,_ (ap-congl E (liftOp'-cong A ρ-is-σ)) (ap-congl F ρ-is-σ)

      ap-cong : ∀ {U} {V} {C} {K} {ρ σ : Op U V} {M N : Subexpression U C K} →
        ρ ∼op σ → M ≡ N → ap ρ M ≡ ap σ N
      ap-cong {ρ = ρ} {σ} {M} {N} ρ∼σ M≡N = let open ≡-Reasoning in 
        begin
          ap ρ M
        ≡⟨ ap-congl M ρ∼σ ⟩
          ap σ M
        ≡⟨ cong (ap σ) M≡N ⟩
          ap σ N
        ∎

record Grammar : Set₁ where
  field
    taxonomy : Taxonomy
    toGrammar : ToGrammar taxonomy
  open Taxonomy taxonomy public
  open ToGrammar toGrammar public
\end{code}
