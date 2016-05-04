\begin{code}
module Grammar where

open import Function
open import Data.List
open import Prelims
open import Taxonomy

record ToGrammar (T : Taxonomy) : Set₁ where
  open Taxonomy.Taxonomy T
  field
    Constructor    : ∀ {K} → Kind' (-Constructor K) → Set
    parent         : VarKind → ExpressionKind

  data Subexpression : Alphabet → ∀ C → Kind' C → Set
  Expression : Alphabet → ExpressionKind → Set
  Body : Alphabet → ∀ {K} → Kind' (-Constructor K) → Set

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
--TODO Refactor to deal with sequences of kinds instead of abstraction kinds?

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

        record IsLiftFamily : Set₁ where
          field
            liftOp-x₀ : ∀ {U} {V} {K} {σ : Op U V} → apV (liftOp K σ) x₀ ≡ var x₀
            liftOp-↑ : ∀ {U} {V} {K} {L} {σ : Op U V} (x : Var U L) →
              apV (liftOp K σ) (↑ x) ≡ ap up (apV σ x)

          liftOp-idOp : ∀ {V} {K} → liftOp K (idOp V) ∼op idOp (V , K)
          liftOp-idOp {V} {K} x₀ = let open ≡-Reasoning in
            begin
              apV (liftOp K (idOp V)) x₀
            ≡⟨ liftOp-x₀ ⟩
              var x₀
            ≡⟨⟨ apV-idOp x₀ ⟩⟩
              apV (idOp (V , K)) x₀
            ∎
          liftOp-idOp {V} {K} {L} (↑ x) = let open ≡-Reasoning in 
            begin 
              apV (liftOp K (idOp V)) (↑ x)
            ≡⟨ liftOp-↑ x ⟩
              ap up (apV (idOp V) x)
            ≡⟨ cong (ap up) (apV-idOp x) ⟩
              ap up (var x)              
            ≡⟨ apV-up ⟩
              var (↑ x)
            ≡⟨⟨ apV-idOp (↑ x) ⟩⟩
              (apV (idOp (V , K)) (↑ x)
            ∎)
       
          liftOp'-idOp : ∀ {V} A → liftOp' A (idOp V) ∼op idOp (extend' V A)
          liftOp'-idOp [] = ∼-refl
          liftOp'-idOp {V} (K ∷ A) = let open EqReasoning (OP (extend' (V , K) A) (extend' (V , K) A)) in 
            begin
              liftOp' A (liftOp K (idOp V))
            ≈⟨ liftOp'-cong A liftOp-idOp ⟩
              liftOp' A (idOp (V , K))
            ≈⟨ liftOp'-idOp A ⟩
              idOp (extend' (V , K) A)
            ∎

          ap-idOp : ∀ {V} {C} {K} {E : Subexpression V C K} → ap (idOp V) E ≡ E
          ap-idOp {E = var x} = apV-idOp x
          ap-idOp {E = app c EE} = cong (app c) ap-idOp
          ap-idOp {E = out} = refl
          ap-idOp {E = _,,_ {A = A} E F} = cong₂ _,,_ (trans (ap-congl E (liftOp'-idOp A)) ap-idOp) ap-idOp
          
  record LiftFamily : Set₂ where
      field
        preOpFamily : PreOpFamily
        lifting : PreOpFamily.Lifting preOpFamily
        isLiftFamily : PreOpFamily.Lifting.IsLiftFamily lifting
      open PreOpFamily preOpFamily public
      open Lifting lifting public
      open IsLiftFamily isLiftFamily public

record Grammar : Set₁ where
  field
    taxonomy : Taxonomy
    toGrammar : ToGrammar taxonomy
  open Taxonomy.Taxonomy taxonomy public
  open ToGrammar toGrammar public
\end{code}
