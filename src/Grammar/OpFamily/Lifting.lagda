\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.OpFamily.Lifting (G : Grammar) where
open import Level
open import Relation.Binary
open import Function.Equality hiding (setoid)
open import Data.Product hiding (map) renaming (_,_ to _,p_)
open import Data.List hiding (foldr;map)
open import Algebra
open import Prelims
open Grammar G renaming (_⟶_ to _⇒_)
open import Grammar.OpFamily.PreOpFamily G
\end{code}
}

\subsubsection{Liftings}

Define a \emph{lifting} on a pre-family to be an function $(- , K)$ that respects $\sim$:

\begin{code}
record Lifting (F : PreOpFamily) : Set₁ where
  open PreOpFamily F
  field
    liftOp : ∀ {U} {V} K → Op U V → Op (U , K) (V , K)
    liftOp-cong : ∀ {V} {W} {K} {ρ σ : Op V W} → ρ ∼op σ → liftOp K ρ ∼op liftOp K σ

  LIFTOP : ∀ {U} {V} K → OP U V ⟶ OP (U , K) (V , K)
  LIFTOP = λ K → record { _⟨$⟩_ = liftOp K ; cong = liftOp-cong }
\end{code}

Given an operation $\sigma : U \rightarrow V$ and a list of variable kinds $A \equiv (A_1 , \ldots , A_n)$, define
the \emph{repeated lifting} $\sigma^A$ to be $((\cdots(\sigma , A_1) , A_2) , \cdots ) , A_n)$.

\begin{code}
  LIFTSOP' : ∀ {U V} F (AA : FoldFunc.F F VarKind) → OP U V ⟶ OP (extend F U AA) (extend F V AA)
  LIFTSOP' F AA = FoldFunc.depfold₂ F {C = λ U V → OP (lower U) (lower V)} AA (λ _ _ → LIFTOP)

  liftsOp' : ∀ {U V} F AA → Op U V → Op (extend F U AA) (extend F V AA)
  liftsOp' F AA = Π._⟨$⟩_ (LIFTSOP' F AA)

  liftsOp'-cong : ∀ {U V} F AA {ρ σ : Op U V} → ρ ∼op σ → liftsOp' F AA ρ ∼op liftsOp' F AA σ
  liftsOp'-cong F AA = Π.cong (LIFTSOP' F AA)

  liftsOp : ∀ {U} {V} VV → Op U V → Op (extend LIST U VV) (extend LIST V VV)
  liftsOp = liftsOp' LIST

  liftsOp-cong : ∀ {U} {V} A {ρ σ : Op U V} → ρ ∼op σ → liftsOp A ρ ∼op liftsOp A σ
  liftsOp-cong = liftsOp'-cong LIST

  liftsnocOp : ∀ {U V} KK → Op U V → Op (extend SNOCLIST U KK) (extend SNOCLIST V KK)
  liftsnocOp = liftsOp' SNOCLIST
\end{code}

This allows us to define the action of \emph{application} $E[\sigma]$:

\begin{code}
  ap : ∀ {U} {V} {C} {K} → Op U V → Subexp U C K → Subexp V C K
  ap ρ (var x) = apV ρ x
  ap ρ (app c EE) = app c (ap ρ EE)
  ap _ [] = []
  ap ρ (_∷_ {A = SK AA _} E EE) = ap (liftsOp AA ρ) E ∷ ap ρ EE
\end{code}

We prove that application respects $\sim$.

\begin{code}
  ap-congl : ∀ {U} {V} {C} {K} 
    {ρ σ : Op U V} → ρ ∼op σ → ∀ (E : Subexp U C K) →
    ap ρ E ≡ ap σ E
\end{code}

\AgdaHide{
\begin{code}
  ap-congl ρ-is-σ (var x) = ρ-is-σ x
  ap-congl ρ-is-σ (app c E) = Prelims.cong (app c) (ap-congl ρ-is-σ E)
  ap-congl _ [] = refl
  ap-congl ρ-is-σ (_∷_ {A = SK AA _} E F) = 
    cong₂ _∷_ (ap-congl (liftsOp-cong AA ρ-is-σ) E) (ap-congl ρ-is-σ F)

  ap-congr : ∀ {U} {V} {C} {K} {σ : Op U V} {E F : Subexp U C K} → E ≡ F → ap σ E ≡ ap σ F
  ap-congr {σ = σ} = Prelims.cong (ap σ)

  ap-cong : ∀ {U} {V} {C} {K}
    {ρ σ : Op U V} {M N : Subexp U C K} →
    ρ ∼op σ → M ≡ N → ap ρ M ≡ ap σ N
  ap-cong {U} {V} {C} {K} =
    cong2 {A = OP U V} {B = Prelims.EqReasoning.setoid (Subexp U C K)} {C = Prelims.EqReasoning.setoid (Subexp V C K)} 
    ap ap-congl (λ _ → ap-congr)
\end{code}
}
