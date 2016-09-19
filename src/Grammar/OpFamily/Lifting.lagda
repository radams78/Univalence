\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.OpFamily.Lifting (G : Grammar) where
open import Function.Equality hiding (Π)
open import Data.List
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
    liftOp-cong : ∀ {V} {W} {K} {ρ σ : Op V W} → 
      ρ ∼op σ → liftOp K ρ ∼op liftOp K σ

  LIFTOP : ∀ {U} {V} K → OP U V ⟶ OP (U , K) (V , K)
  LIFTOP = λ K → record { _⟨$⟩_ = liftOp K ; cong = liftOp-cong }
\end{code}

Given an operation $\sigma : U \rightarrow V$ and a list of variable kinds $A \equiv (A_1 , \ldots , A_n)$, define
the \emph{repeated lifting} $\sigma^A$ to be $((\cdots(\sigma , A_1) , A_2) , \cdots ) , A_n)$.

\begin{code}
  LIFTOP' : ∀ {U} {V} VV → OP U V ⟶ OP (extend U VV) (extend V VV)
  LIFTOP' [] = id
  LIFTOP' (W ∷ VV) = LIFTOP' VV ∘ LIFTOP W

  liftOp' : ∀ {U} {V} VV → Op U V → Op (extend U VV) (extend V VV)
  liftOp' A = Function.Equality.Π._⟨$⟩_ (LIFTOP' A)

  liftOp'-cong : ∀ {U} {V} A {ρ σ : Op U V} → 
    ρ ∼op σ → liftOp' A ρ ∼op liftOp' A σ
  liftOp'-cong A = Function.Equality.Π.cong (LIFTOP' A)
\end{code}

This allows us to define the action of \emph{application} $E[\sigma]$:

\begin{code}
  ap : ∀ {U} {V} {C} {K} → Op U V → Subexpression U C K → Subexpression V C K
  ap ρ (var x) = apV ρ x
  ap ρ (app c EE) = app c (ap ρ EE)
  ap _ [] = []
  ap ρ (_∷_ {A = SK AA _} E EE) = ap (liftOp' AA ρ) E ∷ ap ρ EE
\end{code}

We prove that application respects $\sim$.

\begin{code}
  ap-congl : ∀ {U} {V} {C} {K} 
    {ρ σ : Op U V} → ρ ∼op σ → ∀ (E : Subexpression U C K) →
    ap ρ E ≡ ap σ E
\end{code}

\AgdaHide{
\begin{code}
  ap-congl ρ-is-σ (var x) = ρ-is-σ x
  ap-congl ρ-is-σ (app c E) = Prelims.cong (app c) (ap-congl ρ-is-σ E)
  ap-congl _ [] = refl
  ap-congl ρ-is-σ (_∷_ {A = SK AA _} E F) = 
    cong₂ _∷_ (ap-congl (liftOp'-cong AA ρ-is-σ) E) (ap-congl ρ-is-σ F)

  ap-congr : ∀ {U} {V} {C} {K}
    {σ : Op U V} {E F : Subexpression U C K} →
    E ≡ F → ap σ E ≡ ap σ F
  ap-congr {σ = σ} = Prelims.cong (ap σ)

  ap-cong : ∀ {U} {V} {C} {K}
    {ρ σ : Op U V} {M N : Subexpression U C K} →
    ρ ∼op σ → M ≡ N → ap ρ M ≡ ap σ N
  ap-cong {ρ = ρ} {σ} {M} {N} ρ∼σ M≡N = let open ≡-Reasoning in 
    begin
      ap ρ M
    ≡⟨ ap-congl ρ∼σ M ⟩
      ap σ M
    ≡⟨ ap-congr M≡N ⟩
      ap σ N
    ∎
\end{code}
}
