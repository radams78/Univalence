\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.OpFamily.Lifting (G : Grammar) where
open import Data.List
open import Prelims
open Grammar G
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
\end{code}

Given an operation $\sigma : U \rightarrow V$ and a list of variable kinds $A \equiv (A_1 , \ldots , A_n)$, define
the \emph{repeated lifting} $\sigma^A$ to be $((\cdots(\sigma , A_1) , A_2) , \cdots ) , A_n)$.

\begin{code}
{-  liftOp' : ∀ {U} {V} A → Op U V → Op (extend U A) (extend V A)
  liftOp' [] σ = σ
  liftOp' (K ∷ A) σ = liftOp' A (liftOp K σ) -}

  liftOp'' : ∀ {U} {V} A → Op U V → Op (extend U A) (extend V A)
  liftOp'' [] σ = σ
  liftOp'' (K ∷ A) σ = liftOp'' A (liftOp K σ)

  postulate liftOp''' : ∀ {U} {V} A → Op U V → Op (dom {VarKind} {ExpressionKind} U A) (dom V A)

{-  liftOp'-cong : ∀ {U} {V} A {ρ σ : Op U V} → 
    ρ ∼op σ → liftOp' A ρ ∼op liftOp' A σ
\end{code}

\AgdaHide{
\begin{code}
  liftOp'-cong [] ρ-is-σ = ρ-is-σ
  liftOp'-cong (_ ∷ A) ρ-is-σ = liftOp'-cong A (liftOp-cong ρ-is-σ) -}

  postulate liftOp''-cong : ∀ {U} {V} A {ρ σ : Op U V} → 
                          ρ ∼op σ → liftOp'' A ρ ∼op liftOp'' A σ

  postulate liftOp'''-cong : ∀ {U} {V} A {ρ σ : Op U V} → 
                           ρ ∼op σ → liftOp''' A ρ ∼op liftOp''' A σ
\end{code}
}

This allows us to define the action of \emph{application} $E[\sigma]$:

\begin{code}
  ap : ∀ {U} {V} {C} {K} → 
    Op U V → Subexpression U C K → Subexpression V C K
  ap ρ (var x) = apV ρ x
  ap ρ (app c EE) = app c (ap ρ EE)
  ap _ out = out
  ap ρ (_,,_ {A = A} E EE) = ap (liftOp''' A ρ) E ,, ap ρ EE
\end{code}

We prove that application respects $\sim$.

\begin{code}
  ap-congl : ∀ {U} {V} {C} {K} 
    {ρ σ : Op U V} (E : Subexpression U C K) →
    ρ ∼op σ → ap ρ E ≡ ap σ E
\end{code}

\AgdaHide{
\begin{code}
  ap-congl (var x) ρ-is-σ = ρ-is-σ x
  ap-congl (app c E) ρ-is-σ = cong (app c) (ap-congl E ρ-is-σ)
  ap-congl out _ = refl
  ap-congl (_,,_ {A = A} E F) ρ-is-σ = 
    cong₂ _,,_ (ap-congl E (liftOp'''-cong A ρ-is-σ)) (ap-congl F ρ-is-σ)

  ap-congr : ∀ {U} {V} {C} {K}
    {σ : Op U V} {E F : Subexpression U C K} →
    E ≡ F → ap σ E ≡ ap σ F
  ap-congr {σ = σ} = cong (ap σ)

  ap-cong : ∀ {U} {V} {C} {K}
    {ρ σ : Op U V} {M N : Subexpression U C K} →
    ρ ∼op σ → M ≡ N → ap ρ M ≡ ap σ N
  ap-cong {ρ = ρ} {σ} {M} {N} ρ∼σ M≡N = let open ≡-Reasoning in 
    begin
      ap ρ M
    ≡⟨ ap-congl M ρ∼σ ⟩
      ap σ M
    ≡⟨ ap-congr M≡N ⟩
      ap σ N
    ∎
\end{code}
}
