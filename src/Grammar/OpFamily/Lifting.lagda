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
  apV2 : ∀ {U} {V} {A} → Op U V → Var (liftAlphabet U) A → Abstraction V A
  apV2 {∅} _ ()
  apV2 {_ , _} σ x₀ = apV σ x₀
  apV2 {U , _} σ (↑ x) = {!apV2 {U} σ x!}

  ap : ∀ {U} {V} {C} {K} → 
    Op U V → Subexpression U C K → Subexpression V C K
  ap {∅} _ (var2 () _)
  ap {U , K} ρ (var2 x₀ []) = apV ρ x₀
  ap {U , K} ρ (var2 (↑ x) EE) = {!ap {U} ρ (var2 x EE)!}
  ap ρ (Grammar.app x E) = {!!}
  ap ρ Grammar.[] = {!!}
  ap ρ (E Grammar.∷ E₁) = {!!}
\end{code}

We prove that application respects $\sim$.

\begin{code}
  ap-congl : ∀ {U} {V} {C} {K} 
    {ρ σ : Op U V} (E : Subexpression U C K) →
    ρ ∼op σ → ap ρ E ≡ ap σ E
\end{code}

\AgdaHide{
\begin{code}
  ap-congl (var2 x EE) ρ-is-σ = {!!}
  ap-congl (app c E) ρ-is-σ = {!!}
  ap-congl [] _ = {!!}
  ap-congl (_∷_ E F) ρ-is-σ = {!!}

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
