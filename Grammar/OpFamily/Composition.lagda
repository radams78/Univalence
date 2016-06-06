\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.OpFamily.Composition (A : Grammar) where
open import Data.List
open import Prelims
open Grammar A
open import Grammar.OpFamily.LiftFamily A

open LiftFamily
\end{code}
}

\subsubsection{Compositions}

Let $F$, $G$ and $H$ be three pre-families with lifting.  A \emph{composition} $\circ : F;G \rightarrow H$ is a family of functions
\[ \circ_{UVW} : F[V,W] \times G[U,V] \rightarrow H[U,W] \]
for all alphabets $U$, $V$ and $W$ such that:
\begin{itemize}
\item
$(\sigma \circ \rho , K) \sim (\sigma , K) \circ (\rho , K)$
\item
$(\sigma \circ \rho)(x) \equiv \rho(x) [ \sigma ]$
\end{itemize}

\begin{code}
record Composition (F G H : LiftFamily) : Set where
  field
    circ : ∀ {U} {V} {W} → Op F V W → Op G U V → Op H U W
    liftOp-circ : ∀ {U V W K σ ρ} → 
      _∼op_ H (liftOp H K (circ {U} {V} {W} σ ρ)) 
        (circ (liftOp F K σ) (liftOp G K ρ))
    apV-circ : ∀ {U} {V} {W} {K} {σ} {ρ} {x : Var U K} → 
      apV H (circ {U} {V} {W} σ ρ) x ≡ ap F σ (apV G ρ x)
\end{code}

\begin{lemma}
For any composition $\circ$:
\begin{enumerate}
\item
$(\sigma \circ \rho)^A \sim \sigma^A \circ \rho^A$
\item
$E [ \sigma \circ \rho ] \equiv E [ \rho ] [ \sigma ]$
\item
If $\sigma \sim \sigma'$ and $\rho \sim \rho'$ then $\sigma \circ \rho \sim \sigma' \circ \rho'$
\end{enumerate}
\end{lemma}

\begin{code}
  liftOp'-circ : ∀ {U V W} A {σ ρ} → 
    _∼op_ H (liftOp' H A (circ {U} {V} {W} σ ρ)) 
      (circ (liftOp' F A σ) (liftOp' G A ρ))
\end{code}

\AgdaHide{
\begin{code}
  liftOp'-circ [] = ∼-refl H
  liftOp'-circ {U} {V} {W} (K ∷ A) {σ} {ρ} = let open EqReasoning (OP H _ _) in 
    begin
      liftOp' H A (liftOp H K (circ σ ρ))
    ≈⟨ liftOp'-cong H A liftOp-circ ⟩
      liftOp' H A (circ (liftOp F K σ) (liftOp G K ρ))
    ≈⟨ liftOp'-circ A ⟩
      circ (liftOp' F A (liftOp F K σ)) (liftOp' G A (liftOp G K ρ))
    ∎
\end{code}
}

\begin{code}
  ap-circ : ∀ {U V W C K} (E : Subexpression U C K) {σ ρ} → 
    ap H (circ {U} {V} {W} σ ρ) E ≡ ap F σ (ap G ρ E)
\end{code}

\AgdaHide{
\begin{code}
  ap-circ (var _) = apV-circ
  ap-circ (app c E) = cong (app c) (ap-circ E)
  ap-circ out = refl
  ap-circ (_,,_ {A = pi A _} E E') {σ} {ρ} = cong₂ _,,_
    (let open ≡-Reasoning in 
    begin
      ap H (liftOp' H A (circ σ ρ)) E
    ≡⟨ ap-congl H E (liftOp'-circ A) ⟩
      ap H (circ (liftOp' F A σ) (liftOp' G A ρ)) E
    ≡⟨ ap-circ E ⟩
      ap F (liftOp' F A σ) (ap G (liftOp' G A ρ) E)
    ∎) 
    (ap-circ E')
\end{code}
}

\begin{code}
  circ-cong : ∀ {U V W} {σ σ' : Op F V W} {ρ ρ' : Op G U V} → 
    _∼op_ F σ σ' → _∼op_ G ρ ρ' → _∼op_ H (circ σ ρ) (circ σ' ρ')
\end{code}

\AgdaHide{
\begin{code}
  circ-cong {U} {V} {W} {σ} {σ'} {ρ} {ρ'} σ∼σ' ρ∼ρ' x = let open ≡-Reasoning in 
    begin
      apV H (circ σ ρ) x
    ≡⟨ apV-circ ⟩
      ap F σ (apV G ρ x)
    ≡⟨ ap-cong F σ∼σ' (ρ∼ρ' x) ⟩
      ap F σ' (apV G ρ' x)
    ≡⟨⟨ apV-circ ⟩⟩
      apV H (circ σ' ρ') x
    ∎

ap-circ-sim : ∀ {F F' G G' H} (circ₁ : Composition F G H) (circ₂ : Composition F' G' H) {U} {V} {V'} {W}
  {σ : Op F V W} {ρ : Op G U V} {σ' : Op F' V' W} {ρ' : Op G' U V'} →
  _∼op_ H (Composition.circ circ₁ σ ρ) (Composition.circ circ₂ σ' ρ') →
  ∀ {C} {K} (E : Subexpression U C K) →
  ap F σ (ap G ρ E) ≡ ap F' σ' (ap G' ρ' E)
ap-circ-sim {F} {F'} {G} {G'} {H} circ₁ circ₂ {U} {V} {V'} {W} {σ} {ρ} {σ'} {ρ'} hyp {C} {K} E =
  let open ≡-Reasoning in 
  begin
    ap F σ (ap G ρ E)
  ≡⟨⟨ Composition.ap-circ circ₁ E {σ} {ρ} ⟩⟩
    ap H (Composition.circ circ₁ σ ρ) E
  ≡⟨ ap-congl H E hyp ⟩
    ap H (Composition.circ circ₂ σ' ρ') E
  ≡⟨ Composition.ap-circ circ₂ E {σ'} {ρ'} ⟩
    ap F' σ' (ap G' ρ' E)
  ∎

liftOp-up-mixed : ∀ {F} {G} {H} {F'} (circ₁ : Composition F G H) (circ₂ : Composition F' F H)
  {U} {V} {K} {σ : Op F U V} →
  (∀ {V} {C} {K} {L} {E : Subexpression V C K} → ap F (up F {V} {L}) E ≡ ap F' (up F' {V} {L}) E) →
  _∼op_ H (Composition.circ circ₁ (liftOp F K σ) (up G)) (Composition.circ circ₂ (up F') σ)
liftOp-up-mixed {F} {G} {H} {F'} circ₁ circ₂ {U} {V} {K} {σ} hyp {L} x = 
  let open ≡-Reasoning in 
  begin
    apV H (Composition.circ circ₁ (liftOp F K σ) (up G)) x
  ≡⟨ Composition.apV-circ circ₁ ⟩
    ap F (liftOp F K σ) (apV G (up G) x)
  ≡⟨ cong (ap F (liftOp F K σ)) (apV-up G) ⟩
    apV F (liftOp F K σ) (↑ x)
  ≡⟨ liftOp-↑ F x ⟩
    ap F (up F) (apV F σ x)
  ≡⟨ hyp {E = apV F σ x}⟩
    ap F' (up F') (apV F σ x)
  ≡⟨⟨ Composition.apV-circ circ₂ ⟩⟩
    apV H (Composition.circ circ₂ (up F') σ) x
  ∎

liftOp-up-mixed' : ∀ {F} {G} {H} {F'} (circ₁ : Composition F G H) (circ₂ : Composition F' F H)
  {U} {V} {C} {K} {L} {σ : Op F U V} →
  (∀ {V} {C} {K} {L} {E : Subexpression V C K} → ap F (up F {V} {L}) E ≡ ap F' (up F' {V} {L}) E) →
  ∀ {E : Subexpression U C K} → ap F (liftOp F L σ) (ap G (up G) E) ≡ ap F' (up F') (ap F σ E)
liftOp-up-mixed' circ₁ circ₂ hyp {E = E} = ap-circ-sim circ₁ circ₂ (liftOp-up-mixed circ₁ circ₂ (λ {_} {_} {_} {_} {E} → hyp {E = E})) E
\end{code}
}
