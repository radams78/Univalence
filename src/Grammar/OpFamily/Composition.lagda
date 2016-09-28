\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.OpFamily.Composition (A : Grammar) where
open import Data.List
open import Function.Equality hiding (cong;_∘_)
open import Prelims
open Grammar A hiding (_⟶_)
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
  infix 25 _∘_
  field
    _∘_ : ∀ {U} {V} {W} → Op F V W → Op G U V → Op H U W
    liftOp-comp : ∀ {U V W K σ ρ} → 
      _∼op_ H (liftOp H K (_∘_ {U} {V} {W} σ ρ)) 
        (liftOp F K σ ∘ liftOp G K ρ)
    apV-comp : ∀ {U} {V} {W} {K} {σ} {ρ} {x : Var U K} → 
      apV H (_∘_ {U} {V} {W} σ ρ) x ≡ ap F σ (apV G ρ x)
\end{code}

\begin{lemma}
For any composition $\circ$:
\begin{enumerate}
\item
If $\sigma \sim \sigma'$ and $\rho \sim \rho'$ then $\sigma \circ \rho \sim \sigma' \circ \rho'$
\item
$(\sigma \circ \rho)^A \sim \sigma^A \circ \rho^A$
\item
$E [ \sigma \circ \rho ] \equiv E [ \rho ] [ \sigma ]$
\end{enumerate}
\end{lemma}

\begin{code}
  comp-cong : ∀ {U V W} {σ σ' : Op F V W} {ρ ρ' : Op G U V} → 
    _∼op_ F σ σ' → _∼op_ G ρ ρ' → _∼op_ H (σ ∘ ρ) (σ' ∘ ρ')
\end{code}

\AgdaHide{
\begin{code}
  comp-cong {U} {V} {W} {σ} {σ'} {ρ} {ρ'} σ∼σ' ρ∼ρ' x = let open ≡-Reasoning in 
    begin
      apV H (σ ∘ ρ) x
    ≡⟨ apV-comp ⟩
      ap F σ (apV G ρ x)
    ≡⟨ ap-cong F σ∼σ' (ρ∼ρ' x) ⟩
      ap F σ' (apV G ρ' x)
    ≡⟨⟨ apV-comp ⟩⟩
      apV H (σ' ∘ ρ') x
    ∎
\end{code}
}

\begin{code}
  liftsOp-comp : ∀ {U V W} A {σ ρ} → 
    _∼op_ H (liftsOp H A (_∘_ {U} {V} {W} σ ρ)) 
      (liftsOp F A σ ∘ liftsOp G A ρ)
\end{code}

\AgdaHide{
\begin{code}
  liftsOp-comp [] = ∼-refl H
  liftsOp-comp {U} {V} {W} (K ∷ A) {σ} {ρ} = let open EqReasoning (OP H _ _) in 
    begin
      liftsOp H A (liftOp H K (σ ∘ ρ))
    ≈⟨ liftsOp-cong H A liftOp-comp ⟩
      liftsOp H A (liftOp F K σ ∘ liftOp G K ρ)
    ≈⟨ liftsOp-comp A ⟩
      liftsOp F A (liftOp F K σ) ∘ liftsOp G A (liftOp G K ρ)
    ∎
\end{code}
}

\begin{code}
  ap-comp : ∀ {U V W C K} (E : Subexpression U C K) {σ ρ} → 
    ap H (_∘_ {U} {V} {W} σ ρ) E ≡ ap F σ (ap G ρ E)
\end{code}

\AgdaHide{
\begin{code}
  ap-comp (var _) = apV-comp
  ap-comp (app c E) = cong (app c) (ap-comp E)
  ap-comp [] = refl
  ap-comp (_∷_ {A = SK A _} E E') {σ} {ρ} = cong₂ _∷_
    (let open ≡-Reasoning in 
    begin
      ap H (liftsOp H A (σ ∘ ρ)) E
    ≡⟨ ap-congl H (liftsOp-comp A) E ⟩
      ap H (liftsOp F A σ ∘ liftsOp G A ρ) E
    ≡⟨ ap-comp E ⟩
      ap F (liftsOp F A σ) (ap G (liftsOp G A ρ) E)
    ∎) 
    (ap-comp E')
\end{code}
}

\begin{lm}
Let $\circ_1 : F;G \rightarrow H$ and $\circ_2 : F';G' \rightarrow H$.  If
\[ \sigma \circ_1 \rho \sim \simga' \circ_2 \rho' \]
then $E [\rho] [\sigma] \equiv E [\rho'] [\sigma']$ for every expression $E$.
\end{lm}

\begin{code}
ap-comp-sim : ∀ {F F' G G' H} (comp₁ : Composition F G H) (comp₂ : Composition F' G' H) {U} {V} {V'} {W}
  {σ : Op F V W} {ρ : Op G U V} {σ' : Op F' V' W} {ρ' : Op G' U V'} →
  _∼op_ H (Composition._∘_ comp₁ σ ρ) (Composition._∘_ comp₂ σ' ρ') →
  ∀ {C} {K} (E : Subexpression U C K) →
  ap F σ (ap G ρ E) ≡ ap F' σ' (ap G' ρ' E)
\end{code}

\AgdaHide{
\begin{code}
ap-comp-sim {F} {F'} {G} {G'} {H} comp₁ comp₂ {U} {V} {V'} {W} {σ} {ρ} {σ'} {ρ'} hyp {C} {K} E =
  let open ≡-Reasoning in 
  begin
    ap F σ (ap G ρ E)
  ≡⟨⟨ Composition.ap-comp comp₁ E {σ} {ρ} ⟩⟩
    ap H (Composition._∘_ comp₁ σ ρ) E
  ≡⟨ ap-congl H hyp E ⟩
    ap H (Composition._∘_ comp₂ σ' ρ') E
  ≡⟨ Composition.ap-comp comp₂ E {σ'} {ρ'} ⟩
    ap F' σ' (ap G' ρ' E)
  ∎
\end{code}
}

\begin{lm}
Suppose there exist compositions $F;G \rightarrow H$ and $F';F \rightarrow H$.
Let $\uparrow_F$, $\uparrow_{F'}$ and $\uparrow_G$ be the lifting operations of $F$, $F'$ and $G$.
Suppose $\up_F(E) \equiv \up_{F'}(E)$ for every subexpression $E$.  Then
$\uparrow_G(E)[F \uparrow] \equiv \uparrow_{F'}(\sigma(E))$ for every subexpression $E$.
\end{lm}

\begin{code}
liftOp-up-mixed : ∀ {F} {G} {H} {F'} (comp₁ : Composition F G H) (comp₂ : Composition F' F H)
  {U} {V} {C} {K} {L} {σ : Op F U V} →
  (∀ {V} {C} {K} {L} {E : Subexpression V C K} → ap F (up F {V} {L}) E ≡ ap F' (up F' {V} {L}) E) →
  ∀ {E : Subexpression U C K} → ap F (liftOp F L σ) (ap G (up G) E) ≡ ap F' (up F') (ap F σ E)
liftOp-up-mixed {F} {G} {H} {F'} comp₁ comp₂ {U} {V} {C} {K} {L} {σ} hyp {E = E} = ap-comp-sim comp₁ comp₂ 
  (λ x → let open ≡-Reasoning in 
  begin
    apV H (Composition._∘_ comp₁ (liftOp F L σ) (up G)) x
  ≡⟨ Composition.apV-comp comp₁ ⟩
    ap F (liftOp F L σ) (apV G (up G) x)
  ≡⟨ cong (ap F (liftOp F L σ)) (apV-up G) ⟩
    apV F (liftOp F L σ) (↑ x)
  ≡⟨ liftOp-↑ F x ⟩
    ap F (up F) (apV F σ x)
  ≡⟨ hyp {E = apV F σ x}⟩
    ap F' (up F') (apV F σ x)
  ≡⟨⟨ Composition.apV-comp comp₂ ⟩⟩
    apV H (Composition._∘_ comp₂ (up F') σ) x
  ∎) 
  E
\end{code}
}
