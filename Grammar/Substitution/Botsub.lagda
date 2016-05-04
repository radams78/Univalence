\begin{code}
open import Prelims
open import Grammar

module Grammar.Substitution.Botsub (G : Grammar) where
  open Grammar.Grammar G
  open import Grammar.Replacement G
  open import Grammar.Substitution G
\end{code}

Let $E$ be an expression of kind $K$ over $V$.  Then we write $[x_0 := E]$ for the following substitution
$(V , K) \Rightarrow V$:

\begin{code}
  x₀:= : ∀ {V} {K} → Expression V (varKind K) → Sub (V , K) V
  x₀:= E _ x₀ = E
  x₀:= E K₁ (↑ x) = var x
\end{code}

\begin{lemma}
\begin{enumerate}
\item
$$ \rho \bullet_1 [x_0 := E] \sim [x_0 := E \langle \rho \rangle] \bullet_2 (\rho , K) $$
\item
$$ \sigma \bullet [x_0 := E] \sim [x_0 := E[\sigma]] \bullet (\sigma , K) $$
\end{enumerate}
\end{lemma}

\begin{code}
  comp₁-botsub : ∀ {U} {V} {K} {E : Expression U (varKind K)} {ρ : Rep U V} →
      ρ •₁ (x₀:= E) ∼ (x₀:= (E 〈 ρ 〉)) •₂ Rep↑ K ρ
  comp₁-botsub x₀ = refl
  comp₁-botsub (↑ _) = refl

  comp-botsub : ∀ {U} {V} {K} {E : Expression U (varKind K)} {σ : Sub U V} →
      σ • (x₀:= E) ∼ (x₀:= (E ⟦ σ ⟧)) • Sub↑ K σ
  comp-botsub x₀ = refl
  comp-botsub {σ = σ} {L} (↑ x) = trans (sym sub-idOp) (sub-comp₂ {E = σ L x})
\end{code}

