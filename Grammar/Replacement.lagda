Let $\mathsf{embedl}$ be the canonical injection $A \rightarrow \mathsf{extend}\ A\ K\ F$, which
is a replacement.

\begin{code}
open import Data.Nat
open import Grammar

module Grammar.Replacement (G : Grammar) where
  open Grammar.Grammar G

  embedl : ∀ {A} {K} {F} → Rep A (extend A K F)
  embedl {F = zero} _ x = x
  embedl {F = suc F} K x = ↑ (embedl {F = F} K x)
\end{code}
