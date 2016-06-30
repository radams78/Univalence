\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.Substitution.LiftFamily (G : Grammar) where
open import Prelims
open Grammar G
open import Grammar.OpFamily.LiftFamily G
open import Grammar.Substitution.PreOpFamily G
open import Grammar.Substitution.Lifting G
open import Grammar.Substitution.RepSub G
\end{code}
}

It is now easy to show that substitution forms a pre-family with lifting.  If $\sigma : U \rightarrow V$ and $x \in U$ then $(\sigma , K)(\uparrow x) \equiv
\sigma(x) \langle \uparrow \rangle \equiv (\sigma , K)(x) [ \uparrow ]$.

\begin{code}
SubLF : LiftFamily
SubLF = record { 
  preOpFamily = pre-substitution ; 
  lifting = LIFTSUB ; 
  isLiftFamily = record { 
    liftOp-x₀ = refl ; 
    liftOp-↑ = λ {_} {_} {_} {_} {σ} x → rep-is-sub (σ _ x) }}
\end{code}
