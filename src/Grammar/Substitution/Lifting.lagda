\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.Substitution.Lifting (G : Grammar) where
open import Prelims
open Grammar G
open import Grammar.OpFamily.Lifting G
open import Grammar.Replacement G
open import Grammar.Substitution.PreOpFamily G
\end{code}
}

\begin{code}
liftSub : ∀ {U} {V} K → Sub U V → Sub (U , K) (V , K)
liftSub _ _ _ x₀ = var x₀
liftSub _ σ K (↑ x) = (σ K x) 〈 upRep 〉

liftSub-cong : ∀ {U} {V} {K} {σ σ' : Sub U V} → 
  σ ∼ σ' → liftSub K σ ∼ liftSub K σ'
\end{code}

\AgdaHide{
\begin{code}
liftSub-cong {K = K} σ-is-σ' x₀ = refl
liftSub-cong σ-is-σ' (↑ x) = cong (λ E → E 〈 upRep 〉) (σ-is-σ' x)
\end{code}
}

\begin{code}
LIFTSUB : Lifting pre-substitution
LIFTSUB = record { liftOp = liftSub ; liftOp-cong = liftSub-cong }
\end{code}
    
Then, given an expression $E$ of kind $K$ over $U$, we write $E[\sigma]$ for the application of $\sigma$ to $E$, which is the result of substituting $\sigma(x)$ for $x$ for each variable in $E$, avoiding capture.

\begin{code}    
infix 70 _⟦_⟧
_⟦_⟧ : ∀ {U} {V} {C} {K} → 
  Subexp U C K → Sub U V → Subexp V C K
E ⟦ σ ⟧ = Lifting.ap LIFTSUB σ E
\end{code}
