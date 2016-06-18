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
sub↑ : ∀ {U} {V} K → Sub U V → Sub (U , K) (V , K)
sub↑ _ _ _ x₀ = var x₀
sub↑ _ σ K (↑ x) = (σ K x) 〈 upRep 〉

sub↑-cong : ∀ {U} {V} {K} {σ σ' : Sub U V} → 
  σ ∼ σ' → sub↑ K σ ∼ sub↑ K σ'
\end{code}

\AgdaHide{
\begin{code}
sub↑-cong {K = K} σ-is-σ' x₀ = refl
sub↑-cong σ-is-σ' (↑ x) = cong (λ E → E 〈 upRep 〉) (σ-is-σ' x)
\end{code}
}

\begin{code}
SUB↑ : Lifting pre-substitution
SUB↑ = record { liftOp = sub↑ ; liftOp-cong = sub↑-cong }
\end{code}
    
Then, given an expression $E$ of kind $K$ over $U$, we write $E[\sigma]$ for the application of $\sigma$ to $E$, which is the result of substituting $\sigma(x)$ for $x$ for each variable in $E$, avoiding capture.

\begin{code}    
infix 70 _⟦_⟧
_⟦_⟧ : ∀ {U} {V} {C} {K} → 
  Subexpression U C K → Sub U V → Subexpression V C K
E ⟦ σ ⟧ = Lifting.ap SUB↑ σ E
\end{code}
