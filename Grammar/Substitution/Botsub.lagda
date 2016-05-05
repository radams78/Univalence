\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.Substitution.Botsub (G : Grammar) where
open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G
open import Grammar.Substitution G
\end{code}
}

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

comp₁-botsub' : ∀ {U} {V} {C} {K} {L} (E : Subexpression (U , K) C L) {F : Expression U (varKind K)} {ρ : Rep U V} →
  E ⟦ x₀:= F ⟧ 〈 ρ 〉 ≡ E 〈 Rep↑ K ρ 〉 ⟦ x₀:= (F 〈 ρ 〉) ⟧
comp₁-botsub' E = ap-circ-sim COMP₁ COMP₂ comp₁-botsub E

comp-botsub : ∀ {U} {V} {K} {E : Expression U (varKind K)} {σ : Sub U V} →
  σ • (x₀:= E) ∼ (x₀:= (E ⟦ σ ⟧)) • Sub↑ K σ
comp-botsub x₀ = refl
comp-botsub {U} {V} {K} {E} {σ} {L} (↑ x) = let open ≡-Reasoning in 
  begin
    (σ • x₀:= E) _ (↑ x)
  ≡⟨⟩
    σ _ x
  ≡⟨⟨ sub-idOp ⟩⟩
    σ _ x ⟦ idOpSub V ⟧
  ≡⟨⟩
    σ _ x ⟦ x₀:= (E ⟦ σ ⟧) •₂ upRep ⟧
  ≡⟨ sub-comp₂ (σ L x) ⟩
    (σ _ x) 〈 upRep 〉 ⟦ x₀:= (E ⟦ σ ⟧) ⟧
  ≡⟨⟩
    (x₀:= (E ⟦ σ ⟧) • Sub↑ K σ) _ (↑ x)
  ∎

comp-botsub' : ∀ {U} {V} {C} {K} {L} 
  {E : Expression U (varKind K)} {σ : Sub U V} (F : Subexpression (U , K) C L) →
  F ⟦ x₀:= E ⟧ ⟦ σ ⟧ ≡ F ⟦ Sub↑ K σ ⟧ ⟦ x₀:= (E ⟦ σ ⟧) ⟧
comp-botsub' F = ap-circ-sim (OpFamily.COMP substitution) (OpFamily.COMP substitution) comp-botsub F

botsub-upRep : ∀ {U} {C} {K} {L} {E : Subexpression U C K} {F : Expression U (varKind L)} → E 〈 upRep 〉 ⟦ x₀:= F ⟧ ≡ E
botsub-upRep {U} {C} {K} {L} {E} {F} = let open ≡-Reasoning in 
  begin
    E 〈 upRep 〉 ⟦ x₀:= F ⟧
  ≡⟨⟨ sub-comp₂ E ⟩⟩
    E ⟦ x₀:= F •₂ upRep ⟧
  ≡⟨ sub-idOp ⟩
     E
  ∎
\end{code}
