\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.Substitution.Botsub (G : Grammar) where
open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G
open import Grammar.Substitution.PreOpFamily G
open import Grammar.Substitution.Lifting G
open import Grammar.Substitution.LiftFamily G
open import Grammar.Substitution.OpFamily G
\end{code}
}

\subsubsection{Substitution for an Individual Variable}

Let $E$ be an expression of kind $K$ over $V$.  Then we write $[x_0 := E]$ for the following substitution
$(V , K) \Rightarrow V$:

\begin{code}
x₀:= : ∀ {V} {K} → Expression V (varKind K) → Sub (V , K) V
x₀:= E _ x₀ = E
x₀:= E K₁ (↑ x) = var x
\end{code}

\begin{lemma}$ $
\begin{enumerate}
\item
$ \rho \bullet_1 [x_0 := E] \sim [x_0 := E \langle \rho \rangle] \bullet_2 (\rho , K) $
\item
$ \sigma \bullet [x_0 := E] \sim [x_0 := E[\sigma]] \bullet (\sigma , K) $
\item
$ E [ \uparrow ] [ x_0 := F ] \equiv E$
\end{enumerate}
\end{lemma}

\begin{code}
open LiftFamily

botsub-upGEN : ∀ {F} {V} {K} {E : Expression V (varKind K)} (circ : Composition proto-substitution F proto-substitution) →
  Composition.circ circ (x₀:= E) (up F) ∼ idSub V
botsub-upGEN {F} {V} {K} {E} circ x = let open ≡-Reasoning in 
  begin
    (Composition.circ circ (x₀:= E) (up F)) _ x
  ≡⟨ Composition.apV-circ circ ⟩
    apV F (up F) x ⟦ x₀:= E ⟧
  ≡⟨ sub-congl (apV-up F) ⟩
    var x
  ∎

comp-botsubGEN : ∀ {F} {U} {V} {K} {E : Expression U (varKind K)} (circ₁ : Composition F proto-substitution proto-substitution) (circ₂ : Composition proto-substitution F proto-substitution)
  {σ : Op F U V} →
  Composition.circ circ₁ σ (x₀:= E) ∼ Composition.circ circ₂ (x₀:= (ap F σ E)) (liftOp F K σ)
comp-botsubGEN {F} {U} {V} {K} {E} circ₁ circ₂ {σ} x₀ = let open ≡-Reasoning in 
  begin
    (Composition.circ circ₁ σ (x₀:= E)) _ x₀
  ≡⟨ Composition.apV-circ circ₁ ⟩
    ap F σ E
  ≡⟨⟨ sub-congl (liftOp-x₀ F) ⟩⟩
    (apV F (liftOp F K σ) x₀) ⟦ x₀:= (ap F σ E) ⟧
  ≡⟨⟨ Composition.apV-circ circ₂ ⟩⟩
    (Composition.circ circ₂ (x₀:= (ap F σ E)) (liftOp F K σ)) _ x₀
  ∎
comp-botsubGEN {F} {U} {V} {K} {E} circ₁ circ₂ {σ} (↑ x) = let open ≡-Reasoning in 
  begin
    (Composition.circ circ₁ σ (x₀:= E)) _ (↑ x)
  ≡⟨ Composition.apV-circ circ₁ ⟩
    apV F σ x
  ≡⟨⟨ sub-idOp ⟩⟩
    apV F σ x ⟦ idSub V ⟧
  ≡⟨⟨ sub-congr (apV F σ x) (botsub-upGEN circ₂) ⟩⟩
    apV F σ x ⟦ Composition.circ circ₂ (x₀:= (ap F σ E)) (up F) ⟧
  ≡⟨ Composition.ap-circ circ₂ (apV F σ x) ⟩
    ap F (up F) (apV F σ x) ⟦ x₀:= (ap F σ E) ⟧
  ≡⟨⟨ sub-congl (liftOp-↑ F x) ⟩⟩
    (apV F (liftOp F K σ) (↑ x)) ⟦ x₀:= (ap F σ E) ⟧
  ≡⟨⟨ Composition.apV-circ circ₂ ⟩⟩
    (Composition.circ circ₂ (x₀:= (ap F σ E)) (liftOp F K σ)) _ (↑ x)
  ∎

comp₁-botsub : ∀ {U} {V} {K} {E : Expression U (varKind K)} {ρ : Rep U V} →
  ρ •₁ (x₀:= E) ∼ (x₀:= (E 〈 ρ 〉)) •₂ Rep↑ K ρ
\end{code}

\AgdaHide{
\begin{code}
comp₁-botsub {U} {V} {K} {E} {ρ} = ?
--comp₁-botsub x₀ = refl
--comp₁-botsub (↑ _) = refl

comp₁-botsub' : ∀ {U} {V} {C} {K} {L} (E : Subexpression (U , K) C L) {F : Expression U (varKind K)} {ρ : Rep U V} →
  E ⟦ x₀:= F ⟧ 〈 ρ 〉 ≡ E 〈 Rep↑ K ρ 〉 ⟦ x₀:= (F 〈 ρ 〉) ⟧
comp₁-botsub' E = ap-circ-sim COMP₁ COMP₂ comp₁-botsub E
\end{code}
}

\begin{code}
comp-botsub : ∀ {U} {V} {K} {E : Expression U (varKind K)} {σ : Sub U V} →
  σ • (x₀:= E) ∼ (x₀:= (E ⟦ σ ⟧)) • Sub↑ K σ
\end{code}

\AgdaHide{
\begin{code}
comp-botsub x₀ = refl
comp-botsub {U} {V} {K} {E} {σ} {L} (↑ x) = let open ≡-Reasoning in 
  begin
    (σ • x₀:= E) _ (↑ x)
  ≡⟨⟩
    σ _ x
  ≡⟨⟨ sub-idOp ⟩⟩
    σ _ x ⟦ idSub V ⟧
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
\end{code}
}

\begin{code}
botsub-upRep : ∀ {U} {C} {K} {L}
  {E : Subexpression U C K} {F : Expression U (varKind L)} → 
  E 〈 upRep 〉 ⟦ x₀:= F ⟧ ≡ E
\end{code}

\AgdaHide{
\begin{code}
botsub-upRep {U} {C} {K} {L} {E} {F} = let open ≡-Reasoning in 
  begin
    E 〈 upRep 〉 ⟦ x₀:= F ⟧
  ≡⟨⟨ sub-comp₂ E ⟩⟩
    E ⟦ x₀:= F •₂ upRep ⟧
  ≡⟨ sub-idOp ⟩
     E
  ∎
\end{code}
}
