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

comp-botsubGEN : ∀ {F} {U} {V} {K} {E : Expression U (varKind K)} 
  (circ₁ : Composition F proto-substitution proto-substitution) 
  (circ₂ : Composition proto-substitution F proto-substitution)
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

comp-botsubGEN' : ∀ {F} {U} {V} {K} {C} {L} 
  {E : Expression U (varKind K)} {E' : Subexpression (U , K) C L} {σ : Op F U V} →
  Composition F proto-substitution proto-substitution →
  Composition proto-substitution F proto-substitution →
  ap F σ (E' ⟦ x₀:= E ⟧) ≡ (ap F (liftOp F K σ) E') ⟦ x₀:= (ap F σ E) ⟧
comp-botsubGEN' {E' = E'} circ₁ circ₂ = ap-circ-sim circ₁ circ₂ (comp-botsubGEN circ₁ circ₂) E'

comp₁-botsub' : ∀ {U} {V} {C} {K} {L} (E : Subexpression (U , K) C L) {F : Expression U (varKind K)} {ρ : Rep U V} →
  E ⟦ x₀:= F ⟧ 〈 ρ 〉 ≡ E 〈 Rep↑ K ρ 〉 ⟦ x₀:= (F 〈 ρ 〉) ⟧
\end{code}

\AgdaHide{
\begin{code}
comp₁-botsub' E = comp-botsubGEN' {E' = E} COMP₁ COMP₂
\end{code}
}

\begin{code}
comp-botsub' : ∀ {U} {V} {C} {K} {L} 
  {E : Expression U (varKind K)} {σ : Sub U V} (F : Subexpression (U , K) C L) →
  F ⟦ x₀:= E ⟧ ⟦ σ ⟧ ≡ F ⟦ Sub↑ K σ ⟧ ⟦ x₀:= (E ⟦ σ ⟧) ⟧
\end{code}

\AgdaHide{
\begin{code}
comp-botsub' F = let COMP = OpFamily.COMP substitution in comp-botsubGEN' {E' = F} COMP COMP
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

postulate botsub-botsub' : ∀ {V} {K} {L} (N : Expression V (varKind K)) (N' : Expression V (varKind L)) → x₀:= N' • Sub↑ L (x₀:= N) ∼ x₀:= N • x₀:= (N' ⇑)

postulate botsub-botsub : ∀ {V} {K} {L} {M} (E : Expression (V , K , L) M) F G → E ⟦ Sub↑ L (x₀:= F) ⟧ ⟦ x₀:= G ⟧ ≡ E ⟦ x₀:= (G ⇑) ⟧ ⟦ x₀:= F ⟧
\end{code}
}
