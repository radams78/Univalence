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

\AgdaHide{
\begin{code}
botSub : ∀ {V} {A} → ExpList V A → Sub (snoc-extend V A) V
botSub {A = []} _ _ x = var x
botSub {A = _ snoc _} (_ snoc E) _ x₀ = E
botSub {A = _ snoc _} (EE snoc _) L (↑ x) = botSub EE L x
\end{code}
}

\begin{code}
infix 65 x₀:=_
x₀:=_ : ∀ {V} {K} → Expression V (varKind K) → Sub (V , K) V
x₀:= E = botSub ([] snoc E)
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

botSub-up' : ∀ {F} {V} {K} {E : Expression V (varKind K)} (circ : Composition SubLF F SubLF) →
  Composition.circ circ (x₀:= E) (up F) ∼ idSub V
botSub-up' {F} {V} {K} {E} circ x = let open ≡-Reasoning in 
  begin
    (Composition.circ circ (x₀:= E) (up F)) _ x
  ≡⟨ Composition.apV-circ circ ⟩
    apV F (up F) x ⟦ x₀:= E ⟧
  ≡⟨ sub-congl (apV-up F) ⟩
    var x
  ∎

botSub-up : ∀ {F} {V} {K} {C} {L} {E : Expression V (varKind K)} (circ : Composition SubLF F SubLF) {E' : Subexpression V C L} →
  ap F (up F) E' ⟦ x₀:= E ⟧ ≡ E'
botSub-up {F} {V} {K} {C} {L} {E} circ {E'} = let open ≡-Reasoning in
  begin
    ap F (up F) E' ⟦ x₀:= E ⟧
  ≡⟨⟨ Composition.ap-circ circ E' ⟩⟩
    E' ⟦ Composition.circ circ (x₀:= E) (up F) ⟧
  ≡⟨ sub-congr (botSub-up' circ) E' ⟩
    E' ⟦ idSub V ⟧
  ≡⟨ sub-idOp ⟩
    E'
  ∎

circ-botSub' : ∀ {F} {U} {V} {K} {E : Expression U (varKind K)} 
  (circ₁ : Composition F SubLF SubLF) 
  (circ₂ : Composition SubLF F SubLF)
  {σ : Op F U V} →
  Composition.circ circ₁ σ (x₀:= E) ∼ Composition.circ circ₂ (x₀:= (ap F σ E)) (liftOp F K σ)
circ-botSub' {F} {U} {V} {K} {E} circ₁ circ₂ {σ} x₀ = let open ≡-Reasoning in 
  begin
    (Composition.circ circ₁ σ (x₀:= E)) _ x₀
  ≡⟨ Composition.apV-circ circ₁ ⟩
    ap F σ E
  ≡⟨⟨ sub-congl (liftOp-x₀ F) ⟩⟩
    (apV F (liftOp F K σ) x₀) ⟦ x₀:= (ap F σ E) ⟧
  ≡⟨⟨ Composition.apV-circ circ₂ ⟩⟩
    (Composition.circ circ₂ (x₀:= (ap F σ E)) (liftOp F K σ)) _ x₀
  ∎
circ-botSub' {F} {U} {V} {K} {E} circ₁ circ₂ {σ} (↑ x) = let open ≡-Reasoning in 
  begin
    (Composition.circ circ₁ σ (x₀:= E)) _ (↑ x)
  ≡⟨ Composition.apV-circ circ₁ ⟩
    apV F σ x
  ≡⟨⟨ sub-idOp ⟩⟩
    apV F σ x ⟦ idSub V ⟧
  ≡⟨⟨ sub-congr (botSub-up' circ₂) (apV F σ x) ⟩⟩
    apV F σ x ⟦ Composition.circ circ₂ (x₀:= (ap F σ E)) (up F) ⟧
  ≡⟨ Composition.ap-circ circ₂ (apV F σ x) ⟩
    ap F (up F) (apV F σ x) ⟦ x₀:= (ap F σ E) ⟧
  ≡⟨⟨ sub-congl (liftOp-↑ F x) ⟩⟩
    (apV F (liftOp F K σ) (↑ x)) ⟦ x₀:= (ap F σ E) ⟧
  ≡⟨⟨ Composition.apV-circ circ₂ ⟩⟩
    (Composition.circ circ₂ (x₀:= (ap F σ E)) (liftOp F K σ)) _ (↑ x)
  ∎

circ-botSub : ∀ {F} {U} {V} {K} {C} {L} 
  {E : Expression U (varKind K)} {E' : Subexpression (U , K) C L} {σ : Op F U V} →
  Composition F SubLF SubLF →
  Composition SubLF F SubLF →
  ap F σ (E' ⟦ x₀:= E ⟧) ≡ (ap F (liftOp F K σ) E') ⟦ x₀:= (ap F σ E) ⟧
circ-botSub {E' = E'} circ₁ circ₂ = ap-circ-sim circ₁ circ₂ (circ-botSub' circ₁ circ₂) E'

compRS-botSub : ∀ {U} {V} {C} {K} {L} (E : Subexpression (U , K) C L) {F : Expression U (varKind K)} {ρ : Rep U V} →
  E ⟦ x₀:= F ⟧ 〈 ρ 〉 ≡ E 〈 liftRep K ρ 〉 ⟦ x₀:= (F 〈 ρ 〉) ⟧
--TODO Common pattern with liftRep-botSub₃
\end{code}

\AgdaHide{
\begin{code}
compRS-botSub E = circ-botSub {E' = E} COMPRS COMPSR
\end{code}
}

\begin{code}
comp-botSub : ∀ {U} {V} {C} {K} {L} 
  {E : Expression U (varKind K)} {σ : Sub U V} (F : Subexpression (U , K) C L) →
   F ⟦ x₀:= E ⟧ ⟦ σ ⟧ ≡ F ⟦ liftSub K σ ⟧ ⟦ x₀:= (E ⟦ σ ⟧) ⟧
\end{code}

\AgdaHide{
\begin{code}
comp-botSub F = let COMP = OpFamily.COMP SUB in circ-botSub {E' = F} COMP COMP
\end{code}
}

\begin{code}
botSub-upRep : ∀ {U} {C} {K} {L}
  (E : Subexpression U C K) {F : Expression U (varKind L)} → 
  E 〈 upRep 〉 ⟦ x₀:= F ⟧ ≡ E
\end{code}

\AgdaHide{
\begin{code}
botSub-upRep _ = botSub-up COMPSR

botSub-botSub' : ∀ {V} {K} {L} (N : Expression V (varKind K)) (N' : Expression V (varKind L)) → x₀:= N' • liftSub L (x₀:= N) ∼ x₀:= N • x₀:= (N' ⇑)
botSub-botSub' N N' x₀ = sym (botSub-upRep N')
botSub-botSub' N N' (↑ x₀) = botSub-upRep N
botSub-botSub' N N' (↑ (↑ x)) = refl

botSub-botSub : ∀ {V} {K} {L} {M} (E : Expression (V , K , L) M) F G → E ⟦ liftSub L (x₀:= F) ⟧ ⟦ x₀:= G ⟧ ≡ E ⟦ x₀:= (G ⇑) ⟧ ⟦ x₀:= F ⟧
botSub-botSub {V} {K} {L} {M} E F G = let COMP = OpFamily.COMP SUB in ap-circ-sim COMP COMP (botSub-botSub' F G) E

x₂:=_,x₁:=_,x₀:=_ : ∀ {V} {K1} {K2} {K3} → Expression V (varKind K1) → Expression V (varKind K2) → Expression V (varKind K3) → Sub (V , K1 , K2 , K3) V
x₂:=_,x₁:=_,x₀:=_ M1 M2 M3 = botSub ([] snoc M1 snoc M2 snoc M3)

postulate botSub-upRep₃ : ∀ {V} {K1} {K2} {K3} {L} {M : Expression V L} 
                          {N1 : Expression V (varKind K1)} {N2 : Expression V (varKind K2)} {N3 : Expression V (varKind K3)} →
                          M ⇑ ⇑ ⇑ ⟦ x₂:= N1 ,x₁:= N2 ,x₀:= N3 ⟧ ≡ M

--TODO Definition for Expression varKind
botSub₃-liftRep₃' : ∀ {U} {V} {K2} {K1} {K0}
  {M2 : Expression U (varKind K1)} {M1 : Expression U (varKind K2)} {M0 : Expression U (varKind K0)} {ρ : Rep U V} →
  (x₂:= M2 〈 ρ 〉 ,x₁:= M1 〈 ρ 〉 ,x₀:= M0 〈 ρ 〉) •SR liftRep _ (liftRep _ (liftRep _ ρ))
  ∼ ρ •RS (x₂:= M2 ,x₁:= M1 ,x₀:= M0)
botSub₃-liftRep₃' x₀ = refl
botSub₃-liftRep₃' (↑ x₀) = refl
botSub₃-liftRep₃' (↑ (↑ x₀)) = refl 
botSub₃-liftRep₃' (↑ (↑ (↑ x))) = refl

botSub₃-liftRep₃ : ∀ {U} {V} {K2} {K1} {K0} {L}
  {M2 : Expression U (varKind K2)} {M1 : Expression U (varKind K1)} {M0 : Expression U (varKind K0)} {ρ : Rep U V} (N : Expression (U , K2 , K1 , K0) L) →
  N 〈 liftRep _ (liftRep _ (liftRep _ ρ)) 〉 ⟦ x₂:= M2 〈 ρ 〉 ,x₁:= M1 〈 ρ 〉 ,x₀:= M0 〈 ρ 〉 ⟧
  ≡ N ⟦ x₂:= M2 ,x₁:= M1 ,x₀:= M0 ⟧ 〈 ρ 〉
botSub₃-liftRep₃ {M2 = M2} {M1} {M0} {ρ} N = let open ≡-Reasoning in
              begin
                N 〈 liftRep _ (liftRep _ (liftRep _ ρ)) 〉 ⟦ x₂:= M2 〈 ρ 〉 ,x₁:= M1 〈 ρ 〉 ,x₀:= M0 〈 ρ 〉 ⟧
              ≡⟨⟨ sub-compSR N ⟩⟩
                N ⟦ (x₂:= M2 〈 ρ 〉 ,x₁:= M1 〈 ρ 〉 ,x₀:= M0 〈 ρ 〉) •SR liftRep _ (liftRep _ (liftRep _ ρ)) ⟧
              ≡⟨ sub-congr botSub₃-liftRep₃' N ⟩
                N ⟦ ρ •RS (x₂:= M2 ,x₁:= M1 ,x₀:= M0) ⟧
              ≡⟨ sub-compRS N ⟩
                N ⟦ x₂:= M2 ,x₁:= M1 ,x₀:= M0 ⟧ 〈 ρ 〉
              ∎
--TODO General lemma for this
--TODO Deletable?
\end{code}
}
