\begin{code}
open import Grammar.Base

module Grammar.Substitution.RepSub (G : Grammar) where
open import Data.List
open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G
open import Grammar.Substitution.PreOpFamily G
open import Grammar.Substitution.Lifting G

open OpFamily REP using () renaming (liftsOp to liftsOpR)
open PreOpFamily pre-substitution
open Lifting LIFTSUB
\end{code}

We can consider replacement to be a special case of substitution.  That is,
we can identify every replacement $\rho : U \rightarrow V$ with the substitution
that maps $x$ to $\rho(x)$.  
\begin{lemma}
Let $\rho$ be a replacement $U \rightarrow V$.
\begin{enumerate}
\item
The replacement $(\rho , K)$ and the substitution $(\rho , K)$ are equal.
\item
The replacement $\uparrow$ and the substitution $\uparrow$ are equal.
\item
The replacement $\rho^A$ and the substitution $\rho^A$ are equal.
\item
$ E \langle \rho \rangle \equiv E [ \rho ] $
\item
Hence $ E \langle \uparrow \rangle \equiv E [ \uparrow ]$.
\item
Substitution is a pre-family with lifting.
\end{enumerate}
\end{lemma}

\begin{code}
rep2sub : ∀ {U} {V} → Rep U V → Sub U V
rep2sub ρ K x = var (ρ K x)

liftRep-is-liftSub : ∀ {U} {V} {ρ : Rep U V} {K} → 
  rep2sub (liftRep K ρ) ∼ liftSub K (rep2sub ρ)
\end{code}

\AgdaHide{
\begin{code}
liftRep-is-liftSub x₀ = refl
liftRep-is-liftSub (↑ _) = refl
\end{code}
}

\begin{code}
up-is-up : ∀ {V} {K} → rep2sub (upRep {V} {K}) ∼ upSub
\end{code}

\AgdaHide{
\begin{code}
up-is-up _ = refl
\end{code}
}

\begin{code}
liftsOp-is-liftsOp : ∀ {U} {V} {ρ : Rep U V} {A} → 
  rep2sub (liftsOpR  A ρ) ∼ liftsOp A (rep2sub ρ)
\end{code}

\AgdaHide{
\begin{code}
liftsOp-is-liftsOp {ρ = ρ} {A = []} = ∼-refl {σ = rep2sub ρ}
liftsOp-is-liftsOp {U} {V} {ρ} {K ∷ A} = let open EqReasoning (OP _ _) in 
  begin
    rep2sub (liftsOpR A (liftRep K ρ))
  ≈⟨ liftsOp-is-liftsOp {A = A} ⟩
    liftsOp A (rep2sub (liftRep K ρ))
  ≈⟨ liftsOp-cong A liftRep-is-liftSub ⟩
    liftsOp A (liftSub K (rep2sub ρ))
  ∎
\end{code}
}

\begin{code}
rep-is-sub : ∀ {U} {V} {K} {C} (E : Subexpression U K C) {ρ : Rep U V} → 
  E 〈 ρ 〉 ≡ E ⟦ rep2sub ρ ⟧
\end{code}

\AgdaHide{
\begin{code}
rep-is-sub (var _) = refl
rep-is-sub (app c E) = cong (app c) (rep-is-sub E)
rep-is-sub [] = refl
rep-is-sub {U} {V} (_∷_ {A = SK A _} E F) {ρ} = cong₂ _∷_ 
  (let open ≡-Reasoning {A = Subexpression (extend V A) _ _} in
  begin 
    E 〈 liftsOpR A ρ 〉
  ≡⟨ rep-is-sub E ⟩
    E ⟦ (λ K x → var (liftsOpR A ρ K x)) ⟧ 
  ≡⟨ ap-congl (liftsOp-is-liftsOp {A = A}) E ⟩
    E ⟦ liftsOp A (λ K x → var (ρ K x)) ⟧
  ∎)
  (rep-is-sub F)
\end{code}
}

\begin{code}
up-is-up' : ∀ {V} {C} {K} {L} {E : Subexpression V C K} → 
  E 〈 upRep {K = L} 〉 ≡ E ⟦ upSub ⟧
\end{code}

\AgdaHide{
\begin{code}
up-is-up' {E = E} = rep-is-sub E
\end{code}
}
