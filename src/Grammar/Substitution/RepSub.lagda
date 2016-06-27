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

open OpFamily replacement using () renaming (liftOp'' to liftOp''R; liftOp''' to liftOp'''R)
open PreOpFamily pre-substitution
open Lifting SUB↑
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

rep↑-is-sub↑ : ∀ {U} {V} {ρ : Rep U V} {K} → 
  rep2sub (rep↑ K ρ) ∼ sub↑ K (rep2sub ρ)
\end{code}

\AgdaHide{
\begin{code}
rep↑-is-sub↑ x₀ = refl
rep↑-is-sub↑ (↑ _) = refl
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
liftOp'-is-liftOp' : ∀ {U} {V} {ρ : Rep U V} {A} → 
  rep2sub (liftOp''R A ρ) ∼ liftOp'' A (rep2sub ρ)
\end{code}

\AgdaHide{
\begin{code}
liftOp'-is-liftOp' {ρ = ρ} {A = []} = ∼-refl {σ = rep2sub ρ}
liftOp'-is-liftOp' {U} {V} {ρ} {K ∷ A} = let open EqReasoning (OP _ _) in 
  begin
    rep2sub (liftOp''R A (rep↑ K ρ))
  ≈⟨ liftOp'-is-liftOp' {A = A} ⟩
    liftOp'' A (rep2sub (rep↑ K ρ))
  ≈⟨ liftOp''-cong A rep↑-is-sub↑ ⟩
    liftOp'' A (sub↑ K (rep2sub ρ))
  ∎

postulate liftOp'''-is-liftOp''' : ∀ {U} {V} {ρ : Rep U V} A → 
                                 rep2sub (liftOp'''R A ρ) ∼ liftOp''' A (rep2sub ρ)
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
rep-is-sub out = refl
rep-is-sub {U} {V} (_,,_ {A = A} E F) {ρ} = cong₂ _,,_ 
  (let open ≡-Reasoning {A = Abstraction V A} in
  begin 
    E 〈 liftOp'''R A ρ 〉
  ≡⟨ rep-is-sub E ⟩
    E ⟦ (λ K x → var (liftOp'''R A ρ K x)) ⟧ 
  ≡⟨ ap-congl E (liftOp'''-is-liftOp''' A) ⟩
    E ⟦ liftOp''' A (λ K x → var (ρ K x)) ⟧
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
