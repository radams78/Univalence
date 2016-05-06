\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.OpFamily.LiftFamily (G : Grammar) where
open import Data.List
open import Prelims
open Grammar G
open import Grammar.OpFamily.PreOpFamily G
open import Grammar.OpFamily.Lifting G
\end{code}
}

\subsubsection{Pre-family with Lifting}

A \emph{pre-family with lifting} is a pre-family with a lifting operation that satisfies, for every operation $\sigma : U \rightarrow V$:
\begin{align*}
(\sigma , K) (x_0) & \equiv x_0 \\
(\sigma , K) (x) & \equiv \sigma(x) & (x \in U)
\end{align*}

\begin{code}
record IsLiftFamily (F : PreOpFamily) (L : Lifting F) : Set₁ where
  open PreOpFamily F
  open Lifting L
  field
    liftOp-x₀ : ∀ {U} {V} {K} {σ : Op U V} → 
      apV (liftOp K σ) x₀ ≡ var x₀
    liftOp-↑ : ∀ {U} {V} {K} {L} {σ : Op U V} (x : Var U L) →
      apV (liftOp K σ) (↑ x) ≡ ap up (apV σ x)
\end{code}

\AgdaHide{
\begin{code}
record LiftFamily : Set₂ where
  field
    preOpFamily : PreOpFamily
    lifting : Lifting preOpFamily
    isLiftFamily : IsLiftFamily preOpFamily lifting
  open PreOpFamily preOpFamily public
  open Lifting lifting public
  open IsLiftFamily isLiftFamily public
\end{code}
}

\begin{lemma}
In any pre-family with lifting:
\begin{enumerate}
\item
$(\id{V} , K) \sim \id{(V , K)}$
\item
$\id{V}^{K_1, \ldots, K_n} \sim \id{(V , K_1 , \cdots , K_n)}$
%TODO Better notation?
\item
$E[\id{V}] \equiv E$
\end{enumerate}
\end{lemma}

\begin{code}
  liftOp-idOp : ∀ {V} {K} → liftOp K (idOp V) ∼op idOp (V , K)
\end{code}

\AgdaHide{
\begin{code}
  liftOp-idOp {V} {K} x₀ = let open ≡-Reasoning in
    begin
      apV (liftOp K (idOp V)) x₀
    ≡⟨ liftOp-x₀ ⟩
      var x₀
    ≡⟨⟨ apV-idOp x₀ ⟩⟩
      apV (idOp (V , K)) x₀
    ∎
  liftOp-idOp {V} {K} {L} (↑ x) = let open ≡-Reasoning in 
    begin 
      apV (liftOp K (idOp V)) (↑ x)
    ≡⟨ liftOp-↑ x ⟩
      ap up (apV (idOp V) x)
    ≡⟨ cong (ap up) (apV-idOp x) ⟩
      ap up (var x)              
    ≡⟨ apV-up ⟩
      var (↑ x)
    ≡⟨⟨ apV-idOp (↑ x) ⟩⟩
      (apV (idOp (V , K)) (↑ x)
    ∎)
\end{code}
}
 
\begin{code}      
  liftOp'-idOp : ∀ {V} A → 
    liftOp' A (idOp V) ∼op idOp (extend V A)
\end{code}

\AgdaHide{
\begin{code}
  liftOp'-idOp [] = ∼-refl
  liftOp'-idOp {V} (K ∷ A) = let open EqReasoning (OP (extend (V , K) A) (extend (V , K) A)) in 
    begin
      liftOp' A (liftOp K (idOp V))
    ≈⟨ liftOp'-cong A liftOp-idOp ⟩
      liftOp' A (idOp (V , K))
    ≈⟨ liftOp'-idOp A ⟩
      idOp (extend (V , K) A)
    ∎
\end{code}
}

\begin{code}
  ap-idOp : ∀ {V} {C} {K} {E : Subexpression V C K} → 
    ap (idOp V) E ≡ E
\end{code}

\AgdaHide{
\begin{code}
  ap-idOp {E = var x} = apV-idOp x
  ap-idOp {E = app c EE} = cong (app c) ap-idOp
  ap-idOp {E = out} = refl
  ap-idOp {E = _,,_ {A = A} E F} = cong₂ _,,_ (trans (ap-congl E (liftOp'-idOp A)) ap-idOp) ap-idOp
\end{code}
}
