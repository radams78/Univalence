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
(\sigma , K) (x) & \equiv \sigma(x)[ \uparrow ] & (x \in U)
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

\begin{lemma}
In any pre-family with lifting:
\begin{enumerate}
\item
$(\id{V} , K) \sim \id{(V , K)}$
\item
$\id{V}^{K_1, \ldots, K_n} \sim \id{(V , K_1 , \cdots , K_n)}$
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
  liftsOp-idOp : ∀ {V} A → 
    liftsOp A (idOp V) ∼op idOp (extend LIST V A)
\end{code}

\AgdaHide{
\begin{code}
  liftsOp-idOp [] = ∼-refl
  liftsOp-idOp {V} (K ∷ A) = let open EqReasoning (OP (extend LIST V (K ∷ A)) (extend LIST V (K ∷ A))) in 
    begin
      liftsOp A (liftOp K (idOp V))
    ≈⟨ liftsOp-cong A liftOp-idOp ⟩
      liftsOp A (idOp (V , K))
    ≈⟨ liftsOp-idOp A ⟩
      idOp (extend LIST V (K ∷ A))
    ∎
\end{code}
}

\begin{code}
  ap-idOp : ∀ {V} {C} {K} {E : Subexp V C K} → ap (idOp V) E ≡ E
\end{code}

\AgdaHide{
\begin{code}
  ap-idOp {E = var x} = apV-idOp x
  ap-idOp {E = app c EE} = cong (app c) ap-idOp
  ap-idOp {E = []} = refl
  ap-idOp {V} {E = _∷_ {A = SK A _} E F} =
    let open ≡-Reasoning in 
    begin
      ap (liftsOp A (idOp V)) E ∷ ap (idOp V) F
    ≡⟨ cong₂ _∷_ (ap-congl (liftsOp-idOp A) E) ap-idOp ⟩
       ap (idOp (extend LIST V A)) E ∷ F
    ≡⟨ cong (λ x → x ∷ F) ap-idOp ⟩
       E ∷ F
    ∎

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

