\begin{code}
open import Data.List
open import Prelims
open import Grammar
\end{code}

Let $F$, $G$ and $H$ be three families of operations.  For all $U$, $V$, $W$, let $\circ$ be a function
\[ \circ : F V W \times G U V \rightarrow H U W \]

\begin{lemma}
If $\circ$ respects lifting, then it respects repeated lifting.
\end{lemma}

\begin{code}
module Grammar.OpFamily.Composition (A : Grammar) where
  open Grammar.Grammar A
  open LiftFamily

  record Composition (F G H : LiftFamily) : Set where
    field
      circ : ∀ {U} {V} {W} → Op F V W → Op G U V → Op H U W
      liftOp-circ : ∀ {U V W K σ ρ} → _∼op_ H (liftOp H K (circ {U} {V} {W} σ ρ)) (circ (liftOp F K σ) (liftOp G K ρ))
      apV-circ : ∀ {U} {V} {W} {K} {σ} {ρ} {x : Var U K} → apV H (circ {U} {V} {W} σ ρ) x ≡ ap F σ (apV G ρ x)

    liftOp'-circ : ∀ {U V W} A {σ ρ} → _∼op_ H (liftOp' H A (circ {U} {V} {W} σ ρ)) (circ (liftOp' F A σ) (liftOp' G A ρ))
    liftOp'-circ [] = ∼-refl H
    liftOp'-circ {U} {V} {W} (K ∷ A) {σ} {ρ} = let open EqReasoning (OP H _ _) in 
      begin
        liftOp' H A (liftOp H K (circ σ ρ))
      ≈⟨ liftOp'-cong H A liftOp-circ ⟩
        liftOp' H A (circ (liftOp F K σ) (liftOp G K ρ))
      ≈⟨ liftOp'-circ A ⟩
        circ (liftOp' F A (liftOp F K σ)) (liftOp' G A (liftOp G K ρ))
      ∎

    ap-circ : ∀ {U V W C K} (E : Subexpression U C K) {σ ρ} → ap H (circ {U} {V} {W} σ ρ) E ≡ ap F σ (ap G ρ E)
    ap-circ (var _) = apV-circ
    ap-circ (app c E) = cong (app c) (ap-circ E)
    ap-circ out = refl
    ap-circ (_,,_ {A = A} E E') {σ} {ρ} = cong₂ _,,_
      (let open ≡-Reasoning in 
      begin
        ap H (liftOp' H A (circ σ ρ)) E
      ≡⟨ ap-congl H E (liftOp'-circ A) ⟩
        ap H (circ (liftOp' F A σ) (liftOp' G A ρ)) E
      ≡⟨ ap-circ E ⟩
        ap F (liftOp' F A σ) (ap G (liftOp' G A ρ) E)
      ∎) 
      (ap-circ E')

    circ-cong : ∀ {U V W} {σ σ' : Op F V W} {ρ ρ' : Op G U V} → _∼op_ F σ σ' → _∼op_ G ρ ρ' → _∼op_ H (circ σ ρ) (circ σ' ρ')
    circ-cong {U} {V} {W} {σ} {σ'} {ρ} {ρ'} σ∼σ' ρ∼ρ' x = let open ≡-Reasoning in 
      begin
        apV H (circ σ ρ) x
      ≡⟨ apV-circ ⟩
        ap F σ (apV G ρ x)
      ≡⟨ ap-cong F σ∼σ' (ρ∼ρ' x) ⟩
        ap F σ' (apV G ρ' x)
      ≡⟨⟨ apV-circ ⟩⟩
        apV H (circ σ' ρ') x
      ∎
\end{code}
