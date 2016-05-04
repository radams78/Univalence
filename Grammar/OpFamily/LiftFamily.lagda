\begin{code}
open import Data.List
open import Prelims
open import Grammar.Base

module Grammar.OpFamily.LiftFamily (G : Grammar) where
open Grammar G

record IsLiftFamily (F : PreOpFamily) (L : PreOpFamily.Lifting F) : Set₁ where
  open PreOpFamily F
  open Lifting L
  field
    liftOp-x₀ : ∀ {U} {V} {K} {σ : Op U V} → apV (liftOp K σ) x₀ ≡ var x₀
    liftOp-↑ : ∀ {U} {V} {K} {L} {σ : Op U V} (x : Var U L) →
      apV (liftOp K σ) (↑ x) ≡ ap up (apV σ x)

  liftOp-idOp : ∀ {V} {K} → liftOp K (idOp V) ∼op idOp (V , K)
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
       
  liftOp'-idOp : ∀ {V} A → liftOp' A (idOp V) ∼op idOp (extend' V A)
  liftOp'-idOp [] = ∼-refl
  liftOp'-idOp {V} (K ∷ A) = let open EqReasoning (OP (extend' (V , K) A) (extend' (V , K) A)) in 
    begin
      liftOp' A (liftOp K (idOp V))
    ≈⟨ liftOp'-cong A liftOp-idOp ⟩
      liftOp' A (idOp (V , K))
    ≈⟨ liftOp'-idOp A ⟩
      idOp (extend' (V , K) A)
    ∎

  ap-idOp : ∀ {V} {C} {K} {E : Subexpression V C K} → ap (idOp V) E ≡ E
  ap-idOp {E = var x} = apV-idOp x
  ap-idOp {E = app c EE} = cong (app c) ap-idOp
  ap-idOp {E = out} = refl
  ap-idOp {E = _,,_ {A = A} E F} = cong₂ _,,_ (trans (ap-congl E (liftOp'-idOp A)) ap-idOp) ap-idOp
          
record LiftFamily : Set₂ where
  field
    preOpFamily : PreOpFamily
    lifting : PreOpFamily.Lifting preOpFamily
    isLiftFamily : IsLiftFamily preOpFamily lifting
  open PreOpFamily preOpFamily public
  open Lifting lifting public
  open IsLiftFamily isLiftFamily public
\end{code}
