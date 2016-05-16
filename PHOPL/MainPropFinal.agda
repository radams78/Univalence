module PHOPL.MainPropFinal where
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import Prelims
open import PHOPL
open import PHOPL.Rules
open import PHOPL.PathSub
open import PHOPL.Close
open import PHOPL.Red
open import PHOPL.Neutral
open import PHOPL.Meta
open import PHOPL.Computable
open import PHOPL.SubC

Computable-Substitution : ∀ U V (σ : Sub U V) Γ Δ M A → 
  σ ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → E Δ (close A) (M ⟦ σ ⟧)
Computable-Substitution _ _ _ _ _ _ _ σ∶Γ⇒Δ (varR x _) _ = proj₁ σ∶Γ⇒Δ x
Computable-Substitution _ V _ _ Δ .⊥ .Ω _ (⊥R _) Δvalid = ⊥-E {V} {Δ} Δvalid
Computable-Substitution U V σ Γ Δ .(φ ⊃ ψ) .Ω σ∶Γ⇒Δ (impR {φ = φ} {ψ} Γ⊢φ∶Ω Γ⊢ψ∶Ω) Δvalid = ⊃-E 
  (Computable-Substitution U V σ Γ Δ φ Ω σ∶Γ⇒Δ Γ⊢φ∶Ω Δvalid) 
  (Computable-Substitution U V σ Γ Δ ψ Ω σ∶Γ⇒Δ Γ⊢ψ∶Ω Δvalid)
Computable-Substitution U V σ Γ Δ .(appT M N) .B σ∶Γ⇒Δ (appR {M = M} {N} {A} {B} Γ⊢M∶A⇒B Γ⊢N∶A) Δvalid = appT-E 
  Δvalid
  (Computable-Substitution U V σ Γ Δ M (A ⇛ B) σ∶Γ⇒Δ Γ⊢M∶A⇒B Δvalid) 
  (Computable-Substitution U V σ Γ Δ N A σ∶Γ⇒Δ Γ⊢N∶A Δvalid)
Computable-Substitution U V σ Γ Δ .(ΛT A M) .(A ⇛ B) σ∶Γ⇒Δ (ΛR {A = A} {M} {B} Γ,A⊢M∶B) Δvalid = func-E (λ W Θ ρ N Θvalid ρ∶Δ⇒RΘ N∈EΘA → 
  expand-E (subst₂ (E Θ) (close-rep B) 
  (let open ≡-Reasoning in 
  begin
    M ⟦ x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ ⟧
  ≡⟨ sub-comp M ⟩ 
    M ⟦ Sub↑ -Term σ ⟧ ⟦ x₀:= N •₂ Rep↑ -Term ρ ⟧
  ≡⟨ sub-comp₂ (M ⟦ Sub↑ -Term σ ⟧) ⟩
    M ⟦ Sub↑ -Term σ ⟧ 〈 Rep↑ -Term ρ 〉 ⟦ x₀:= N ⟧
  ∎) 
  (Computable-Substitution (U , -Term) W 
    (x₀:= N •₂ Rep↑ -Term ρ • Sub↑ -Term σ) (Γ ,T A) Θ M (B ⇑) 
    (compC (comp₂C (botsubC (subst (λ T → E Θ T N) 
      (let open ≡-Reasoning in 
      begin
        close A
      ≡⟨⟨ close-sub A ⟩⟩
        close (A ⟦ σ ⟧)
      ≡⟨⟨ close-rep (A ⟦ σ ⟧) ⟩⟩
        close (A ⟦ σ ⟧ 〈 ρ 〉)
      ∎) 
      N∈EΘA)) (Rep↑-typed ρ∶Δ⇒RΘ)) (Sub↑C σ∶Γ⇒Δ)) Γ,A⊢M∶B Θvalid)))
