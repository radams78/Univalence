\begin{code}
module PHOPL.MainProp where
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

postulate _∶_⇒R_ : ∀ {U} {V} → Rep U V → Context U → Context V → Set

postulate Rep↑-typed : ∀ {U} {V} {ρ : Rep U V} {K} {Γ} {Δ} {A} →
                     ρ ∶ Γ ⇒R Δ → Rep↑ K ρ ∶ (Γ , A) ⇒R (Δ , A 〈 ρ 〉)

postulate E : ∀ {V} → Context V → Type ∅ → Term V → Set

postulate Neutral-E : ∀ {V} {Γ : Context V} {A : Type V} {M : Term V} →
                    Neutral M → Γ ⊢ M ∶ A → E Γ (close A) M

var-E : ∀ {V} {Γ : Context V} {x : Var V -Term} → 
  valid Γ → E Γ (close (typeof x Γ)) (var x)
var-E {V} {Γ} {x} Γvalid = Neutral-E (var x) (varR x Γvalid)

postulate E-sub-SN : ∀ V (Γ : Context V) A M → E Γ A M → SN M

postulate ⊥-E : ∀ {V} {Γ : Context V} → valid Γ → E Γ Ω ⊥

postulate ⊃-E : ∀ {V} {Γ : Context V} {φ} {ψ} → E Γ Ω φ → E Γ Ω ψ → E Γ Ω (φ ⊃ ψ)

postulate appT-E : ∀ {V} {Γ : Context V} {M N : Term V} {A} {B} →
                 valid Γ → E Γ (A ⇛ B) M → E Γ A N → E Γ B (appT M N)

postulate func-E : ∀ {U} {Γ : Context U} {M : Term U} {A} {B} →
                   (∀ V Δ (ρ : Rep U V) (N : Term V) → valid Δ → ρ ∶ Γ ⇒R Δ → E Δ A N → E Δ B (appT (M 〈 ρ 〉) N)) →
                   E Γ (A ⇛ B) M

postulate expand-E : ∀ {V} {Γ : Context V} {A : Type V} {B : Type ∅} {M : Term (V , -Term)} {N : Term V} →
                   E Γ B (M ⟦ x₀:= N ⟧) → E Γ B (appT (ΛT A M) N)

postulate EP : ∀ {V} → Context V → Term V → Proof V → Set

postulate appP-EP : ∀ {V} {Γ : Context V} {δ ε : Proof V} {φ} {ψ} →
                  EP Γ (φ ⊃ ψ) δ → EP Γ φ ε → EP Γ ψ (appP δ ε)

postulate conv-EP : ∀ {V} {Γ : Context V} {φ ψ : Term V} {δ : Proof V} →
                    φ ≃ ψ → EP Γ φ δ → EP Γ ψ δ

postulate func-EP : ∀ {U} {Γ : Context U} {δ : Proof U} {φ} {ψ} →
                   (∀ V Δ (ρ : Rep U V) (ε : Proof V) → valid Δ → ρ ∶ Γ ⇒R Δ → EP Δ (φ 〈 ρ 〉) ε → EP Δ (ψ 〈 ρ 〉) (appP (δ 〈 ρ 〉) ε)) →
                   EP Γ (φ ⊃ ψ) δ

postulate expand-EP : ∀ {V} {Γ : Context V} {φ : Term V} {δ ε : Proof V} →
                   EP Γ φ ε → Γ ⊢ δ ∶ φ → δ ⇒R ε → SN δ → EP Γ φ δ

postulate EP-typed : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} →
                   EP Γ φ δ → Γ ⊢ δ ∶ φ

postulate EE : ∀ {V} → Context V → Equation V → Path V → Set

postulate ref-EE : ∀ {V} {Γ : Context V} {M : Term V} {A : Type V} → E Γ (close A) M → EE Γ (M ≡〈 A 〉 M) (reff M)

postulate plus-EP : ∀ {V} {Γ : Context V} {P : Path V} {φ ψ : Term V} →
                  EE Γ (φ ≡〈 Ω 〉 ψ) P → EP Γ (φ ⊃ ψ) (plus P)

postulate minus-EP : ∀ {V} {Γ : Context V} {P : Path V} {φ ψ : Term V} →
                   EE Γ (φ ≡〈 Ω 〉 ψ) P → EP Γ (ψ ⊃ φ) (minus P)

--TODO Refactor
_∶_⇒C_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set
σ ∶ Γ ⇒C Δ = (∀ x → E Δ (close (typeof x Γ)) (σ _ x)) × 
             (∀ x → EP Δ (typeof x Γ ⟦ σ ⟧) (σ _ x)) ×
             (∀ x → EE Δ (typeof x Γ ⟦ σ ⟧) (σ _ x))

postulate compC : ∀ {U} {V} {W} {ρ : Sub V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                ρ ∶ Δ ⇒C Θ → σ ∶ Γ ⇒C Δ → ρ • σ ∶ Γ ⇒C Θ

postulate compC₂ : ∀ {U} {V} {W} {σ : Sub V W} {ρ : Rep U V} {Γ} {Δ} {Θ} →
                 σ ∶ Δ ⇒C Θ → ρ ∶ Γ ⇒R Δ → σ •₂ ρ ∶ Γ ⇒C Θ

postulate Sub↑C : ∀ {U} {V} {σ : Sub U V} {K} {Γ} {Δ} {A} →
                    σ ∶ Γ ⇒C Δ → Sub↑ K σ ∶ (Γ , A) ⇒C (Δ , A ⟦ σ ⟧)

postulate botsubC : ∀ {V} {Γ : Context V} {M} {A} →
                    E Γ (close A) M → x₀:= M ∶ (Γ ,T A) ⇒C Γ

postulate botsubCP : ∀ {V} {Γ : Context V} {δ} {φ} →
                     EP Γ φ δ → x₀:= δ ∶ (Γ ,P φ) ⇒C Γ

_∶_∼_∶_⇒C_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ = ∀ x → EE Δ (ρ _ x ≡〈 typeof x Γ ⟦ ρ ⟧ 〉 σ _ x) (τ x)

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
    (compC (compC₂ (botsubC (subst (λ T → E Θ T N) 
      (let open ≡-Reasoning in 
      begin
        close A
      ≡⟨⟨ close-sub A ⟩⟩
        close (A ⟦ σ ⟧)
      ≡⟨⟨ close-rep (A ⟦ σ ⟧) ⟩⟩
        close (A ⟦ σ ⟧ 〈 ρ 〉)
      ∎) 
      N∈EΘA)) (Rep↑-typed ρ∶Δ⇒RΘ)) (Sub↑C σ∶Γ⇒Δ)) Γ,A⊢M∶B Θvalid)))

--TODO Rename
Computable-Proof-Substitution : ∀ U V (σ : Sub U V) Γ Δ δ φ →
  σ ∶ Γ ⇒C Δ → Γ ⊢ δ ∶ φ → valid Δ → EP Δ (φ ⟦ σ ⟧) (δ ⟦ σ ⟧)
Computable-Path-Substitution₁ : ∀ U V (σ : Sub U V) Γ Δ P E →
  σ ∶ Γ ⇒C Δ → Γ ⊢ P ∶ E → valid Δ → EE Δ (E ⟦ σ ⟧) (P ⟦ σ ⟧)

Computable-Proof-Substitution U V σ Γ Δ .(var x) .(typeof x Γ) σ∶Γ⇒Δ (varR x x₁) Δvalid = proj₁ (proj₂ σ∶Γ⇒Δ) x
Computable-Proof-Substitution U V σ Γ Δ .(appP δ ε) .ψ σ∶Γ⇒Δ (appPR {δ = δ} {ε} {φ} {ψ} Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) Δvalid = appP-EP {V} {Δ} {δ ⟦ σ ⟧} {ε ⟦ σ ⟧} {φ ⟦ σ ⟧} {ψ ⟦ σ ⟧}
  (Computable-Proof-Substitution U V σ Γ Δ δ (φ ⊃ ψ) σ∶Γ⇒Δ Γ⊢δ∶φ⊃ψ Δvalid) 
  (Computable-Proof-Substitution U V σ Γ Δ ε φ σ∶Γ⇒Δ Γ⊢ε∶φ Δvalid)
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒Δ (ΛPR {δ = δ} {φ} {ψ} Γ,φ⊢δ∶ψ) Δvalid = 
  func-EP (λ W Θ ρ ε validΘ ρ∶Δ⇒RΘ ε∈EΘφσρ → 
  expand-EP 
    (subst₂ (EP Θ) 
      (let open ≡-Reasoning in 
      begin
        ψ ⇑ ⟦ x₀:= ε •₂ Rep↑ -Proof ρ • Sub↑ -Proof σ ⟧
      ≡⟨ sub-comp (ψ ⇑) ⟩
        ψ ⇑ ⟦ Sub↑ -Proof σ ⟧ ⟦ x₀:= ε •₂ Rep↑ -Proof ρ ⟧
      ≡⟨ sub-comp₂ (ψ ⇑ ⟦ Sub↑ -Proof σ ⟧) ⟩
        ψ ⇑ ⟦ Sub↑ -Proof σ ⟧ 〈 Rep↑ -Proof ρ 〉 ⟦ x₀:= ε ⟧
      ≡⟨ cong (λ x → (x 〈 Rep↑ -Proof ρ 〉) ⟦ x₀:= ε ⟧) (Sub↑-upRep {E = ψ}) ⟩
--TODO Make E explicit?
        ψ ⟦ σ ⟧ ⇑ 〈 Rep↑ -Proof ρ 〉 ⟦ x₀:= ε ⟧
      ≡⟨ sub-congl (Rep↑-upRep (ψ ⟦ σ ⟧)) ⟩
        ψ ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⟦ x₀:= ε ⟧
      ≡⟨ botsub-upRep ⟩
        ψ ⟦ σ ⟧ 〈 ρ 〉
      ∎) 
      (let open ≡-Reasoning in 
      begin
        δ ⟦ x₀:= ε •₂ Rep↑ -Proof ρ • Sub↑ -Proof σ ⟧
      ≡⟨ sub-comp δ ⟩
        δ ⟦ Sub↑ -Proof σ ⟧ ⟦ x₀:= ε •₂ Rep↑ -Proof ρ ⟧
      ≡⟨ sub-comp₂ (δ ⟦ Sub↑ -Proof σ ⟧) ⟩
        δ ⟦ Sub↑ -Proof σ ⟧ 〈 Rep↑ -Proof ρ 〉 ⟦ x₀:= ε ⟧
      ∎) 
    (Computable-Proof-Substitution (U , -Proof) W (x₀:= ε •₂ Rep↑ -Proof ρ • Sub↑ -Proof σ) (Γ ,P φ) Θ δ (ψ ⇑) (compC (compC₂ (botsubCP ε∈EΘφσρ) (Rep↑-typed ρ∶Δ⇒RΘ)) (Sub↑C σ∶Γ⇒Δ)) Γ,φ⊢δ∶ψ validΘ))
    (appPR (ΛPR {!!}) (EP-typed ε∈EΘφσρ)) 
    (redexR βR) 
    {!!}) -- TODO Common pattern with Computable-Substitution
Computable-Proof-Substitution U V σ Γ Δ δ φ σ∶Γ⇒Δ (convR Γ⊢δ∶φ Γ⊢δ∶φ₁ x) Δvalid = 
  conv-EP {!!} 
  (Computable-Proof-Substitution U V σ Γ Δ δ _ σ∶Γ⇒Δ Γ⊢δ∶φ Δvalid)
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒Δ (plusR Γ⊢P∶φ≡ψ) Δvalid = 
  plus-EP (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢P∶φ≡ψ Δvalid)
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒Δ (minusR Γ⊢P∶φ≡ψ) Δvalid = 
  minus-EP (Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ Γ⊢P∶φ≡ψ Δvalid)

Computable-Path-Substitution₁ U V σ Γ Δ .(var x) .(typeof x Γ) σ∶Γ⇒Δ (varR x x₁) validΔ = proj₂ (proj₂ σ∶Γ⇒Δ) x
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ (refR {M = M} {A} Γ⊢M∶A) validΔ = ref-EE
  (subst (λ x → E Δ x (M ⟦ σ ⟧)) (sym (close-sub A)) 
  (Computable-Substitution U V σ Γ Δ M A σ∶Γ⇒Δ Γ⊢M∶A validΔ))
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ (imp*R Γ⊢P∶E Γ⊢P∶E₁) validΔ = {!!}
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ (univR Γ⊢P∶E Γ⊢P∶E₁) validΔ = {!!}
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ (lllR Γ⊢P∶E) validΔ = {!!}
Computable-Path-Substitution₁ U V σ Γ Δ _ _ σ∶Γ⇒Δ (app*R Γ⊢P∶E Γ⊢P∶E₁) validΔ = {!!}
Computable-Path-Substitution₁ U V σ Γ Δ P _ σ∶Γ⇒Δ (convER Γ⊢P∶E Γ⊢P∶E₁ Γ⊢P∶E₂ x x₁) validΔ = {!!}

Computable-Path-Substitution : ∀ U V (τ : PathSub U V) σ σ' Γ Δ M A → τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → 
  EE Δ (M ⟦ σ ⟧ ≡〈 A ⟦ σ ⟧ 〉 M ⟦ σ' ⟧) (M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧) 
Computable-Path-Substitution U V τ σ σ' Γ Δ .(var x) .(typeof x Γ) τ∶σ∼σ' (varR x x₁) _ = 
  τ∶σ∼σ' x
Computable-Path-Substitution U V τ σ σ' Γ Δ .(app -bot out) .(app -Omega out) τ∶σ∼σ' (⊥R x) validΔ = ref-EE (⊥-E validΔ)
Computable-Path-Substitution U V τ σ σ' Γ Δ _ .(app -Omega out) τ∶σ∼σ' (impR Γ⊢M∶A Γ⊢M∶A₁) = {!!}
Computable-Path-Substitution U V τ σ σ' Γ Δ _ A τ∶σ∼σ' (appR Γ⊢M∶A Γ⊢M∶A₁) = {!!}
Computable-Path-Substitution U V τ σ σ' Γ Δ _ _ τ∶σ∼σ' (ΛR Γ⊢M∶A) = {!!}

Strong-Normalization : ∀ V K (Γ : Context V) (M : Expression V (varKind K)) A → Γ ⊢ M ∶ A → SN M
Strong-Normalization V -Proof Γ δ φ Γ⊢δ∶φ = {!!}
Strong-Normalization V -Term Γ M A Γ⊢M∶A = E-sub-SN V Γ (close A) M 
  (subst (E Γ (close A)) sub-idOp 
  (Computable-Substitution V V (idSub V) Γ Γ M A {!!} Γ⊢M∶A {!!}))
Strong-Normalization V -Path Γ P E Γ⊢P∶E = {!!}
\end{code}
