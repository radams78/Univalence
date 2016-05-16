module PHOPL.Computable where
open import PHOPL
open import PHOPL.Neutral
open import PHOPL.Rules
open import PHOPL.Close
open import PHOPL.Red
open import PHOPL.Meta

postulate E : ∀ {V} → Context V → Type ∅ → Term V → Set

postulate Neutral-E : ∀ {V} {Γ : Context V} {A : Type V} {M : Term V} →
                    Neutral M → Γ ⊢ M ∶ A → E Γ (close A) M

var-E : ∀ {V} {Γ : Context V} {x : Var V -Term} → 
  valid Γ → E Γ (close (typeof x Γ)) (var x)
var-E {V} {Γ} {x} Γvalid = Neutral-E (var x) (varR x Γvalid)

postulate E-SN : ∀ V (Γ : Context V) A M → E Γ A M → SN M

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

postulate EP-SN : ∀ {V} {Γ : Context V} {δ} {φ} → EP Γ φ δ → SN δ

postulate EE : ∀ {V} → Context V → Equation V → Path V → Set

postulate ref-EE : ∀ {V} {Γ : Context V} {M : Term V} {A : Type V} → E Γ (close A) M → EE Γ (M ≡〈 A 〉 M) (reff M)

postulate univ-EE : ∀ {V} {Γ : Context V} {φ ψ : Term V} {δ ε : Proof V} →
                  EP Γ (φ ⊃ ψ) δ → EP Γ (ψ ⊃ φ) ε → EE Γ (φ ≡〈 Ω 〉 ψ) (univ φ ψ δ ε)

postulate imp*-EE : ∀ {V} {Γ : Context V} {φ φ' ψ ψ' : Term V} {P Q : Path V} →
                  EE Γ (φ ≡〈 Ω 〉 φ') P → EE Γ (ψ ≡〈 Ω 〉 ψ') Q → EE Γ (φ ⊃ ψ ≡〈 Ω 〉 φ' ⊃ ψ') (P ⊃* Q)

postulate app*-EE : ∀ {V} {Γ : Context V} {M} {M'} {N} {N'} {A} {B} {P} {Q} →
                  EE Γ (M ≡〈 A ⇛ B 〉 M') P → EE Γ (N ≡〈 A 〉 N') Q →
                  EE Γ (appT M N ≡〈 B 〉 appT M' N') (app* N N' P Q)

postulate plus-EP : ∀ {V} {Γ : Context V} {P : Path V} {φ ψ : Term V} →
                  EE Γ (φ ≡〈 Ω 〉 ψ) P → EP Γ (φ ⊃ ψ) (plus P)

postulate minus-EP : ∀ {V} {Γ : Context V} {P : Path V} {φ ψ : Term V} →
                   EE Γ (φ ≡〈 Ω 〉 ψ) P → EP Γ (ψ ⊃ φ) (minus P)

postulate func-EE : ∀ {U} {Γ : Context U} {A} {B} {M} {M'} {P} →
                   (∀ V (Δ : Context V) (N N' : Term V) Q ρ → ρ ∶ Γ ⇒R Δ → valid Δ → 
                     E Δ (close A) N → E Δ (close A) N' → EE Δ (N ≡〈 A 〈 ρ 〉 〉 N') Q →
                     EE Δ (appT (M 〈 ρ 〉) N ≡〈 B 〈 ρ 〉 〉 appT (M' 〈 ρ 〉) N') (app* N N' (P 〈 ρ 〉) Q)) →
                   EE Γ (M ≡〈 A ⇛ B 〉 M') P

postulate expand-EE : ∀ {V} {Γ : Context V} {A} {M N : Term V} {P Q} →
                   EE Γ (M ≡〈 A 〉 N) Q → Γ ⊢ P ∶ M ≡〈 A 〉 N → P ⇒R Q → SN P → EE Γ (M ≡〈 A 〉 N) P

postulate conv-EE : ∀ {V} {Γ : Context V} {E} {E'} {P} →
                  EE Γ E P → E ≃ E' → EE Γ E' P

postulate EE-typed : ∀ {V} {Γ : Context V} {A} {M N : Term V} {P} →
                   EE Γ (M ≡〈 A 〉 N) P → Γ ⊢ P ∶ M ≡〈 A 〉 N

