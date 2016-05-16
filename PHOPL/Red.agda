module PHOPL.Red where
open import Data.Unit
open import Data.Product hiding (_,_)
open import Data.List
open import PHOPL 

postulate R : Reduction

postulate βR : ∀ {V} {φ} {δ} {ε} → R {V} -appProof (ΛP φ δ ,, ε ,, out) (δ ⟦ x₀:= ε ⟧)

postulate βE : ∀ {V} {M} {N} {A} {P} {Q} → R {V} -app* (M ,, N ,, λλλ A P ,, Q ,, out) (P ⟦ x₀:= M • x₀:= (N ⇑) • x₀:= (Q ⇑ ⇑) ⟧)

open import Reduction PHOPL R public renaming (_⇒_ to _⇒R_;_≃_ to _≃R_;redex to redexR;app to appR;appl to applR;appr to apprR;creates' to creates'R;
  respects' to respects'R;respects-osr to respects-osrR;respects-conv to respects-convR)

postulate R-creates-rep : creates'R replacement

postulate ⊥SN : ∀ {V} → SN {V} ⊥

postulate ⊃SN : ∀ {V} {φ ψ : Term V} → SN φ → SN ψ → SN (φ ⊃ ψ)

all-SN : ∀ {V} → List (Term V) → Set
all-SN [] = ⊤
all-SN (M ∷ MM) = SN M × all-SN MM
--TODO Use Data.List library

postulate var-APP-SN : ∀ {V} (x : Var V -Term) (MM : List (Term V)) →
                     all-SN MM → SN (APP (var x) MM)
--TODO Move to Reduction library

postulate SN-βexp : ∀ {V} {φ : Term V} {δ : Proof (V , -Proof)} {ε : Proof V} →
                  SN ε → SN (δ ⟦ x₀:= ε ⟧) → SN (appP (ΛP φ δ) ε) 

