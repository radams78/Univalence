module PHOPL.Close where
open import Prelims
open import PHOPL

close : ∀ {V} → Type V → Type ∅
close (app -Omega out) = Ω
close (app -func (A ,, B ,, out)) = close A ⇛ close B

ty : ∀ {U} {V} → Type U → Type V
ty A = close A 〈 magic 〉

postulate close-close : ∀ {V} {A : Type V} → close (close A) ≡ close A

postulate close-sub : ∀ {U} {V} (A : Type U) {σ : Sub U V} → close (A ⟦ σ ⟧) ≡ close A

postulate close-rep : ∀ {U} {V} (A : Type U) {ρ : Rep U V} → close (A 〈 ρ 〉) ≡ close A

postulate close-magic : ∀ {V} {A : Type V} → close A 〈 magic 〉 ≡ A

postulate type-sub : ∀ {U} {V} {A : Type U} {σ σ' : Sub U V} → A ⟦ σ ⟧ ≡ A ⟦ σ' ⟧

postulate ty-rep : ∀ {U} {V} {W} (A : Type U) {ρ : Rep U V} → ty {V = W} (A 〈 ρ 〉) ≡ ty A

postulate ty-sub : ∀ {U} {V} {W} (A : Type U) {σ : Sub U V} → ty {V = W} (A ⟦ σ ⟧) ≡ ty A

postulate ty-rep' : ∀ {U} {V} {W} (A : Type U) {ρ : Rep V W} → (ty A) 〈 ρ 〉 ≡ ty A

postulate ty-sub' : ∀ {U} {V} {W} (A : Type U) {σ : Sub V W} → (ty A) ⟦ σ ⟧ ≡ ty A
