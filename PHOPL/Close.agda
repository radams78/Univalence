module PHOPL.Close where
open import Prelims
open import PHOPL

close : ∀ {V} → Type V → Type ∅
close (app -Omega out) = Ω
close (app -func (A ,, B ,, out)) = close A ⇛ close B

postulate close-sub : ∀ {U} {V} (A : Type U) {σ : Sub U V} → close (A ⟦ σ ⟧) ≡ close A

postulate close-rep : ∀ {U} {V} (A : Type U) {ρ : Rep U V} → close (A 〈 ρ 〉) ≡ close A
