\begin{code}
module PHOPL.MainProp where
open import PHOPL
open import PHOPL.Rules
open import PHOPL.PathSub

_⟦⟦_⟧⟧ : ∀ {U} {V} → Term U → PathSub U V → Path V
M ⟦⟦ τ ⟧⟧ = {!!}

E : ∀ {V} → Context V → Type V → Term V → Set
E = {!!}

EE : ∀ {V} → Context V → Equation V → Path V → Set
EE = {!!}

_∶_⇒C_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set
σ ∶ Γ ⇒C Δ = {!!}

_∶_∼_∶_⇒C_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ = {!!}

Computable-Substitution : ∀ U V (σ : Sub U V) Γ Δ M A → σ ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → E Δ (A ⟦ σ ⟧) (M ⟦ σ ⟧)

Computable-Substitution = {!!}

Computable-Path-Substitution : ∀ U V (τ : PathSub U V) σ σ' Γ Δ M A → τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → 
  EE Δ (M ⟦ σ ⟧ ≡〈 A ⟦ σ ⟧ 〉 M ⟦ σ' ⟧) (M ⟦⟦ τ ⟧⟧)

Computable-Path-Substitution = {!!}
\end{code}
