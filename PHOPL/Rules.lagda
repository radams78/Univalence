\AgdaHide{
\begin{code}
module PHOPL.Rules where
open import PHOPL
\end{code}
}

The rules of deduction of the system are as follows.

\[ \infer{\langle \rangle \vald}{} \qquad
\infer{\Gamma, x : A \vald}{\Gamma \vald} \qquad 
\infer{\Gamma, p : \phi \vald}{\Gamma \vdash \phi : \Omega} \]

\[ \infer[(x : A \in \Gamma)]{\Gamma \vdash x : A}{\Gamma \vald} \qquad
\infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald} \]

\[ \infer{\Gamma \vdash \bot : \Omega}{\Gamma \vald} \qquad
\infer{\Gamma \vdash \phi \rightarrow \psi : \Omega}{\Gamma \vdash \phi : \Omega \quad \Gamma \vdash \psi : \Omega} \]

\[ \infer{\Gamma \vdash M N : B} {\Gamma \vdash M : A \rightarrow B \quad \Gamma \vdash N : A} \qquad
\infer{\Gamma \vdash \delta \epsilon : \psi} {\Gamma \vdash \delta : \phi \rightarrow \psi \quad \Gamma \vdash \epsilon : \phi} \]

\[ \infer{\Gamma \vdash \lambda x:A.M : A \rightarrow B}{\Gamma, x : A \vdash M : B} \qquad
\infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \rightarrow \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]

\[ \infer[(\phi \simeq \phi)]{\Gamma \vdash \delta : \psi}{\Gamma \vdash \delta : \phi \quad \Gamma \vdash \psi : \Omega} \]

\begin{code}
infix 10 _⊢_∶_
data _⊢_∶_ : ∀ {V} → Context V → Term V → Expression V (nonVarKind -Type) → Set₁ where
  var : ∀ {V} {Γ : Context V} {x} → Γ ⊢ var x ∶ typeof x Γ
  ⊥R : ∀ {V} {Γ : Context V} → Γ ⊢ ⊥ ∶ Ω 〈 (λ _ ()) 〉
  imp : ∀ {V} {Γ : Context V} {φ} {ψ} → Γ ⊢ φ ∶ Ω 〈 (λ _ ()) 〉 → Γ ⊢ ψ ∶ Ω 〈 (λ _ ()) 〉 → Γ ⊢ φ ⊃ ψ ∶ Ω 〈 (λ _ ()) 〉
  app : ∀ {V} {Γ : Context V} {M} {N} {A} {B} → Γ ⊢ M ∶ app -func (A ,, B ,, out) → Γ ⊢ N ∶ A → Γ ⊢ appTerm M N ∶ B
  Λ : ∀ {V} {Γ : Context V} {A} {M} {B} → Γ , A ⊢ M ∶ B 〈 upRep 〉 → Γ ⊢ app -lamTerm (A ,, M ,, out) ∶ app -func (A ,, B ,, out)

data Pvalid : ∀ {V} {P} → Context V → PContext' V P → Set₁ where
  〈〉 : ∀ {V} {Γ : Context V} → Pvalid Γ 〈〉
  _,_ : ∀ {V} {P} {Γ : Context V} {Δ : PContext' V P} {φ : Term V} → Pvalid Γ Δ → Γ ⊢ φ ∶ Ω 〈 (λ _ ()) 〉 → Pvalid Γ (Δ , φ)

infix 10 _,,_⊢_∶∶_
data _,,_⊢_∶∶_ : ∀ {V} {P} → Context V → PContext' V P → Proof V P → Term V → Set₁ where
  var : ∀ {V} {P} {Γ : Context V} {Δ : PContext' V P} {p} → Pvalid Γ Δ → Γ ,, Δ ⊢ varP p ∶∶ propof p Δ 
  app : ∀ {V} {P} {Γ : Context V} {Δ : PContext' V P} {δ} {ε} {φ} {ψ} → Γ ,, Δ ⊢ δ ∶∶ φ ⊃ ψ → Γ ,, Δ ⊢ ε ∶∶ φ → Γ ,, Δ ⊢ appP {V} {P} δ ε ∶∶ ψ
  Λ : ∀ {V} {P} {Γ : Context V} {Δ : PContext' V P} {φ} {δ} {ψ} → Γ ,, Δ , φ ⊢ δ ∶∶ ψ → Γ ,, Δ ⊢ ΛP {V} {P} φ δ ∶∶ φ ⊃ ψ
  convR : ∀ {V} {P} {Γ : Context V} {Δ : PContext' V P} {δ} {φ} {ψ} → Γ ,, Δ ⊢ δ ∶∶ φ → Γ ⊢ ψ ∶ Ω 〈 (λ _ ()) 〉 → φ ⇒ ψ → Γ ,, Δ ⊢ δ ∶∶ ψ
\end{code}
