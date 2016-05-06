\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.Substitution.OpFamily (G : Grammar) where
open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G
open import Grammar.Substitution.PreOpFamily G
open import Grammar.Substitution.Lifting G
open import Grammar.Substitution.LiftFamily G
\end{code}
}

We now define two compositions $\bullet_1 : \mathrm{replacement};\mathrm{substitution} \rightarrow \mathrm{substitution}$ and $\bullet_2 : \mathrm{substitution};\mathrm{replacement} \rightarrow \mathrm{substitution}$.

\begin{code}
infix 75 _•₁_
_•₁_ : ∀ {U} {V} {W} → Rep V W → Sub U V → Sub U W
(ρ •₁ σ) K x = (σ K x) 〈 ρ 〉

Sub↑-comp₁ : ∀ {U} {V} {W} {K} {ρ : Rep V W} {σ : Sub U V} → Sub↑ K (ρ •₁ σ) ∼ Rep↑ K ρ •₁ Sub↑ K σ
\end{code}

\AgdaHide{
\begin{code}
Sub↑-comp₁ {K = K} x₀ = refl
Sub↑-comp₁ {U} {V} {W} {K} {ρ} {σ} {L} (↑ x) = let open ≡-Reasoning {A = Expression (W , K) (varKind L)} in 
  begin 
    (σ L x) 〈 ρ 〉 〈 upRep 〉
  ≡⟨⟨ rep-comp (σ L x) ⟩⟩
    (σ L x) 〈 upRep •R ρ 〉
  ≡⟨⟩
    (σ L x) 〈 Rep↑ K ρ •R upRep 〉
  ≡⟨ rep-comp (σ L x) ⟩
    (σ L x) 〈 upRep 〉 〈 Rep↑ K ρ 〉
  ∎
\end{code}
}

\begin{code}
COMP₁ : Composition proto-replacement proto-substitution proto-substitution
COMP₁ = record { 
  circ = _•₁_ ; 
  liftOp-circ = Sub↑-comp₁ ; 
  apV-circ = refl }

sub-comp₁ : ∀ {U} {V} {W} {C} {K} 
  (E : Subexpression U C K) {ρ : Rep V W} {σ : Sub U V} →
  E ⟦ ρ •₁ σ ⟧ ≡ E ⟦ σ ⟧ 〈 ρ 〉
sub-comp₁ E = Composition.ap-circ COMP₁ E

infix 75 _•₂_
_•₂_ : ∀ {U} {V} {W} → Sub V W → Rep U V → Sub U W
(σ •₂ ρ) K x = σ K (ρ K x)

Sub↑-comp₂ : ∀ {U} {V} {W} {K} {σ : Sub V W} {ρ : Rep U V} → 
  Sub↑ K (σ •₂ ρ) ∼ Sub↑ K σ •₂ Rep↑ K ρ
\end{code}

\AgdaHide{
\begin{code}
Sub↑-comp₂ {K = K} x₀ = refl
Sub↑-comp₂ (↑ x) = refl
\end{code}
}

\begin{code}
COMP₂ : Composition proto-substitution proto-replacement proto-substitution
COMP₂ = record { 
  circ = _•₂_ ; 
  liftOp-circ = Sub↑-comp₂ ; 
  apV-circ = refl }

sub-comp₂ : ∀ {U} {V} {W} {C} {K} 
  (E : Subexpression U C K) {σ : Sub V W} {ρ : Rep U V} → 
  E ⟦ σ •₂ ρ ⟧ ≡ E 〈 ρ 〉 ⟦ σ ⟧
\end{code}

\AgdaHide{
\begin{code}
sub-comp₂ E = Composition.ap-circ COMP₂ E
\end{code}
}

Composition is defined by $(\sigma \circ \rho)(x) \equiv \rho(x) [ \sigma ]$.

\begin{code}
infix 75 _•_
_•_ : ∀ {U} {V} {W} → Sub V W → Sub U V → Sub U W
(σ • ρ) K x = ρ K x ⟦ σ ⟧
\end{code}

Using the fact that $\bullet_1$ and $\bullet_2$ are compositions, we are
able to prove that this is a composition $\mathrm{substitution} ; \mathrm{substitution} \rightarrow \mathrm{substitution}$, and hence that substitution is a family of operations.

\begin{code}
Sub↑-comp : ∀ {U} {V} {W} {ρ : Sub U V} {σ : Sub V W} {K} → 
  Sub↑ K (σ • ρ) ∼ Sub↑ K σ • Sub↑ K ρ
Sub↑-comp x₀ = refl
Sub↑-comp {W = W} {ρ = ρ} {σ = σ} {K = K} {L} (↑ x) = 
  let open ≡-Reasoning in 
  begin 
    ρ L x ⟦ σ ⟧ 〈 upRep 〉
  ≡⟨⟨ sub-comp₁ (ρ L x) ⟩⟩
    ρ L x ⟦ upRep •₁ σ ⟧
  ≡⟨⟩
    ρ L x ⟦ Sub↑ K σ •₂ upRep ⟧
  ≡⟨ sub-comp₂ (ρ L x) ⟩
     ρ L x 〈 upRep 〉 ⟦ Sub↑ K σ ⟧ 
  ∎

substitution : OpFamily
substitution = record { 
  liftFamily = proto-substitution ; 
  isOpFamily = record { 
    _∘_ = _•_ ; 
    liftOp-comp = Sub↑-comp ; 
    apV-comp = refl } 
  }
\end{code}

\AgdaHide{
\begin{code}
open OpFamily substitution using (assoc) 
  renaming (liftOp-idOp to Sub↑-idOp;
           ap-idOp to sub-idOp;
           ap-circ to sub-comp;
           ap-congl to sub-cong;
           unitl to sub-unitl;
           unitr to sub-unitr)
  public
\end{code}
}