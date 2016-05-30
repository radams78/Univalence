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
open import Grammar.Substitution.RepSub G
\end{code}
}

We now define two compositions $\bullet_1 : \mathrm{replacement} ; \mathrm{substitution} \rightarrow \mathrm{substitution}$ and $\bullet_2 : \mathrm{substitution};\mathrm{replacement} \rightarrow \mathrm{substitution}$.

\begin{code}
infixl 60 _•RS_
_•RS_ : ∀ {U} {V} {W} → Rep V W → Sub U V → Sub U W
(ρ •RS σ) K x = (σ K x) 〈 ρ 〉

Sub↑-compRS : ∀ {U} {V} {W} {K} {ρ : Rep V W} {σ : Sub U V} → Sub↑ K (ρ •RS σ) ∼ Rep↑ K ρ •RS Sub↑ K σ
\end{code}

\AgdaHide{
\begin{code}
Sub↑-compRS {K = K} x₀ = refl
Sub↑-compRS {U} {V} {W} {K} {ρ} {σ} {L} (↑ x) = let open ≡-Reasoning {A = Expression (W , K) (varKind L)} in 
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
COMPRS : Composition proto-replacement proto-substitution proto-substitution
COMPRS = record { 
  circ = _•RS_ ; 
  liftOp-circ = Sub↑-compRS ; 
  apV-circ = refl }

sub-compRS : ∀ {U} {V} {W} {C} {K} 
  (E : Subexpression U C K) {ρ : Rep V W} {σ : Sub U V} →
  E ⟦ ρ •RS σ ⟧ ≡ E ⟦ σ ⟧ 〈 ρ 〉
sub-compRS E = Composition.ap-circ COMPRS E

infixl 60 _•SR_
_•SR_ : ∀ {U} {V} {W} → Sub V W → Rep U V → Sub U W
(σ •SR ρ) K x = σ K (ρ K x)

Sub↑-compSR : ∀ {U} {V} {W} {K} {σ : Sub V W} {ρ : Rep U V} → 
  Sub↑ K (σ •SR ρ) ∼ Sub↑ K σ •SR Rep↑ K ρ
\end{code}

\AgdaHide{
\begin{code}
Sub↑-compSR {K = K} x₀ = refl
Sub↑-compSR (↑ x) = refl
\end{code}
}

\begin{code}
COMPSR : Composition proto-substitution proto-replacement proto-substitution
COMPSR = record { 
  circ = _•SR_ ; 
  liftOp-circ = Sub↑-compSR ; 
  apV-circ = refl }

sub-compSR : ∀ {U} {V} {W} {C} {K} 
  (E : Subexpression U C K) {σ : Sub V W} {ρ : Rep U V} → 
  E ⟦ σ •SR ρ ⟧ ≡ E 〈 ρ 〉 ⟦ σ ⟧
\end{code}

\AgdaHide{
\begin{code}
sub-compSR E = Composition.ap-circ COMPSR E
\end{code}
}

\begin{code}
Sub↑-upRep : ∀ {U} {V} {C} {K} {L} (E : Subexpression U C K) {σ : Sub U V} →
  E 〈 upRep 〉 ⟦ Sub↑ L σ ⟧ ≡ E ⟦ σ ⟧ 〈 upRep 〉
\end{code}

\AgdaHide{
\begin{code}
Sub↑-upRep E = liftOp-up-mixed COMPSR COMPRS (λ {_} {_} {_} {_} {E} → sym (up-is-up' {E = E})) {E}
\end{code}
}

Composition is defined by $(\sigma \circ \rho)(x) \equiv \rho(x) [ \sigma ]$.

\begin{code}
infixl 60 _•_
_•_ : ∀ {U} {V} {W} → Sub V W → Sub U V → Sub U W
(σ • ρ) K x = ρ K x ⟦ σ ⟧
\end{code}

Using the fact that $\bullet_1$ and $\bullet_2$ are compositions, we are
able to prove that this is a composition $\mathrm{substitution} ; \mathrm{substitution} \rightarrow \mathrm{substitution}$, and hence that substitution is a family of operations.

\begin{code}
Sub↑-comp : ∀ {U} {V} {W} {ρ : Sub U V} {σ : Sub V W} {K} → 
  Sub↑ K (σ • ρ) ∼ Sub↑ K σ • Sub↑ K ρ
\end{code}

\AgdaHide{
\begin{code}
Sub↑-comp x₀ = refl
Sub↑-comp {W = W} {ρ = ρ} {σ = σ} {K = K} {L} (↑ x) = sym (Sub↑-upRep (ρ L x))

Sub↑-upRep₂ : ∀ {U} {V} {C} {K} {L} {M} (E : Subexpression U C M) {σ : Sub U V} → E ⇑ ⇑ ⟦ Sub↑ K (Sub↑ L σ) ⟧ ≡ E ⟦ σ ⟧ ⇑ ⇑
Sub↑-upRep₂ {U} {V} {C} {K} {L} {M} E {σ} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ ⟦ Sub↑ K (Sub↑ L σ) ⟧
  ≡⟨ Sub↑-upRep (E ⇑) ⟩
    E ⇑ ⟦ Sub↑ L σ ⟧ ⇑
  ≡⟨ rep-congl (Sub↑-upRep E) ⟩
    E ⟦ σ ⟧ ⇑ ⇑
  ∎

Sub↑-upRep₃ : ∀ {U} {V} {C} {K} {L} {M} {N} (E : Subexpression U C N) {σ : Sub U V} → E ⇑ ⇑ ⇑ ⟦ Sub↑ K (Sub↑ L (Sub↑ M σ)) ⟧ ≡ E ⟦ σ ⟧ ⇑ ⇑ ⇑
Sub↑-upRep₃ {U} {V} {C} {K} {L} {M} {N} E {σ} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ ⇑ ⟦ Sub↑ K (Sub↑ L (Sub↑ M σ)) ⟧
  ≡⟨ Sub↑-upRep₂ (E ⇑) ⟩
    E ⇑ ⟦ Sub↑ M σ ⟧ ⇑ ⇑
  ≡⟨ rep-congl (rep-congl (Sub↑-upRep E)) ⟩
    E ⟦ σ ⟧ ⇑ ⇑ ⇑
  ∎

Rep↑-Sub↑-upRep₃ : ∀ {U} {V} {W} {K1} {K2} {K3} {C} {K4} 
                   (M : Subexpression U C K4)
                   (σ : Sub U V) (ρ : Rep V W) →
                    M ⇑ ⇑ ⇑ ⟦ Sub↑ K1 (Sub↑ K2 (Sub↑ K3 σ)) ⟧ 〈 Rep↑ K1 (Rep↑ K2 (Rep↑ K3 ρ)) 〉
                    ≡ M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑
Rep↑-Sub↑-upRep₃ M σ ρ = trans (rep-congl (Sub↑-upRep₃ M {σ})) (Rep↑-upRep₃ (M ⟦ σ ⟧))

assocRSSR : ∀ {U} {V} {W} {X} {ρ : Sub W X} {σ : Rep V W} {τ : Sub U V} →
            ρ • (σ •RS τ) ∼ (ρ •SR σ) • τ
assocRSSR {ρ = ρ} {σ} {τ} x = sym (sub-compSR (τ _ x))
\end{code}
}

\begin{code}
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
open OpFamily substitution using (comp-congl;comp-congr)
  renaming (liftOp-idOp to Sub↑-idOp;
           ap-idOp to sub-idOp;
           ap-congl to sub-congr;
           ap-congr to sub-congl;
           unitl to sub-unitl;
           unitr to sub-unitr;
           ∼-sym to sub-sym;
           ∼-trans to sub-trans;
           assoc to sub-assoc)
  public
\end{code}
}

\begin{frame}[fragile]
\frametitle{Metatheorems}
We can now prove general results such as:

\begin{code}
sub-comp : ∀ {U} {V} {W} {C} {K}
  (E : Subexpression U C K) {σ : Sub V W} {ρ : Sub U V} →
  E ⟦ σ • ρ ⟧ ≡ E ⟦ ρ ⟧ ⟦ σ ⟧
\end{code}
\end{frame}

\AgdaHide{
\begin{code}
sub-comp = OpFamily.ap-circ substitution
\end{code}
}
