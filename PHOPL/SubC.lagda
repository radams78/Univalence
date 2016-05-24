\AgdaHide{
\begin{code}
module PHOPL.SubC where
open import Data.Product hiding (_,_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Red
open import PHOPL.Rules
open import PHOPL.Meta
open import PHOPL.Computable
open import PHOPL.PathSub
\end{code}
}

\begin{frame}[fragile]
\frametitle{Path Substitution}
\begin{prop}
If $\Gamma, x : A \vdash M : B$ and $\Gamma \vdash P : N =_A N'$ then
$\Gamma \vdash \{ P / x \} M : [N / x] M =_B [N' / x] M$.
\end{prop}

\AgdaHide{
\begin{code}
_∶_∼_∶_⇒_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ σ ∼ σ' ∶ Γ ⇒ Δ = ∀ x → Δ ⊢ τ x ∶ σ -Term x ≡〈 typeof' x Γ 〉 σ' -Term x

change-cod-PS : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} {Δ'} →
                τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ → Δ ≡ Δ' → τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ'
change-cod-PS {τ = τ} {ρ} {σ} {Γ} τ∶ρ∼σ Δ≡Δ' = subst (λ x → τ ∶ ρ ∼ σ ∶ Γ ⇒ x) Δ≡Δ' τ∶ρ∼σ

postulate typeof'-up : ∀ {V} {Γ : Context V} {A} {x} → typeof' (↑ x) (Γ ,T A) ≡ typeof' x Γ

pathsub↑-typed : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {A} {Δ} → 
  τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ → valid Δ → pathsub↑ τ ∶ sub↖ ρ ∼ sub↗ σ ∶ Γ ,T A ⇒ Δ ,T  A ,T  A ,E var x₁ ≡〈 A 〉 var x₀
pathsub↑-typed _ validΔ x₀ = varR x₀ (valid-addpath validΔ)
pathsub↑-typed {U} {Γ = Γ} {A} τ∶ρ∼σ validΔ (↑ x) = change-type (Weakening (Weakening (Weakening (τ∶ρ∼σ x) (ctxTR validΔ) upRep-typed) 
                                                                           (ctxTR (ctxTR validΔ)) upRep-typed) 
                                                                (valid-addpath validΔ) upRep-typed) 
                                                    (cong₃ _≡〈_〉_ refl (sym (typeof'-up {U} {Γ = Γ} {A} {x = x})) refl)

postulate sub↖-decomp : ∀ {U} {V} {C} {K} (M : Subexpression (U , -Term) C K) {ρ : Sub U V} → 
                     M ⟦ Sub↑ _ ρ ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= var x₂ ⟧ ≡ M ⟦ sub↖ ρ ⟧

postulate sub↗-decomp : ∀ {U} {V} {C} {K} (M : Subexpression (U , -Term) C K) {ρ : Sub U V} → 
                     M ⟦ Sub↑ _ ρ ⟧ 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 〈 Rep↑ _ upRep 〉 ⟦ x₀:= var x₁ ⟧ ≡ M ⟦ sub↗ ρ ⟧
\end{code}
}

\begin{code}
Path-Substitution : ∀ {U} {V} {Γ : Context U} {Δ : Context V} 
  {ρ} {σ} {τ} {M} {A} →
  (Γ ⊢ M ∶ A) → (τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ) →
  (ρ ∶ Γ ⇒ Δ) → (σ ∶ Γ ⇒ Δ) → 
  valid Δ → 
  Δ ⊢ M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ∶ M ⟦ ρ ⟧ ≡〈 yt A 〉 M ⟦ σ ⟧
\end{code}

\AgdaHide{
\begin{code}
Path-Substitution (varR x validΓ) τ∶ρ∼σ _ _ _ = τ∶ρ∼σ x
Path-Substitution (⊥R validΓ) _ _ _ validΔ = refR (⊥R validΔ)
Path-Substitution (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) τ∶ρ∼σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = ⊃*R (Path-Substitution Γ⊢φ∶Ω τ∶ρ∼σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ) (Path-Substitution Γ⊢ψ∶Ω τ∶ρ∼σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ)
Path-Substitution (appR {A = A} Γ⊢M∶A⇛B Γ⊢N∶A) τ∶σ∼σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = 
  app*R (Substitution Γ⊢N∶A validΔ ρ∶Γ⇒Δ) (Substitution Γ⊢N∶A validΔ σ∶Γ⇒Δ)
  (Path-Substitution Γ⊢M∶A⇛B τ∶σ∼σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ) (Path-Substitution Γ⊢N∶A τ∶σ∼σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ)
Path-Substitution {U} {V} {Γ} {Δ} {ρ} {σ} {τ} (ΛR .{U} .{Γ} {A} {M} {B} Γ,A⊢M∶B) τ∶σ∼σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = 
  let ΔAAE = Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀ in
  let validΔAA  : valid (Δ ,T A ,T A)
      validΔAA = ctxTR (ctxTR validΔ) in
  let validΔAAE : valid ΔAAE
      validΔAAE = ctxER (varR x₁ validΔAA) (varR x₀ validΔAA) in
  let Mσ-typed : ∀ {σ} {x} → σ ∶ Γ ⇒ Δ → typeof x ΔAAE ≡ ty A → ΔAAE ⊢ appT ((ΛT A M) ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x) ∶ ty B
      Mσ-typed = λ {σ} {x} σ∶Γ⇒Δ x∶A∈ΔAAE → appR (ΛR (Weakening (Weakening (Weakening (Substitution Γ,A⊢M∶B (ctxTR validΔ) (Sub↑-typed σ∶Γ⇒Δ)) 
                                                                                      (ctxTR (ctxTR validΔ)) (Rep↑-typed upRep-typed)) 
                                                                           (ctxTR (ctxTR (ctxTR validΔ))) (Rep↑-typed upRep-typed)) 
                                                                (ctxTR validΔAAE) (Rep↑-typed upRep-typed))) 
                                                     (change-type (varR x validΔAAE) x∶A∈ΔAAE) in
  let step1 : Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀ ⊢ 
              M ⟦⟦ pathsub↑ τ ∶ sub↖ ρ ∼ sub↗ σ ⟧⟧ ∶ 
              appT ((ΛT A M) ⟦ ρ ⟧ ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT ((ΛT A M) ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₁)
      step1 = convER 
               (Path-Substitution Γ,A⊢M∶B 
                 (pathsub↑-typed τ∶σ∼σ' validΔ) (sub↖-typed ρ∶Γ⇒Δ) (sub↗-typed σ∶Γ⇒Δ) 
                 validΔAAE)
                 (Mσ-typed ρ∶Γ⇒Δ refl)
                 (Mσ-typed σ∶Γ⇒Δ refl)
                 (sym-conv (redex-conv (subst (R -appTerm ((ΛT A M ⟦ ρ ⟧) ⇑ ⇑ ⇑ ,, var x₂ ,, out)) (sub↖-decomp M) βT))) (sym-conv (redex-conv (subst (R -appTerm ((ΛT A M ⟦ σ ⟧) ⇑ ⇑ ⇑ ,, var x₁ ,, out)) (sub↗-decomp M) βT)))
  in lllR step1

postulate idPathSub : ∀ V → PathSub V V

infixr 75 _•RP_
_•RP_ : ∀ {U} {V} {W} → Rep V W → PathSub U V → PathSub U W
(ρ •RP τ) x = τ x 〈 ρ 〉

postulate compRP-typed : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} {σ σ' : Sub U V}
                           {Γ} {Δ} {Θ} →
                           ρ ∶ Δ ⇒R Θ → τ ∶ σ ∼ σ' ∶ Γ ⇒ Δ →
                           ρ •RP τ ∶ ρ •RS σ ∼ ρ •RS σ' ∶ Γ ⇒ Θ

postulate pathsub↑-compRP : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} →
                          pathsub↑ (ρ •RP τ) ∼∼ Rep↑ -Path (Rep↑ -Term (Rep↑ -Term ρ)) •RP pathsub↑ τ

extendPS : ∀ {U} {V} → PathSub U V → Path V → PathSub (U , -Term) V
extendPS τ P x₀ = P
extendPS τ P (↑ x) = τ x

postulate extendPS-typed : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} {P} {M} {N} {A} →
                           τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ → Δ ⊢ P ∶ M ≡〈 A 〉 N →
                           extendPS τ P ∶ extendSub ρ M ∼ extendSub σ N ∶ Γ ,T A ⇒ Δ

postulate pathsub-extendPS : ∀ {U} {V} M {τ} {P : Path V} {N : Term V} {σ : Sub U V} {N' : Term V} {σ'} →
                           M ⟦⟦ extendPS τ P ∶ x₀:= N • Sub↑ -Term σ ∼ x₀:= N' • Sub↑ -Term σ' ⟧⟧
                           ≡ M ⟦⟦ pathsub↑ τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (P ⇑ ⇑) ⟧

postulate pathsub-compRP : ∀ {U} {V} {W} M {ρ : Rep V W} {τ : PathSub U V} {σ σ' : Sub U V} →
                         M ⟦⟦ ρ •RP τ ∶ ρ •RS σ ∼ ρ •RS σ' ⟧⟧ ≡ M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧ 〈 ρ 〉

\end{code}
x}

\end{frame}

\AgdaHide{
\begin{code}
_∶_⇒C_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set
_∶_⇒C_ {U} {V} σ Γ Δ = ∀ {K} (x : Var U K) → E' {V} Δ ((typeof x Γ) ⟦ σ ⟧) (σ _ x)

postulate change-codC : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} →
                     σ ∶ Γ ⇒C Δ → Δ ≡ Δ' → σ ∶ Γ ⇒C Δ'

idSubC : ∀ {V} {Γ : Context V} → idSub V ∶ Γ ⇒C Γ
idSubC {V} {Γ} x = subst (λ a → E' Γ a (var x)) (sym sub-idOp) var-E'

postulate compC : ∀ {U} {V} {W} {ρ : Sub V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                ρ ∶ Δ ⇒C Θ → σ ∶ Γ ⇒C Δ → ρ • σ ∶ Γ ⇒C Θ

postulate compRSC : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                 ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒C Δ → ρ •RS σ ∶ Γ ⇒C Θ

postulate compSRC : ∀ {U} {V} {W} {σ : Sub V W} {ρ : Rep U V} {Γ} {Δ} {Θ} →
                 σ ∶ Δ ⇒C Θ → ρ ∶ Γ ⇒R Δ → σ •SR ρ ∶ Γ ⇒C Θ

postulate Sub↑C : ∀ {U} {V} {σ : Sub U V} {K} {Γ} {Δ} {A} →
                    σ ∶ Γ ⇒C Δ → Sub↑ K σ ∶ (Γ , A) ⇒C (Δ , A ⟦ σ ⟧)

postulate botsubC : ∀ {V} {Γ : Context V} {M} {A} →
                    E Γ A M → x₀:= M ∶ (Γ ,T A) ⇒C Γ

postulate botsubCP : ∀ {V} {Γ : Context V} {δ} {φ} →
                     EP Γ φ δ → x₀:= δ ∶ (Γ ,P φ) ⇒C Γ

postulate botsubCE : ∀ {V} {Γ : Context V} {P} {E} →
                     EE Γ E P → x₀:= P ∶ (Γ ,E E) ⇒C Γ

postulate subC-typed : ∀ {U} {V} {σ : Sub U V} {Γ : Context U} {Δ : Context V} →
                     σ ∶ Γ ⇒C Δ → σ ∶ Γ ⇒ Δ

postulate subC-cong : ∀ {U} {V} {σ τ : Sub U V} {Γ} {Δ} →
                    σ ∶ Γ ⇒C Δ → σ ∼ τ → τ ∶ Γ ⇒C Δ

_∶_∼_∶_⇒C_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ = ∀ x → EE Δ (ρ _ x ≡〈 typeof' x Γ 〉 σ _ x) (τ x)

postulate change-ends : ∀ {U} {V} {τ : PathSub U V} {ρ} {ρ'} {σ} {σ'} {Γ} {Δ} → 
                      τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → ρ ∼ ρ' → σ ∼ σ' → τ ∶ ρ' ∼ σ' ∶ Γ ⇒C Δ

postulate extendPS-typedC : ∀ {U} {V} {τ : PathSub U V} {ρ σ : Sub U V} {Γ : Context U} {Δ : Context V} {A : Type} {Q : Path V} {N N' : Term V} →
                         τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → EE Δ (N ≡〈 A 〉 N') Q → extendPS τ Q ∶ x₀:= N • Sub↑ -Term ρ ∼ x₀:= N' • Sub↑ -Term σ ∶ Γ ,T A ⇒C Δ

postulate compRP-typedC : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} {σ} {σ'} {Γ} {Δ} {Θ} →
                         τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → ρ ∶ Δ ⇒R Θ → ρ •RP τ ∶ ρ •RS σ ∼ ρ •RS σ' ∶ Γ ⇒C Θ

postulate pathsubC-typed : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} → 
                     τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ

postulate pathsubC-valid₁ : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} →
                          τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → ρ ∶ Γ ⇒C Δ

postulate pathsubC-valid₂ : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} →
                          τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → σ ∶ Γ ⇒C Δ
\end{code}
}
