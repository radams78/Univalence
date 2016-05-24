\AgdaHide{
\begin{code}
module PHOPL.Meta where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Red
open import PHOPL.Rules
open import PHOPL.PathSub

Context-Validity : ∀ {V} {Γ} {K} {M : Expression V (varKind K)} {A} →
                   Γ ⊢ M ∶ A → valid Γ
Context-Validity'' : ∀ {V} {Γ : Context V} {A} → valid (addpath Γ A) → valid Γ
--BUG "with" does not work on lines 8 and 15below

Context-Validity (varR _ validΓ) = validΓ
Context-Validity (appR Γ⊢M∶A⇛B _) = Context-Validity Γ⊢M∶A⇛B
Context-Validity (ΛR Γ,A⊢M∶B) with Context-Validity Γ,A⊢M∶B
Context-Validity (ΛR _) | ctxTR validΓ = validΓ
Context-Validity (⊥R validΓ) = validΓ
Context-Validity (⊃R Γ⊢φ∶Ω _) = Context-Validity Γ⊢φ∶Ω
Context-Validity (appPR Γ⊢δ∶φ⊃ψ _) = Context-Validity Γ⊢δ∶φ⊃ψ
Context-Validity (ΛPR Γ⊢φ∶Ω _) = Context-Validity Γ⊢φ∶Ω
Context-Validity (convR Γ⊢M∶A _ _) = Context-Validity Γ⊢M∶A
Context-Validity (refR Γ⊢M∶A) = Context-Validity Γ⊢M∶A
Context-Validity (⊃*R Γ⊢φ∶Ω _) = Context-Validity Γ⊢φ∶Ω
Context-Validity (univR Γ⊢δ∶φ⊃ψ _) = Context-Validity Γ⊢δ∶φ⊃ψ
Context-Validity (plusR Γ⊢P∶φ≡ψ) = Context-Validity Γ⊢P∶φ≡ψ
Context-Validity (minusR Γ⊢P∶φ≡ψ) = Context-Validity Γ⊢P∶φ≡ψ
Context-Validity (lllR addpathΓ⊢P∶M≡N) = Context-Validity'' (Context-Validity addpathΓ⊢P∶M≡N)
Context-Validity (app*R Γ⊢N∶A _ _ _) = Context-Validity Γ⊢N∶A
Context-Validity (convER Γ⊢P∶M≡N _ _ _ _) = Context-Validity Γ⊢P∶M≡N

Context-Validity'' (ctxER (varR .(↑ x₀) (ctxTR (ctxTR validΓ))) _) = validΓ


postulate Prop-Validity : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} → 
                        Γ ⊢ δ ∶ φ → Γ ⊢ φ ∶ ty Ω

postulate _∶_⇒R_ : ∀ {U} {V} → Rep U V → Context U → Context V → Set

postulate change-codR : ∀ {U} {V} {ρ : Rep U V} {Γ : Context U} {Δ Δ' : Context V} →
                      ρ ∶ Γ ⇒R Δ → Δ ≡ Δ' → ρ ∶ Γ ⇒R Δ'

postulate idRep-typed : ∀ {V} {Γ : Context V} → idRep V ∶ Γ ⇒R Γ

postulate upRep-typed : ∀ {V} {Γ : Context V} {K} {A} → upRep ∶ Γ ⇒R _,_ {K = K} Γ A

postulate Rep↑-typed : ∀ {U} {V} {ρ : Rep U V} {K} {Γ} {Δ} {A} →
                     ρ ∶ Γ ⇒R Δ → Rep↑ K ρ ∶ (Γ , A) ⇒R (Δ , A 〈 ρ 〉)

postulate compR-typed : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Rep U V} {Γ} {Δ} {Θ : Context W} →
                        ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒R Δ → ρ •R σ ∶ Γ ⇒R Θ

postulate Weakening : ∀ {U} {V} {ρ : Rep U V} {K}
                    {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
                    Γ ⊢ M ∶ A → valid Δ → ρ ∶ Γ ⇒R Δ → Δ ⊢ M 〈 ρ 〉 ∶ A 〈 ρ 〉

postulate _∶_⇒_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set

postulate Substitution : ∀ {U} {V} {σ : Sub U V} {K}
                       {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
                       Γ ⊢ M ∶ A → valid Δ → σ ∶ Γ ⇒ Δ → Δ ⊢ M ⟦ σ ⟧ ∶ A ⟦ σ ⟧

postulate comp-typed : ∀ {U} {V} {W} {σ : Sub V W} {ρ : Sub U V} {Γ} {Δ} {Θ} →
                         σ ∶ Δ ⇒ Θ → ρ ∶ Γ ⇒ Δ → σ • ρ ∶ Γ ⇒ Θ

postulate compRS-typed : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                      ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒ Δ → ρ •RS σ ∶ Γ ⇒ Θ

postulate Sub↑-typed : ∀ {U} {V} {K} {σ : Sub U V} {Γ} {Δ} {A} →
                     σ ∶ Γ ⇒ Δ → Sub↑ K σ ∶ Γ , A ⇒ Δ , A ⟦ σ ⟧

postulate change-type : ∀ {V} {Γ} {K} {M : Expression V (varKind K)} {A} {B} →
                      Γ ⊢ M ∶ A → A ≡ B → Γ ⊢ M ∶ B

postulate botsub-typed : ∀ {V} {K} {Γ} {E : Expression V (varKind K)} {A} → Γ ⊢ E ∶ A → x₀:= E ∶ Γ , A ⇒ Γ

lemma : ∀ {U} {V} {W} {K} (M : Expression U K) Q N' N (ρ : Rep V W) (σ : Sub U V) → M ⇑ ⇑ ⇑ ⟦ x₀:= Q • Sub↑ -Path (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •RS σ))) ⟧ ≡ M ⟦ σ ⟧ 〈 ρ 〉 --TODO Rename
lemma {U} {V} {W} M Q N' N ρ σ = let open ≡-Reasoning in 
          begin
            M ⇑ ⇑ ⇑ ⟦ x₀:= Q • Sub↑ -Path (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •RS σ))) ⟧
          ≡⟨ sub-comp (M ⇑ ⇑ ⇑) ⟩
            M ⇑ ⇑ ⇑ ⟦ Sub↑ -Path (x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •RS σ))) ⟧ ⟦ x₀:= Q ⟧
          ≡⟨ sub-congl (Sub↑-upRep (M ⇑ ⇑)) ⟩
            M ⇑ ⇑ ⟦ x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •RS σ)) ⟧ ⇑ ⟦ x₀:= Q ⟧
          ≡⟨ botsub-upRep _ ⟩
            M ⇑ ⇑ ⟦ x₀:= N' • Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •RS σ)) ⟧
          ≡⟨ sub-comp (M ⇑ ⇑) ⟩
            M ⇑ ⇑ ⟦ Sub↑ -Term (x₀:= N • Sub↑ -Term (ρ •RS σ)) ⟧ ⟦ x₀:= N' ⟧
          ≡⟨ sub-congl (Sub↑-upRep (M ⇑)) ⟩
            M ⇑ ⟦ x₀:= N • Sub↑ -Term (ρ •RS σ) ⟧ ⇑ ⟦ x₀:= N' ⟧
          ≡⟨ botsub-upRep _ ⟩
            M ⇑ ⟦ x₀:= N • Sub↑ -Term (ρ •RS σ) ⟧
          ≡⟨ sub-comp (M ⇑) ⟩
            M ⇑ ⟦ Sub↑ -Term (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧
          ≡⟨ sub-congl (Sub↑-upRep M) ⟩
            M ⟦ ρ •RS σ ⟧ ⇑ ⟦ x₀:= N ⟧
          ≡⟨ botsub-upRep _ ⟩
            M ⟦ ρ •RS σ ⟧
          ≡⟨ sub-compRS M ⟩
            M ⟦ σ ⟧ 〈 ρ 〉
          ∎

postulate change-cod' : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} → σ ∶ Γ ⇒ Δ → Δ ≡ Δ' → σ ∶ Γ ⇒ Δ'

extendSub : ∀ {U} {V} → Sub U V → Term V → Sub (U , -Term) V
extendSub σ M _ x₀ = M
extendSub σ M _ (↑ x) = σ _ x

postulate ⊃-gen₁ : ∀ {V} {Γ : Context V} {φ} {ψ} → Γ ⊢ φ ⊃ ψ ∶ ty Ω → Γ ⊢ φ ∶ ty Ω

postulate ⊃-gen₂ : ∀ {V} {Γ : Context V} {φ} {ψ} → Γ ⊢ φ ⊃ ψ ∶ ty Ω → Γ ⊢ ψ ∶ ty Ω

postulate Type-Reduction : ∀ {V} {Γ : Context V} {K} {M : Expression V (varKind K)} {A} {B} →
                         Γ ⊢ M ∶ A → A ↠ B → Γ ⊢ M ∶ B

postulate change-cod : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} → σ ∶ Γ ⇒ Δ → Δ ≡ Δ' → σ ∶ Γ ⇒ Δ'
postulate sub↖-typed : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {A} → σ ∶ Γ ⇒ Δ → sub↖ σ ∶ Γ ,T A ⇒ Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀

postulate sub↗-typed : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {A} → σ ∶ Γ ⇒ Δ → sub↗ σ ∶ Γ ,T A ⇒ Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀
\end{code}
}

\begin{frame}[fragile]
\frametitle{Subject Reduction}

\begin{theorem}[Subject Reduction]
Let $E$ be a path (proof, term) and $A$ an equation (term, type).
If $\Gamma \vdash E : A$ and $E \twoheadrightarrow F$ then $\Gamma \vdash F : A$.
\end{theorem}

\AgdaHide{
\begin{code}
postulate Generation-ΛP : ∀ {V} {Γ : Context V} {φ} {δ} {ε} {ψ} →
                          Γ ⊢ appP (ΛP φ δ) ε ∶ ψ →
                          Σ[ χ ∈ Term V ] 
                          (ψ ≃ φ ⊃ χ × Γ ,P φ ⊢ δ ∶ χ ⇑)

postulate Subject-Reduction-R : ∀ {V} {K} {C} 
                              {c : Constructor C} {E : Body V C} {F : Expression V (varKind K)} {Γ} {A} →
                              Γ ⊢ (app c E) ∶ A → R c E F → Γ ⊢ F ∶ A

{-Subject-Reduction-R : ∀ {V} {K} {C} 
  {c : Constructor C} {E : Body V C} {F : Expression V (varKind K)} {Γ} {A} →
  Γ ⊢ (app c E) ∶ A → R c E F → Γ ⊢ F ∶ A
Subject-Reduction-R Γ⊢ΛPφδε∶A βR =
  let (χ ,p A≃φ⊃χ ,p Γ,φ⊢δ∶χ) = Generation-ΛP Γ⊢ΛPφδε∶A in {!!}
Subject-Reduction-R Γ⊢cE∶A βE = {!!}
Subject-Reduction-R Γ⊢cE∶A plus-ref = {!!}
Subject-Reduction-R Γ⊢cE∶A minus-ref = {!!}
Subject-Reduction-R Γ⊢cE∶A plus-univ = {!!}
Subject-Reduction-R Γ⊢cE∶A minus-univ = {!!}
Subject-Reduction-R Γ⊢cE∶A ref⊃*univ = {!!}
Subject-Reduction-R Γ⊢cE∶A univ⊃*ref = {!!}
Subject-Reduction-R Γ⊢cE∶A univ⊃*univ = {!!}
Subject-Reduction-R Γ⊢cE∶A ref⊃*ref = {!!}
Subject-Reduction-R Γ⊢cE∶A refref = {!!}
Subject-Reduction-R Γ⊢cE∶A lllred = {!!}
Subject-Reduction-R Γ⊢cE∶A reflamvar = {!!}
Subject-Reduction-R Γ⊢cE∶A reflam⊃* = {!!}
Subject-Reduction-R Γ⊢cE∶A reflamuniv = {!!}
Subject-Reduction-R Γ⊢cE∶A reflamλλλ = {!!} -}
\end{code}
}

\begin{code}
postulate Subject-Reduction : ∀ {V} {K} {Γ}
                            {E F : Expression V (varKind K)} {A} → 
                            (Γ ⊢ E ∶ A) → (E ↠ F) → (Γ ⊢ F ∶ A)

postulate Equation-Validity₁ : ∀ {V} {Γ : Context V} {P : Path V} {M} {A} {N} →
                             Γ ⊢ P ∶ M ≡〈 A 〉 N → Γ ⊢ M ∶ ty A

postulate Equation-Validity₂ : ∀ {V} {Γ : Context V} {P : Path V} {M} {A} {N} →
                             Γ ⊢ P ∶ M ≡〈 A 〉 N → Γ ⊢ N ∶ ty A

postulate ⋆-typed : ∀ {V} {M : Term V} {P N N' Γ A B} → 
                  Γ ⊢ M ∶ ty (A ⇛ B) → Γ ⊢ P ∶ N ≡〈 A 〉 N' → Γ ⊢ M ⋆[ P ∶ N ∼ N' ] ∶ appT M N ≡〈 B 〉 appT M N'

valid-addpath : ∀ {V} {Γ : Context V} {A} → valid Γ → valid (addpath Γ A)
valid-addpath validΓ = ctxER (varR x₁ (ctxTR (ctxTR validΓ))) (varR x₀ (ctxTR (ctxTR validΓ)))
\end{code}

