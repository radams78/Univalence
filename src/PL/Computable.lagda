\AgdaHide{
\begin{code}
module PL.Computable where
open import Data.Empty
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PL.Grammar
open PLgrammar
open import Grammar Propositional-Logic
open import Reduction Propositional-Logic β
open import PL.Rules
\end{code}
}

\subsubsection{Computable Terms}

We define the sets of \emph{computable} proofs $C_\Gamma(\phi)$ for each context $\Gamma$ and proposition $\phi$ as follows:

\begin{align*}
C_\Gamma(\bot) & = \{ \delta \mid \Gamma \vdash \delta : \bot \text{ and } \delta \in SN \} \\
C_\Gamma(\phi \rightarrow \psi) & = \{ \delta \mid \Gamma : \delta : \phi \rightarrow \psi \text{ and } \forall \Delta ⊇ \Gamma . ∀ \epsilon \in C_\Delta(\phi). \delta \epsilon \in C_\Delta(\psi) \}
\end{align*}

\begin{code}
C : ∀ {P} → Context P → Prp ∅ → Proof P → Set
C Γ (app -bot out) δ = Γ ⊢ δ ∶ ⊥P × SN δ
C Γ (app -imp (φ ∷ ψ ∷ out)) δ = Γ ⊢ δ ∶ (φ ⇛ ψ) 〈 magic 〉 × 
  (∀ Q {Δ : Context Q} ρ ε → ρ ∶ Γ ⇒R Δ → 
    C Δ φ ε → C Δ ψ (appP (δ 〈 ρ 〉) ε))
\end{code}

\begin{lemma}$ $
\begin{enumerate}
\item
If $\delta \in C_\Gamma(\phi)$ then $\Gamma \vdash \delta : \phi$.
\item
If $\delta \in C_\Gamma(\phi)$ and $\rho : \Gamma \rightarrow \Delta$ then $\delta \langle \rho \rangle \in C_\Delta(\phi)$.
\item
If $\delta \in C_\Gamma(\phi)$ and $\delta \rightarrow_\beta \epsilon$ then $\epsilon \in C_\Gamma(\phi)$.
\item
Let $\Gamma \vdash \delta : \phi$.  
If $\delta$ is neutral and, for all $\epsilon$ such that $\delta \rightarrow_\beta \epsilon$, we have $\epsilon \in C_\Gamma(\phi)$, then $\delta \in C_\Gamma(\phi)$.
\item
If $\delta \in C_\Gamma(\phi)$ then $\delta$ is strongly normalizable.
\end{enumerate}
\end{lemma}

\begin{code}
C-typed : ∀ {P} {Γ : Context P} {φ} {δ} → C Γ φ δ → Γ ⊢ δ ∶ φ 〈 magic 〉
\end{code}

\AgdaHide{
\begin{code}
C-typed {φ = app -bot []} = proj₁
C-typed {φ = app -imp (_ ∷ _ ∷ [])} = proj₁
\end{code}
}

\begin{code}
C-rep : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} {φ} {δ} {ρ} → 
  C Γ φ δ → ρ ∶ Γ ⇒R Δ → C Δ φ (δ 〈 ρ 〉)
\end{code}

\AgdaHide{
\begin{code}
C-rep {φ = app -bot []} (Γ⊢δ∶x₀ ,p SNδ) ρ∶Γ→Δ = (Weakening Γ⊢δ∶x₀ ρ∶Γ→Δ) ,p SNrep β-creates-rep SNδ
C-rep {P} {Q} {Γ} {Δ} {app -imp (φ ∷ ψ ∷ [])} {δ} {ρ} (Γ⊢δ∶φ⇒ψ ,p Cδ) ρ∶Γ→Δ = (subst 
  (λ x → Δ ⊢ δ 〈 ρ 〉 ∶ x) 
  (magic-unique' (φ ⇛ ψ))
  (Weakening Γ⊢δ∶φ⇒ψ ρ∶Γ→Δ)) ,p (λ R {Θ} σ ε σ∶Δ→Θ ε∈CΘ → subst (C Θ ψ) 
    (cong (λ x → appP x ε) (rep-comp δ))
    (Cδ R (σ •R ρ) ε (•R-typed {σ = σ} {ρ = ρ} ρ∶Γ→Δ σ∶Δ→Θ) ε∈CΘ))
\end{code}
}

\begin{code}
C-osr : ∀ {P} {Γ : Context P} φ {δ} {ε} → C Γ φ δ → δ ⇒ ε → C Γ φ ε
\end{code}

\AgdaHide{
\begin{code}
C-osr (app -bot []) (Γ⊢δ∶x₀ ,p SNδ) δ→ε = (subject-reduction Γ⊢δ∶x₀ δ→ε) ,p (SNred SNδ (osr-red δ→ε))
C-osr {Γ = Γ} (app -imp (_∷_ φ (_∷_ ψ []))) {δ = δ} (Γ⊢δ∶φ⇒ψ ,p Cδ) δ→δ' = subject-reduction Γ⊢δ∶φ⇒ψ δ→δ' ,p 
  (λ Q ρ ε ρ∶Γ→Δ ε∈Cφ → C-osr ψ (Cδ Q ρ ε ρ∶Γ→Δ ε∈Cφ) (app (appl (respects-osr REP β-respects-rep δ→δ'))))

C-red : ∀ {P} {Γ : Context P} φ {δ} {ε} → C Γ φ δ → δ ↠ ε → C Γ φ ε
C-red φ δ∈CΓφ (osr-red δ⇒ε) = C-osr φ δ∈CΓφ δ⇒ε
C-red _ δ∈CΓφ ref = δ∈CΓφ
C-red φ δ∈CΓφ (trans-red δ↠ε ε↠χ) = C-red φ (C-red φ δ∈CΓφ δ↠ε) ε↠χ
\end{code}
}

\begin{code}
NeutralC : ∀ {P} {Γ : Context P} {δ : Proof ( P)} (φ : Prp ∅) →
  Γ ⊢ δ ∶ φ 〈 magic 〉 → Neutral δ →
  (∀ ε → δ ⇒ ε → C Γ φ ε) →
  C Γ φ δ

CsubSN : ∀ {P} {Γ : Context P} φ {δ} → C Γ φ δ → SN δ
\end{code}

\AgdaHide{
\begin{code}
NeutralC {P} {Γ} {δ} {app -bot []} Γ⊢δ∶x₀ Neutralδ hyp = Γ⊢δ∶x₀ ,p SNI δ (λ ε δ→ε → proj₂ (hyp ε δ→ε))
NeutralC {P} {Γ} {δ} {app -imp (_∷_ φ (_∷_ ψ []))} Γ⊢δ∶φ→ψ neutralδ hyp = Γ⊢δ∶φ→ψ ,p 
  (λ Q ρ ε ρ∶Γ→Δ ε∈Cφ → claim ε (CsubSN φ {δ = ε} ε∈Cφ) ρ∶Γ→Δ ε∈Cφ) where
  claim : ∀ {Q} {Δ} {ρ : Rep P Q} ε → SN ε → ρ ∶ Γ ⇒R Δ → C Δ φ ε → C Δ ψ (appP (δ 〈  ρ 〉) ε)
  claim {Q} {Δ} {ρ} ε (SNI .ε SNε) ρ∶Γ→Δ ε∈Cφ = NeutralC {Q} {Δ} {appP (δ 〈  ρ 〉) ε} ψ
      (app (subst (λ P₁ → Δ ⊢ δ 〈 ρ 〉 ∶ P₁) 
      (magic-unique' (φ ⇛ ψ))
      (Weakening Γ⊢δ∶φ→ψ ρ∶Γ→Δ)) 
      (C-typed {Q} {Δ} {φ} {ε} ε∈Cφ)) 
      (appNeutral (δ 〈  ρ 〉) ε)
      (NeutralC-lm {X = C Δ ψ} (neutral-rep neutralδ) 
      (λ δ' δ〈ρ〉→δ' → 
        let δ-creation = create-osr β-creates-rep δ δ〈ρ〉→δ' in 
        let open creation δ-creation renaming (created to δ₀;red-created to δ⇒δ₀;ap-created to δ₀〈ρ〉≡δ') in
        let δ₀∈C[φ⇒ψ] : C Γ (φ ⇛ ψ) δ₀
            δ₀∈C[φ⇒ψ] = hyp δ₀ δ⇒δ₀
        in let δ'∈C[φ⇒ψ] : C Δ (φ ⇛ ψ) δ'
               δ'∈C[φ⇒ψ] = subst (C Δ (φ ⇛ ψ)) δ₀〈ρ〉≡δ' (C-rep {φ = φ ⇛ ψ} δ₀∈C[φ⇒ψ] ρ∶Γ→Δ)
        in subst (C Δ ψ) (cong (λ x → appP x ε) δ₀〈ρ〉≡δ') (proj₂ δ₀∈C[φ⇒ψ] Q ρ ε ρ∶Γ→Δ ε∈Cφ))
      (λ ε' ε→ε' → claim ε' (SNε ε' ε→ε') ρ∶Γ→Δ (C-osr φ ε∈Cφ ε→ε')))

CsubSN {P} {Γ} {app -bot []} = proj₂
CsubSN {P} {Γ} {app -imp (φ ∷ ψ ∷ [])} {δ} P₁ = 
    SNap' {REP} {P} {P , -proof} {E = δ} {σ = upRep} β-respects-rep
      (SNsubbodyl (SNsubexp (CsubSN {Γ = Γ ,P φ 〈 magic 〉} ψ
      (proj₂ P₁ (P , -proof) upRep (var x₀) (λ _ → refl)
      (NeutralC φ
        (subst (λ x → (Γ ,P φ 〈 magic 〉) ⊢ var x₀ ∶ x) 
          (magic-unique' φ) var) 
        (varNeutral x₀) 
        (λ _ ()))))))
\end{code}
}

\begin{corollary}
If $p : \phi \in \Gamma$ then $p \in C_\Gamma(\phi)$.
\end{corollary}

\begin{code}
varC : ∀ {P} {Γ : Context P} {x : Var P -proof} → 
  C Γ (close (typeof x Γ)) (var x)
\end{code}

\AgdaHide{
\begin{code}
varC {P} {Γ} {x} = NeutralC (close (typeof x Γ)) (change-type (sym close-magic) var) (varNeutral x) (λ ε ())
\end{code}
}

\begin{lemma}[Computability is preserved under well-typed expansion]
Suppose $\Gamma, p : \phi \vdash \delta : \psi$ and $\Gamma \vdash \epsilon : \phi$.  If
$\delta[p:=\epsilon] \in C_\Gamma(\psi)$ and $\epsilon \in SN$, then $(\lambda p:\phi.\delta)\epsilon \in C_\Gamma(\psi)$.
\end{lemma}

\AgdaHide{
\begin{code}
WTEaux : ∀ {P} {Γ : Context P} {φ} {δ} ψ {ε} →
  Γ ,P φ ⊢ δ ∶ ψ 〈 magic 〉 →
  Γ ⊢ ε ∶ φ →
  C Γ ψ (δ ⟦ x₀:= ε ⟧) →
  SN δ → SN ε →
  C Γ ψ (appP (ΛP φ δ) ε)
WTEaux {Γ = Γ} {φ = φ} ψ Γ,p∶φ⊢δ∶ψ Γ⊢ε∶φ δ[p∶=ε]∈CΓψ (SNI δ SNδ) (SNI ε SNε) = NeutralC {Γ = Γ} {δ = appP (ΛP φ δ) ε} ψ
  (app (Λ (change-type 
    (let open ≡-Reasoning in 
    begin
      ψ 〈 magic 〉
    ≡⟨ rep-congr (λ ()) ψ ⟩
      ψ 〈 upRep •R magic 〉
    ≡⟨ rep-comp ψ ⟩
      ψ 〈 magic 〉 〈 upRep 〉
    ∎) 
  Γ,p∶φ⊢δ∶ψ)) Γ⊢ε∶φ) 
  (appNeutral _ _) 
  (λ χ Λφδε⇒χ → red-β-redex (C Γ ψ) Λφδε⇒χ δ[p∶=ε]∈CΓψ
    (λ δ' δ⇒δ' → WTEaux ψ
      (subject-reduction Γ,p∶φ⊢δ∶ψ δ⇒δ') 
      Γ⊢ε∶φ 
      (C-osr ψ δ[p∶=ε]∈CΓψ (respects-osr SUB β-respects-sub δ⇒δ')) 
      (SNδ δ' δ⇒δ') (SNI ε SNε)) 
    (λ ε' ε⇒ε' → WTEaux ψ
    Γ,p∶φ⊢δ∶ψ 
    (subject-reduction Γ⊢ε∶φ ε⇒ε') 
    (C-red ψ {δ ⟦ x₀:= ε ⟧} {δ ⟦ x₀:= ε' ⟧} δ[p∶=ε]∈CΓψ (apredl SUB {E = δ} β-respects-sub (botsub-red ε⇒ε'))) 
    (SNI δ SNδ) (SNε _ ε⇒ε')))
\end{code}
}

\begin{code}
WTE : ∀ {P} {Γ : Context P} {φ} {δ} {ψ} {ε} →
  Γ ,P φ ⊢ δ ∶ ψ 〈 magic 〉 →
  Γ ⊢ ε ∶ φ →
  C Γ ψ (δ ⟦ x₀:= ε ⟧) →
  SN ε →
  C Γ ψ (appP (ΛP φ δ) ε)
\end{code}

\AgdaHide{
\begin{code}
WTE {ψ = ψ} Γ,p∶φ⊢δ∶ψ Γ⊢ε∶φ δ[p∶=ε]∈CΓψ = WTEaux ψ Γ,p∶φ⊢δ∶ψ Γ⊢ε∶φ δ[p∶=ε]∈CΓψ (SNap' {SUB} β-respects-sub (CsubSN ψ δ[p∶=ε]∈CΓψ))
\end{code}
}

\begin{prop}
If $\Gamma \vdash \delta : \phi$ and $\sigma : \Gamma \rightarrow \Delta$ then $\delta [ \sigma ] \in C_\Delta(\phi)$.
\end{prop}

\begin{code}
SNmainlemma : ∀ {P} {Q} {Γ : Context P} {δ} {φ} {σ : Sub P Q} {Δ} →
  Γ ⊢ δ ∶ φ →
  (∀ x → C Δ (close (typeof {K = -proof} x Γ)) (σ _ x)) →
  C Δ (close φ) (δ ⟦ σ ⟧)
\end{code}

\AgdaHide{
\begin{code}
--TODO Tidy up
SNmainlemma (var {p = p}) hyp = hyp p
SNmainlemma {P} {Q} {Γ} {σ = σ} {Δ} (app {δ = δ} {ε} {φ} {ψ} Γ⊢δ∶φ⇛ψ Γ⊢ε∶φ) hyp = 
  subst (C Δ (close ψ)) (cong (λ M → appP M (ε ⟦ σ ⟧)) rep-idOp) 
    (proj₂ (SNmainlemma Γ⊢δ∶φ⇛ψ hyp) Q (idRep Q) (ε ⟦ σ ⟧) idRep-typed 
      (SNmainlemma Γ⊢ε∶φ hyp))
SNmainlemma {P} {Q} {Γ} {σ = σ} {Δ} (Λ {φ = φ} {δ} {ψ} Γ,φ⊢δ∶ψ) hyp = 
  let σ∶Γ⇒Δ : σ ∶ Γ ⇒ Δ
      σ∶Γ⇒Δ = λ x → change-type 
        (let open ≡-Reasoning in 
        begin
          close (typeof x Γ) 〈 magic 〉
        ≡⟨⟨ cong (λ E → E 〈 magic 〉) (close-sub (typeof x Γ)) ⟩⟩
          close (typeof x Γ ⟦ σ ⟧) 〈 magic 〉
        ≡⟨ close-magic ⟩
          typeof x Γ ⟦ σ ⟧
        ∎) 
        (C-typed {φ = close (typeof x Γ)} (hyp x))
  in
  subst (λ A → Δ ⊢ (ΛP φ δ) ⟦ σ ⟧ ∶ A) (close-magic' {φ = φ ⇛ ψ})
  (Λ {Γ = Δ} {φ = φ ⟦ σ ⟧} {δ = δ ⟦ liftSub -proof σ ⟧} {ψ = ψ ⟦ σ ⟧} 
    (subst (λ A → (Δ ,P (φ ⟦ σ ⟧)) ⊢ δ ⟦ liftSub -proof σ ⟧ ∶ A) 
    (let open ≡-Reasoning in 
    begin
      ψ 〈 upRep 〉 ⟦ liftSub -proof σ ⟧
    ≡⟨⟨ sub-compSR ψ ⟩⟩
      ψ ⟦ liftSub -proof σ •SR upRep ⟧
    ≡⟨⟩
      ψ ⟦ upRep •RS σ ⟧
    ≡⟨ sub-compRS ψ ⟩
      ψ ⟦ σ ⟧ 〈 upRep 〉
    ∎)
  (substitution Γ,φ⊢δ∶ψ (liftSub-typed (λ x → 
    subst (λ A → Δ ⊢ σ _ x ∶ A) (sym (close-magic' {φ = typeof x Γ})) (C-typed {Γ = Δ} {φ = close (typeof x Γ)} (hyp x)))))))
  ,p (λ R {Θ} ρ ε ρ∶Δ→Θ ε∈CΘφ → WTE {ψ = close ψ} 
       (change-type 
         (let open ≡-Reasoning in 
         begin
           ψ 〈 upRep 〉 ⟦ liftSub -proof σ ⟧ 〈 liftRep -proof ρ 〉
         ≡⟨⟨ close-magic ⟩⟩
           close (ψ 〈 upRep 〉 ⟦ liftSub -proof σ ⟧ 〈 liftRep -proof ρ 〉) 〈 magic 〉
         ≡⟨ cong (λ E → E 〈 magic 〉) (trans (trans (close-rep (ψ 〈 upRep 〉 ⟦ liftSub -proof σ ⟧)) (close-sub (ψ 〈 upRep 〉))) (close-rep ψ)) ⟩
           close ψ 〈 magic 〉
         ∎)
         (Weakening (substitution Γ,φ⊢δ∶ψ (liftSub-typed σ∶Γ⇒Δ)) (liftRep-typed ρ∶Δ→Θ))) 
       (change-type 
         (let open ≡-Reasoning in 
         begin
           close φ 〈 magic 〉
         ≡⟨⟨ rep-congl (close-sub φ) ⟩⟩
           close (φ ⟦ ρ •RS σ ⟧) 〈 magic 〉
         ≡⟨ close-magic ⟩ 
           φ ⟦ ρ •RS σ ⟧
         ≡⟨ sub-compRS φ ⟩
           φ ⟦ σ ⟧ 〈 ρ 〉
         ∎) 
         (C-typed {φ = close φ} ε∈CΘφ)) --TODO Make argument explicit in C-typed?
       (subst₂ (C Θ)
         (close-rep ψ)
         (let open ≡-Reasoning in 
         begin
           δ ⟦ x₀:= ε •SR liftRep -proof ρ • liftSub -proof σ ⟧
         ≡⟨ sub-comp δ ⟩
           δ ⟦ liftSub -proof σ ⟧ ⟦ x₀:= ε •SR liftRep -proof ρ ⟧
         ≡⟨ sub-compSR (δ ⟦ liftSub -proof σ ⟧) ⟩
           δ ⟦ liftSub -proof σ ⟧ 〈 liftRep -proof ρ 〉 ⟦ x₀:= ε ⟧
         ∎)
         (SNmainlemma {σ = x₀:= ε •SR liftRep -proof ρ • liftSub -proof σ} Γ,φ⊢δ∶ψ (λ x → aux x ε∈CΘφ ρ∶Δ→Θ))) 
       (CsubSN (close φ) ε∈CΘφ)) where
    aux : ∀ {R} {Θ : Context R} {ρ} {ε} x → 
      C Θ (close φ) ε →
      ρ ∶ Δ ⇒R Θ → 
      C Θ (close (typeof {K = -proof} x (Γ ,P φ))) ((x₀:= ε •SR liftRep -proof ρ • liftSub -proof σ) -proof x)
    aux {Θ = Θ} {ε = ε} x₀ ε∈CΘφ _ = subst (λ P₁ → C Θ P₁ ε) 
      (let open ≡-Reasoning in
      begin
        close φ
      ≡⟨⟨ close-rep φ ⟩⟩
        close (φ 〈 upRep 〉)
      ∎) ε∈CΘφ
    aux {Θ = Θ} {ρ} {ε} (↑ x) _ ρ:Δ→Θ = subst₂ (C Θ) 
      (let open ≡-Reasoning in
      begin
        close (typeof x Γ)
      ≡⟨⟨ close-rep (typeof x Γ) ⟩⟩
        close (typeof x Γ 〈 upRep 〉)
      ≡⟨⟩
        close (typeof (↑ x) (Γ ,P φ))
      ∎) 
      (let open ≡-Reasoning in
      begin
        σ -proof x 〈 ρ 〉
      ≡⟨⟨ botSub-upRep _ ⟩⟩
        σ -proof x 〈 ρ 〉 〈 upRep 〉 ⟦ x₀:= ε ⟧
      ≡⟨⟨ cong (λ E → E ⟦ x₀:= ε ⟧) (liftRep-upRep (σ -proof x)) ⟩⟩
        σ -proof x 〈 upRep 〉 〈 liftRep -proof ρ 〉 ⟦ x₀:= ε ⟧
      ≡⟨⟨ sub-compSR (σ -proof x 〈 upRep 〉) ⟩⟩
        (σ -proof x 〈 upRep 〉) ⟦ x₀:= ε •SR liftRep -proof ρ ⟧
      ∎) 
      (C-rep {φ = close (typeof x Γ)} (hyp x) ρ:Δ→Θ)
\end{code}
}

\begin{theorem}
Propositional Logic is strongly normalizing.
\end{theorem}

\begin{code}
Strong-Normalization : ∀ {P} {Γ : Context P} {δ} {φ} → Γ ⊢ δ ∶ φ → SN δ
\end{code}

\AgdaHide{
\begin{code}
Strong-Normalization {P} {Γ} {δ} {φ} Γ⊢δ:φ = subst SN 
  sub-idOp 
  (CsubSN (close φ) {δ ⟦ idSub P ⟧}
  (SNmainlemma Γ⊢δ:φ (λ x → varC {x = x})))
\end{code}
}
