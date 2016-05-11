\AgdaHide{
\begin{code}
module PL.Computable where
open import Data.Empty
open import Data.Product
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
C_\Gamma(\bot) & = \{ \delta \mid \Gamma \vdash \delta : \bot, \delta \in SN \} \\
C_\Gamma(\phi \rightarrow \psi) & = \{ \delta \mid \Gamma : \delta : \phi \rightarrow \psi, \forall \epsilon \in C_\Gamma(\phi). \delta \epsilon \in C_\Gamma(\psi) \}
\end{align*}

\begin{code}
C : ∀ {P} → Context P → Prp ∅ → Proof P → Set
C Γ (app -bot out) δ = Γ ⊢ δ ∶ ⊥P × SN δ
C Γ (app -imp (φ ,, ψ ,, out)) δ = Γ ⊢ δ ∶ (φ ⇛ ψ) 〈 magic 〉 × 
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
C-typed {φ = app -bot out} = proj₁
C-typed {φ = app -imp (_ ,, _ ,, out)} = proj₁
\end{code}
}

\begin{code}
C-rep : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} {φ} {δ} {ρ} → 
  C Γ φ δ → ρ ∶ Γ ⇒R Δ → C Δ φ (δ 〈 ρ 〉)
\end{code}

\AgdaHide{
\begin{code}
C-rep {φ = app -bot out} (Γ⊢δ∶x₀ , SNδ) ρ∶Γ→Δ = (Weakening Γ⊢δ∶x₀ ρ∶Γ→Δ) , SNap β-creates-rep SNδ
C-rep {P} {Q} {Γ} {Δ} {app -imp (φ ,, ψ ,, out)} {δ} {ρ} (Γ⊢δ∶φ⇒ψ , Cδ) ρ∶Γ→Δ = (subst 
  (λ x → Δ ⊢ δ 〈 ρ 〉 ∶ x) 
  (magic-unique' (φ ⇛ ψ))
  (Weakening Γ⊢δ∶φ⇒ψ ρ∶Γ→Δ)) , (λ R {Θ} σ ε σ∶Δ→Θ ε∈CΘ → subst (C Θ ψ) 
    (cong (λ x → appP x ε) (rep-comp δ))
    (Cδ R (σ •R ρ) ε (•R-typed {σ = σ} {ρ = ρ} ρ∶Γ→Δ σ∶Δ→Θ) ε∈CΘ))
\end{code}
}

\begin{code}
C-osr : ∀ {P} {Γ : Context P} φ {δ} {ε} → C Γ φ δ → δ ⇒ ε → C Γ φ ε
\end{code}

\AgdaHide{
\begin{code}
C-osr (app -bot out) (Γ⊢δ∶x₀ , SNδ) δ→ε = (SR Γ⊢δ∶x₀ δ→ε) , (SNred SNδ (osr-red δ→ε))
C-osr {Γ = Γ} (app -imp (_,,_ φ (_,,_ ψ out))) {δ = δ} (Γ⊢δ∶φ⇒ψ , Cδ) δ→δ' = SR Γ⊢δ∶φ⇒ψ δ→δ' , 
  (λ Q ρ ε ρ∶Γ→Δ ε∈Cφ → C-osr ψ (Cδ Q ρ ε ρ∶Γ→Δ ε∈Cφ) (app (appl (Respects-Creates.respects-osr replacement β-respects-rep δ→δ'))))

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
NeutralC {P} {Γ} {δ} {app -bot out} Γ⊢δ∶x₀ Neutralδ hyp = Γ⊢δ∶x₀ , SNI δ (λ ε δ→ε → proj₂ (hyp ε δ→ε))
NeutralC {P} {Γ} {δ} {app -imp (_,,_ φ (_,,_ ψ out))} Γ⊢δ∶φ→ψ neutralδ hyp = Γ⊢δ∶φ→ψ , 
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
        let open Respects-Creates.creation δ-creation renaming (created to δ₀;red-created to δ⇒δ₀;ap-created to δ₀〈ρ〉≡δ') in
        let δ₀∈C[φ⇒ψ] : C Γ (φ ⇛ ψ) δ₀
            δ₀∈C[φ⇒ψ] = hyp δ₀ δ⇒δ₀
        in let δ'∈C[φ⇒ψ] : C Δ (φ ⇛ ψ) δ'
               δ'∈C[φ⇒ψ] = subst (C Δ (φ ⇛ ψ)) δ₀〈ρ〉≡δ' (C-rep {φ = φ ⇛ ψ} δ₀∈C[φ⇒ψ] ρ∶Γ→Δ)
        in subst (C Δ ψ) (cong (λ x → appP x ε) δ₀〈ρ〉≡δ') (proj₂ δ₀∈C[φ⇒ψ] Q ρ ε ρ∶Γ→Δ ε∈Cφ))
      (λ ε' ε→ε' → claim ε' (SNε ε' ε→ε') ρ∶Γ→Δ (C-osr φ ε∈Cφ ε→ε')))

CsubSN {P} {Γ} {app -bot out} = proj₂
CsubSN {P} {Γ} {app -imp (φ ,, ψ ,, out)} {δ} P₁ = 
    SNap' {replacement} {P} {P , -proof} {E = δ} {σ = upRep} β-respects-rep
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
varC : ∀ {P} {Γ : Context P} {x : Var P -proof} → C Γ (close (typeof x Γ)) (var x)
varC {P} {Γ} {x} = NeutralC (close (typeof x Γ)) (change-type (sym close-magic) var) (varNeutral x) (λ ε ())
\end{code}

\begin{lemma}[Computability is preserved under well-typed expansion]
Suppose $\Gamma, p : \phi \vdash \delta : \psi$ and $\Gamma \vdash \epsilon : \phi$.  If
$\delta[p:=\epsilon] \in C_\Gamma(\psi)$ and $\epsilon \in SN$, then $(\lambda p:\phi.\delta)\epsilon \in C_\Gamma(\psi)$.
\end{lemma}

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
    ≡⟨ rep-cong ψ (λ ()) ⟩
      ψ 〈 upRep •R magic 〉
    ≡⟨ rep-comp ψ ⟩
      ψ 〈 magic 〉 〈 upRep 〉
    ∎) 
  Γ,p∶φ⊢δ∶ψ)) Γ⊢ε∶φ) 
  (appNeutral _ _) 
  (λ χ Λφδε⇒χ → red-β-redex (C Γ ψ) Λφδε⇒χ δ[p∶=ε]∈CΓψ
    (λ δ' δ⇒δ' → WTEaux ψ
      (SR Γ,p∶φ⊢δ∶ψ δ⇒δ') 
      Γ⊢ε∶φ 
      (C-osr ψ δ[p∶=ε]∈CΓψ (respects-osr substitution β-respects-sub δ⇒δ')) 
      (SNδ δ' δ⇒δ') (SNI ε SNε)) 
    (λ ε' ε⇒ε' → WTEaux ψ
    Γ,p∶φ⊢δ∶ψ 
    (SR Γ⊢ε∶φ ε⇒ε') 
    (C-red ψ {δ ⟦ x₀:= ε ⟧} {δ ⟦ x₀:= ε' ⟧} δ[p∶=ε]∈CΓψ (apredl substitution {E = δ} β-respects-sub (botsub-red ε⇒ε'))) 
    (SNI δ SNδ) (SNε _ ε⇒ε')))

WTE : ∀ {P} {Γ : Context P} {φ} {δ} {ψ} {ε} →
  Γ ,P φ ⊢ δ ∶ ψ 〈 magic 〉 →
  Γ ⊢ ε ∶ φ →
  C Γ ψ (δ ⟦ x₀:= ε ⟧) →
  SN ε →
  C Γ ψ (appP (ΛP φ δ) ε)

WTE {ψ = ψ} Γ,p∶φ⊢δ∶ψ Γ⊢ε∶φ δ[p∶=ε]∈CΓψ = WTEaux ψ Γ,p∶φ⊢δ∶ψ Γ⊢ε∶φ δ[p∶=ε]∈CΓψ (SNap' {substitution} β-respects-sub (CsubSN ψ δ[p∶=ε]∈CΓψ))
\end{code}

\begin{prop}
If $\Gamma \vdash \delta : \phi$ and $\sigma : \Gamma \rightarrow \Delta$ then $\delta [ \sigma ] \in C_\Delta(\phi)$.
\end{prop}

\begin{code}
SNmainlemma : ∀ {P} {Q} {Γ : Context P} {δ} {φ} {σ : Sub P Q} {Δ} →
  Γ ⊢ δ ∶ φ →
  (∀ x → C Δ (close (typeof {K = -proof} x Γ)) (σ _ x)) →
  C Δ (close φ) (δ ⟦ σ ⟧)
SNmainlemma (var {p = p}) hyp = hyp p
SNmainlemma {P} {Q} {Γ} {σ = σ} {Δ} (app {δ = δ} {ε} {φ} {ψ} Γ⊢δ∶φ⇛ψ Γ⊢ε∶φ) hyp = 
  subst (C Δ (close ψ)) (cong (λ M → appP M (ε ⟦ σ ⟧)) rep-idOp) 
    (proj₂ (SNmainlemma Γ⊢δ∶φ⇛ψ hyp) Q (idOpRep Q) (ε ⟦ σ ⟧) idRep-typed 
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
  (Λ {Γ = Δ} {φ = φ ⟦ σ ⟧} {δ = δ ⟦ Sub↑ -proof σ ⟧} {ψ = ψ ⟦ σ ⟧} 
    (subst (λ A → (Δ ,P (φ ⟦ σ ⟧)) ⊢ δ ⟦ Sub↑ -proof σ ⟧ ∶ A) 
    (let open ≡-Reasoning in 
    begin
      ψ 〈 upRep 〉 ⟦ Sub↑ -proof σ ⟧
    ≡⟨⟨ sub-comp₂ ψ ⟩⟩
      ψ ⟦ Sub↑ -proof σ •₂ upRep ⟧
    ≡⟨⟩
      ψ ⟦ upRep •₁ σ ⟧
    ≡⟨ sub-comp₁ ψ ⟩
      ψ ⟦ σ ⟧ 〈 upRep 〉
    ∎)
  (Substitution Γ,φ⊢δ∶ψ (Sub↑-typed (λ x → 
    subst (λ A → Δ ⊢ σ _ x ∶ A) (sym (close-magic' {φ = typeof x Γ})) (C-typed {Γ = Δ} {φ = close (typeof x Γ)} (hyp x)))))))
  , (λ R {Θ} ρ ε ρ∶Δ→Θ ε∈CΘφ → WTE {ψ = close ψ} 
       (change-type 
         (let open ≡-Reasoning in 
         begin
           ψ 〈 upRep 〉 ⟦ Sub↑ -proof σ ⟧ 〈 Rep↑ -proof ρ 〉
         ≡⟨⟨ close-magic ⟩⟩
           close (ψ 〈 upRep 〉 ⟦ Sub↑ -proof σ ⟧ 〈 Rep↑ -proof ρ 〉) 〈 magic 〉
         ≡⟨ cong (λ E → E 〈 magic 〉) (trans (trans (close-rep (ψ 〈 upRep 〉 ⟦ Sub↑ -proof σ ⟧)) (close-sub (ψ 〈 upRep 〉))) (close-rep ψ)) ⟩
           close ψ 〈 magic 〉
         ∎) --REFACTOR
         (Weakening (Substitution Γ,φ⊢δ∶ψ (Sub↑-typed σ∶Γ⇒Δ)) (Rep↑-typed ρ∶Δ→Θ))) 
       (change-type 
         (let open ≡-Reasoning in 
         begin
           close φ 〈 magic 〉
         ≡⟨⟨ cong (λ E → E 〈 magic 〉) (close-sub φ) ⟩⟩ -- TODO Lemma for cong-sub
           close (φ ⟦ ρ •₁ σ ⟧) 〈 magic 〉
         ≡⟨ close-magic {φ = φ ⟦ ρ •₁ σ ⟧} ⟩ -- TODO Make argument explicit in close-magic'
           φ ⟦ ρ •₁ σ ⟧
         ≡⟨ sub-comp₁ φ ⟩
           φ ⟦ σ ⟧ 〈 ρ 〉
         ∎) 
         (C-typed {φ = close φ} ε∈CΘφ)) --TODO Make argument explicit in C-typed?
       (subst₂ (C Θ)
         (close-rep ψ)
         (let open ≡-Reasoning in 
         begin
           δ ⟦ x₀:= ε •₂ Rep↑ -proof ρ • Sub↑ -proof σ ⟧
         ≡⟨ sub-comp δ ⟩
           δ ⟦ Sub↑ -proof σ ⟧ ⟦ x₀:= ε •₂ Rep↑ -proof ρ ⟧
         ≡⟨ sub-comp₂ (δ ⟦ Sub↑ -proof σ ⟧) ⟩
           δ ⟦ Sub↑ -proof σ ⟧ 〈 Rep↑ -proof ρ 〉 ⟦ x₀:= ε ⟧
         ∎)
         (SNmainlemma {σ = x₀:= ε •₂ Rep↑ -proof ρ • Sub↑ -proof σ} Γ,φ⊢δ∶ψ (λ x → aux x ε∈CΘφ))) 
       (CsubSN (close φ) ε∈CΘφ)) where
    aux : ∀ {R} {Θ : Context R} {ρ} {ε} x → 
      C Θ (close φ) ε →
      C Θ (close (typeof {K = -proof} x (Γ ,P φ))) ((x₀:= ε •₂ Rep↑ -proof ρ • Sub↑ -proof σ) -proof x)
    aux {Θ = Θ} {ε = ε} x₀ ε∈CΘφ = subst (λ P₁ → C Θ P₁ ε) 
      (let open ≡-Reasoning in
      begin
        close φ
      ≡⟨⟨ close-rep φ ⟩⟩
        close (φ 〈 upRep 〉)
      ∎) ε∈CΘφ
    aux {Θ = Θ} {ρ} {ε} (↑ x) _ = subst₂ (C Θ) 
      (let open ≡-Reasoning in
      begin
        {!!}
      ≡⟨ {!!} ⟩
        {!!}
      ∎) 
      (let open ≡-Reasoning in
      begin
        σ -proof x 〈 ρ 〉
      ≡⟨ {!!} ⟩
        σ -proof x 〈 upRep 〉 〈 Rep↑ -proof ρ 〉 ⟦ x₀:= ε ⟧
      ∎) 
      {!!}
\end{code}