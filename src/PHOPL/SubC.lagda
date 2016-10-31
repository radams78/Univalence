\AgdaHide{
\begin{code}
module PHOPL.SubC where
open import Data.Nat
open import Data.Fin
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Red
open import PHOPL.Rules
open import PHOPL.Meta
open import PHOPL.Computable
open import PHOPL.PathSub
open import PHOPL.KeyRedex2
\end{code}
}

Let us say that a substitution $\sigma : \Gamma \Rightarrow \Delta$ is \emph{computable}
iff, for all $z : T \in \Gamma$, we have $\sigma(z) \in E\Delta(T[\sigma])$.

\begin{code}
_∶_⇒C_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set
_∶_⇒C_ {U} {V} σ Γ Δ = ∀ {K} (x : Var U K) → E' {V} Δ ((typeof x Γ) ⟦ σ ⟧) (σ _ x)
\end{code}

\AgdaHide{
\begin{code}
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

postulate liftSubC : ∀ {U} {V} {σ : Sub U V} {K} {Γ} {Δ} {A} →
                    σ ∶ Γ ⇒C Δ → liftSub K σ ∶ (Γ , A) ⇒C (Δ , A ⟦ σ ⟧)

postulate botsubC : ∀ {V} {Γ : Context V} {M} {A} →
                    E Γ A M → x₀:= M ∶ (Γ ,T A) ⇒C Γ

postulate botsubCP : ∀ {V} {Γ : Context V} {δ} {φ} →
                     EP Γ φ δ → x₀:= δ ∶ (Γ ,P φ) ⇒C Γ

postulate botsubCE : ∀ {V} {Γ : Context V} {P} {E} →
                     EE Γ E P → x₀:= P ∶ (Γ ,E E) ⇒C Γ
--TODO Common pattern

postulate botsub₃C : ∀ {V} {Γ : Context V} {A} {M} {N} {P} →
                   E Γ A M → E Γ A N → EE Γ (M ≡〈 A 〉 N) P →
                   (x₂:= M ,x₁:= N ,x₀:= P) ∶ Γ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀ ⇒C Γ

postulate subC-typed : ∀ {U} {V} {σ : Sub U V} {Γ : Context U} {Δ : Context V} →
                     σ ∶ Γ ⇒C Δ → σ ∶ Γ ⇒ Δ

postulate subC-cong : ∀ {U} {V} {σ τ : Sub U V} {Γ} {Δ} →
                    σ ∶ Γ ⇒C Δ → σ ∼ τ → τ ∶ Γ ⇒C Δ
\end{code}
}

Let us say that a path substitution $\tau : \sigma \sim \rho : \Gamma \Rightarrow \Delta$ is
\emph{computable} iff, for all $x : A \in \Gamma$, we have $\tau(x) \in E_\Delta(\sigma(x) =_A \rho(x))$.

\begin{code}
_∶_∼_∶_⇒C_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ = ∀ x → EE Δ (ρ _ x ≡〈 typeof' x Γ 〉 σ _ x) (τ x)
\end{code}

\AgdaHide{
\begin{code}
postulate change-ends : ∀ {U} {V} {τ : PathSub U V} {ρ} {ρ'} {σ} {σ'} {Γ} {Δ} → 
                      τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → ρ ∼ ρ' → σ ∼ σ' → τ ∶ ρ' ∼ σ' ∶ Γ ⇒C Δ

postulate extendPSC : ∀ {U} {V} {τ : PathSub U V} {ρ σ : Sub U V} {Γ : Context U} {Δ : Context V} {A : Type} {Q : Path V} {N N' : Term V} →
                         τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → EE Δ (N ≡〈 A 〉 N') Q → extendPS τ Q ∶ extendSub ρ N ∼ extendSub σ N' ∶ Γ ,T A ⇒C Δ

postulate compRPC : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} {σ} {σ'} {Γ} {Δ} {Θ} →
                         τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → ρ ∶ Δ ⇒R Θ → ρ •RP τ ∶ ρ •RS σ ∼ ρ •RS σ' ∶ Γ ⇒C Θ

postulate pathsubC-typed : ∀ {U} {V} {τ : PathSub U V} ρ σ {Γ} {Δ} → 
                     τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ

postulate pathsubC-valid₁ : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} →
                          τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → ρ ∶ Γ ⇒C Δ

postulate pathsubC-valid₂ : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} →
                          τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → σ ∶ Γ ⇒C Δ

postulate extendSubC : ∀ {U} {V} {σ : Sub U V} {M : Term V} {Γ} {Δ} {A} →
                          σ ∶ Γ ⇒C Δ → E Δ A M → extendSub σ M ∶ Γ ,T A ⇒C Δ

postulate wteT : ∀ {V} {Γ : Context V} {A M B N} → Γ ,T A ⊢ M ∶ ty B → E Γ A N → E Γ B (M ⟦ x₀:= N ⟧) →
                 E Γ B (appT (ΛT A M) N)

snocVec-rep : ∀ {U V C K n} → snocVec (Subexp U C K) n → Rep U V → snocVec (Subexp V C K) n
snocVec-rep [] ρ = []
snocVec-rep (EE snoc E) ρ = snocVec-rep EE ρ snoc E 〈 ρ 〉

APPP-rep : ∀ {U V n δ} (εε : snocVec (Proof U) n) {ρ : Rep U V} →
  (APPP δ εε) 〈 ρ 〉 ≡ APPP (δ 〈 ρ 〉) (snocVec-rep εε ρ)
APPP-rep [] = refl
APPP-rep (εε snoc ε) {ρ} = cong (λ x → appP x (ε 〈 ρ 〉)) (APPP-rep εε)

private pre-wte+-computeP : ∀ {m} {n} {V} {Γ : Context V} {S} {L₁ : Leaves V S}
                          {MM NN : snocVec (Term V) m} {P L L' Q RR} {εε : snocVec (Proof V) n} {A} →
                          computeP Γ L₁ (APPP (plus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR)) εε) →
                          valid Γ → SN L → SN L' → SN Q →
                          computeP Γ L₁ (APPP (plus (APP* MM NN (app* L L' (λλλ A P) Q) RR)) εε)
pre-wte+-computeP {L₁ = neutral x} {MM} {NN} {P} {L} {L'} {Q} {RR} {εε} computePRRεε validΓ SNL SNL' SNQ = 
  lmSNE MM εε (computeP-SN {L = neutral x} computePRRεε validΓ) SNL SNL' SNQ
pre-wte+-computeP {L₁ = bot} {MM} {NN} {P} {L} {L'} {Q} {RR} {εε} computePRRεε validΓ SNL SNL' SNQ = 
  lmSNE MM εε (computeP-SN {L = bot} computePRRεε validΓ) SNL SNL' SNQ
pre-wte+-computeP {m} {n} {V} {Γ} {imp S₁ S₂} {L₁ = imp L₁ L₂} {MM} {NN} {P} {L} {L'} {Q} {RR} {εε} {A} computePRRεε validΓ SNL SNL' SNQ {W} Δ {ρ = ρ} {ε = ε} ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε = 
  subst (computeP Δ (lrep L₂ ρ)) (let open ≡-Reasoning in 
  begin
    appP (APPP (plus (APP* (snocVec-rep MM ρ) (snocVec-rep NN ρ) (app* (L 〈 ρ 〉) (L' 〈 ρ 〉) (λλλ A (P 〈 liftRep _ (liftRep _ (liftRep _ ρ)) 〉)) (Q 〈 ρ 〉)) (snocVec-rep RR ρ))) (snocVec-rep εε ρ)) ε
  ≡⟨ {!!} ⟩
    appP (APPP (plus ((APP* MM NN (app* L L' (λλλ A P) Q) RR) 〈 ρ 〉)) (snocVec-rep εε ρ)) ε
  ≡⟨⟨ cong (λ x → appP x ε) (APPP-rep εε) ⟩⟩
    appP (APPP (plus (APP* MM NN (app* L L' (λλλ A P) Q) RR)) εε 〈 ρ 〉) ε
  ∎)
  (pre-wte+-computeP {m} {suc n} {W} {Δ} {S₂} {lrep L₂ ρ} {snocVec-rep MM ρ} {snocVec-rep NN ρ} {P 〈 liftRep _ (liftRep _ (liftRep _ ρ)) 〉} {L 〈 ρ 〉} {L' 〈 ρ 〉} {Q 〈 ρ 〉} {snocVec-rep RR ρ} {εε = snocVec-rep εε ρ snoc ε} {A}
  {!!}
  (context-validity Δ⊢ε∶φ) 
  {!!} 
  {!!} 
  {!!})

private pre-wte-compute : ∀ {n} {V} {Γ : Context V} {A P M} {BB : snocVec Type n} {C M' L L' Q NN NN' RR} →
                 addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 Pi BB C 〉 appT (M' ⇑ ⇑ ⇑) (var x₁) →
                 E Γ A L → E Γ A L' → E' Γ (L ≡〈 A 〉 L') Q →
                 (∀ i → E Γ (lookup i BB) (lookup i NN)) → (∀ i → E Γ (lookup i BB) (lookup i NN')) → (∀ i → E' Γ (lookup i NN ≡〈 lookup i BB 〉 lookup i NN') (lookup i RR)) →
                 E' Γ (APP (appT M L) NN ≡〈 C 〉 APP (appT M' L') NN') (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) →
                 computeE Γ (APP (appT M L) NN) C (APP (appT M' L') NN') (APP* NN NN' (app* L L' (λλλ A P) Q) RR)
pre-wte-compute {C = Ω} ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' Ni∈EΓBi N'i∈EΓBi Ri∈EΓNi≡N'i (E'I Γ⊢PLL'Q∶MNN≡M'NN' (S₁ ,p S₂ ,p L₁ ,p L₂ ,p MLNN↠L₁ ,p M'L'NN'↠L₂ ,p computeP+ ,p computeP- )) =
  S₁ ,p S₂ ,p L₁ ,p L₂ ,p MLNN↠L₁ ,p M'L'NN'↠L₂ ,p 
  (λ Δ ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε → {!!}) ,p 
  (λ Δ ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε → {!!})
pre-wte-compute {C = C ⇛ C₁} ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' Ni∈EΓBi N'i∈EΓBi Ri∈EΓNi≡N'i PLL'QRR∈EΓMLNN≡M'L'NN' Δ ρ∶Γ⇒RΔ Δ⊢Q∶N≡N' computeQ = {!!}

private pre-wteE : ∀ {n} {V} {Γ : Context V} {A P M} {BB : snocVec Type n} {C M' L L' Q NN NN' RR} →
                 addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 Pi BB C 〉 appT (M' ⇑ ⇑ ⇑) (var x₁) →
                 E Γ A L → E Γ A L' → E' Γ (L ≡〈 A 〉 L') Q →
                 (∀ i → E Γ (lookup i BB) (lookup i NN)) → (∀ i → E Γ (lookup i BB) (lookup i NN')) → (∀ i → E' Γ (lookup i NN ≡〈 lookup i BB 〉 lookup i NN') (lookup i RR)) →
                 E' Γ (APP (appT M L) NN ≡〈 C 〉 APP (appT M' L') NN') (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) →
                 E' Γ (APP (appT M L) NN ≡〈 C 〉 APP (appT M' L') NN') (APP* NN NN' (app* L L' (λλλ A P) Q) RR)
pre-wteE ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' Ni∈EΓBi N'i∈EΓBi Ri∈EΓNi≡N'i PLL'QRR∈EΓMLNN≡M'L'NN' = E'I (APP*-typed (app*R (E'.typed L∈EΓA) (E'.typed L'∈EΓA) 
  (lllR ΓAAE⊢P∶Mx≡Ny) (E'.typed Q∈EΓL≡L')) 
  (λ i → E'.typed (Ri∈EΓNi≡N'i i))) {!!}

wteE : ∀ {V} {Γ : Context V} {A P M B N L L' Q} →
  addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT (N ⇑ ⇑ ⇑) (var x₁) → 
  E Γ A L → E Γ A L' → E' Γ (L ≡〈 A 〉 L') Q →
  E' Γ (appT M L ≡〈 B 〉 appT N L') (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) →
  E' Γ (appT M L ≡〈 B 〉 appT N L') (app* L L' (λλλ A P) Q)
wteE {V} {Γ} {A} {P} {M} {B} {N} {L} {L'} {Q} ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' P⟦LL'P⟧∈EΓML≡NL' = 
  {!!}

--TODO Duplications with PL
postulate extend-subC : ∀ {U} {V} {σ : Sub U V} {Γ : Context U} {Δ : Context V} {K} {M : Expression V (varKind K)} {A : Expression U (parent K)} →
                      σ ∶ Γ ⇒C Δ → E' Δ (A ⟦ σ ⟧) M → 
                      x₀:= M • liftSub K σ ∶ Γ , A ⇒C Δ

subCRS : ∀ {U V W} {ρ : Rep V W} {σ : Sub U V} {Γ Δ Θ} →
         ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒C Δ → valid Θ → ρ •RS σ ∶ Γ ⇒C Θ
subCRS {ρ = ρ} {σ = σ} {Γ} {Θ = Θ} ρ∶Δ⇒RΘ σ∶Γ⇒CΔ validΘ x = 
  subst (λ a → E' Θ a ((σ _ x) 〈 ρ 〉)) {typeof x Γ ⟦ σ ⟧ 〈 ρ 〉} {typeof x Γ ⟦ ρ •RS σ ⟧} 
    (sym (sub-compRS (typeof x Γ))) (E'-rep (σ∶Γ⇒CΔ x) ρ∶Δ⇒RΘ validΘ)
\end{code}
}

