\AgdaHide{
\begin{code}
module PHOPL.SubC where
open import Data.Nat
open import Data.Fin
open import Data.List hiding (replicate)
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
postulate subC-typed : ∀ {U} {V} {σ : Sub U V} {Γ : Context U} {Δ : Context V} →
                     σ ∶ Γ ⇒C Δ → σ ∶ Γ ⇒ Δ

postulate subC-cong : ∀ {U} {V} {σ τ : Sub U V} {Γ} {Δ} →
                    σ ∶ Γ ⇒C Δ → σ ∼ τ → τ ∶ Γ ⇒C Δ

postulate change-codC : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} →
                     σ ∶ Γ ⇒C Δ → Δ ≡ Δ' → σ ∶ Γ ⇒C Δ'
\end{code}
}

\begin{lemma}
\begin{enumerate}
\item
The identity substitution is computable.

\begin{code}
idSubC : ∀ {V} {Γ : Context V} → idSub V ∶ Γ ⇒C Γ
\end{code}

\AgdaHide{
\begin{code}
idSubC {V} {Γ} x = subst (λ a → E' Γ a (var x)) (sym sub-idSub) var-E'
\end{code}
}

\item
The computable substitutions are closed under composition.

\begin{code}
postulate compC : ∀ {U} {V} {W} {ρ : Sub V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                ρ ∶ Δ ⇒C Θ → σ ∶ Γ ⇒C Δ → ρ • σ ∶ Γ ⇒C Θ
\end{code}

\AgdaHide{
\begin{code}
postulate compRSC : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                 ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒C Δ → ρ •RS σ ∶ Γ ⇒C Θ

postulate compSRC : ∀ {U} {V} {W} {σ : Sub V W} {ρ : Rep U V} {Γ} {Δ} {Θ} →
                 σ ∶ Δ ⇒C Θ → ρ ∶ Γ ⇒R Δ → σ •SR ρ ∶ Γ ⇒C Θ
\end{code}
}

\item
If $\sigma$ is computable, then so is $(\sigma , K)$.

\begin{code}
postulate liftSubC : ∀ {U} {V} {σ : Sub U V} {K} {Γ} {Δ} {A} →
                    σ ∶ Γ ⇒C Δ → liftSub K σ ∶ (Γ , A) ⇒C (Δ , A ⟦ σ ⟧)
\end{code}

\item
If $M \in E_\Gamma(A)$ then $(x := M) : (Γ , x : A) \rightarrow_C \Gamma$.

\begin{code}
postulate botsubC : ∀ {V K} {Γ : Context V} {A : Expression V (parent K)} {M : Expression V (varKind K)} →
                    E' Γ A M → x₀:= M ∶ (Γ , A) ⇒C Γ
\end{code}

\AgdaHide{
\begin{code}
postulate botsub₃C : ∀ {V} {Γ : Context V} {A} {M} {N} {P} →
                   E Γ A M → E Γ A N → EE Γ (M ≡〈 A 〉 N) P →
                   (x₂:= M ,x₁:= N ,x₀:= P) ∶ Γ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀ ⇒C Γ
\end{code}
}
\item
If $\sigma : \Gamma \Rightarrow_C \Delta$ and $M \in E_\Delta(A)$ then $(\sigma , x := M) : (\Gamma , x : A) \Rightarrow_C \Delta$.

\begin{code}
postulate extendSubC : ∀ {U} {V} {σ : Sub U V} {M : Term V} {Γ} {Δ} {A} →
                          σ ∶ Γ ⇒C Δ → E Δ A M → extendSub σ M ∶ Γ ,T A ⇒C Δ
\end{code}
\end{enumerate}
\end{lemma}

Let us say that a path substitution $\tau : \rho \sim \sigma : \Gamma \Rightarrow \Delta$ is
\emph{computable} iff, for all $x : A \in \Gamma$, we have $\tau(x) \in E_\Delta(\rho(x) =_A \sigma(x))$.

\begin{code}
_∶_∼_∶_⇒C_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ = ∀ x → EE Δ (ρ _ x ≡〈 typeof' x Γ 〉 σ _ x) (τ x)
\end{code}

\AgdaHide{
\begin{code}
postulate pathsubC-typed : ∀ {U} {V} {τ : PathSub U V} ρ σ {Γ} {Δ} → 
                     τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ

postulate pathsubC-valid₁ : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} →
                          τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → ρ ∶ Γ ⇒C Δ

postulate pathsubC-valid₂ : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} →
                          τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → σ ∶ Γ ⇒C Δ

postulate change-ends : ∀ {U} {V} {τ : PathSub U V} {ρ} {ρ'} {σ} {σ'} {Γ} {Δ} → 
                      τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → ρ ∼ ρ' → σ ∼ σ' → τ ∶ ρ' ∼ σ' ∶ Γ ⇒C Δ
\end{code}
}

\begin{lemma}
\item
If $\tau : \rho \sim \sigma : \Gamma \Rightarrow \Delta$ and $Q \in E_\Delta(N =_A N')$ then $(\tau, x := Q) : (\rho , x := N) \sim (\sigma , x := N') : (\Gamma , x : A) \Rightarrow \Delta$.

\begin{code}
postulate extendPSC : ∀ {U} {V} {τ : PathSub U V} {ρ σ : Sub U V} {Γ : Context U} {Δ : Context V} {A : Type} {Q : Path V} {N N' : Term V} →
                         τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → EE Δ (N ≡〈 A 〉 N') Q → extendPS τ Q ∶ extendSub ρ N ∼ extendSub σ N' ∶ Γ ,T A ⇒C Δ
\end{code}

\AgdaHide{
\begin{code}
postulate compRPC : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} {σ} {σ'} {Γ} {Δ} {Θ} →
                         τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → ρ ∶ Δ ⇒R Θ → ρ •RP τ ∶ ρ •RS σ ∼ ρ •RS σ' ∶ Γ ⇒C Θ

Emult-lookup : ∀ {V n} {Γ : Context V} {MM NN : snocVec (Term V) n} {AA PP i} →
  Emult Γ (eqmult MM AA NN) (toSnocListExp PP) → E' Γ (lookup i MM ≡〈 lookup i AA 〉 lookup i NN) (lookup i PP)
Emult-lookup {n = suc n} {Γ} {_ snoc _} {_ snoc _} {_ snoc A} {_ snoc P} {zero} (_ snoc P∈EΓM≡N) = 
  subst₂ (λ a b → E' Γ (a ≡〈 A 〉 b) P) (botSub-ups (replicate n -Path)) (botSub-ups (replicate n -Path)) P∈EΓM≡N
Emult-lookup {MM = _ snoc _} {_ snoc _} {_ snoc _} {_ snoc _} {suc i} (PP∈EΓMM≡NN snoc _) = Emult-lookup {i = i} PP∈EΓMM≡NN

private pre-wteE : ∀ {n} {V} {Γ : Context V} {A P M} {BB : snocVec Type n} {C M' L L' Q NN NN' RR} →
                 addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 Pi BB C 〉 appT (M' ⇑ ⇑ ⇑) (var x₁) →
                 E Γ A L → E Γ A L' → E' Γ (L ≡〈 A 〉 L') Q →
                 Emult Γ (toSnocTypes BB) (toSnocListExp NN) → Emult Γ (toSnocTypes BB) (toSnocListExp NN') → Emult Γ (eqmult NN BB NN') (toSnocListExp RR) →
                 E' Γ (APP (appT M L) NN ≡〈 C 〉 APP (appT M' L') NN') (APP* NN NN' (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) RR) →
                 E' Γ (APP (appT M L) NN ≡〈 C 〉 APP (appT M' L') NN') (APP* NN NN' (app* L L' (λλλ A P) Q) RR)
pre-wteE ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' Ni∈EΓBi N'i∈EΓBi Ri∈EΓNi≡N'i PLL'QRR∈EΓMLNN≡M'L'NN' = E'I (APP*-typed (app*R (E'-typed L∈EΓA) (E'-typed L'∈EΓA) 
  (lllR ΓAAE⊢P∶Mx≡Ny) (E'-typed Q∈EΓL≡L')) 
  (λ i → E'-typed (Emult-lookup {i = i} Ri∈EΓNi≡N'i))) (pre-wte-compute ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' Ni∈EΓBi N'i∈EΓBi Ri∈EΓNi≡N'i PLL'QRR∈EΓMLNN≡M'L'NN')

wteE : ∀ {V} {Γ : Context V} {A P M B N L L' Q} →
  addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT (N ⇑ ⇑ ⇑) (var x₁) → 
  E Γ A L → E Γ A L' → E' Γ (L ≡〈 A 〉 L') Q →
  E' Γ (appT M L ≡〈 B 〉 appT N L') (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) →
  E' Γ (appT M L ≡〈 B 〉 appT N L') (app* L L' (λλλ A P) Q)
wteE {V} {Γ} {A} {P} {M} {B} {N} {L} {L'} {Q} ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' PLL'P∈EΓML≡NL' = 
  pre-wteE {BB = []} {NN = []} {[]} {[]} ΓAAE⊢P∶Mx≡Ny L∈EΓA L'∈EΓA Q∈EΓL≡L' [] [] [] PLL'P∈EΓML≡NL'

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

