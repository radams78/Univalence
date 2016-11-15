\AgdaHide{
\begin{code}
module PHOPL.SubC where
open import Data.Nat
open import Data.Empty renaming (⊥ to Empty)
open import Data.Fin
open import Data.List hiding (replicate)
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Red
open import PHOPL.Rules
open import PHOPL.Meta
open import PHOPL.Computable
open import PHOPL.PathSub
open import PHOPL.KeyRedex
\end{code}
}

Let us say that a substitution $\sigma : \Gamma \Rightarrow \Delta$ is \emph{computable}
iff, for all $z : T \in \Gamma$, we have $\sigma(z) \in E\Delta(T[\sigma])$.

\begin{code}
_∶_⇒C_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set
_∶_⇒C_ {U} {V} σ Γ Δ = ∀ {K} (x : Var U K) → E {V} Δ ((typeof x Γ) ⟦ σ ⟧) (σ _ x)
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
⊥MM-not-func : ∀ {V Γ} (MM : snocList (Term V)) {A B} →
  Γ ⊢ APPl ⊥ MM ∶ ty (A ⇛ B) → Empty
⊥MM-not-func [] ()
⊥MM-not-func (MM snoc _) (appR Γ⊢⊥MM∶A⇛B⇛C _) = ⊥MM-not-func MM Γ⊢⊥MM∶A⇛B⇛C

⊃MM-not-func : ∀ {V Γ φ ψ} (MM : snocList (Term V)) {A B} →
  Γ ⊢ APPl (φ ⊃ ψ) MM ∶ ty (A ⇛ B) → Empty
⊃MM-not-func [] ()
⊃MM-not-func (MM snoc _) (appR Γ⊢⊥MM∶A⇛B⇛C _) = ⊃MM-not-func MM Γ⊢⊥MM∶A⇛B⇛C

postulate nf-is-Meaning : ∀ {V} {M : Term V} {Γ} → Γ ⊢ M ∶ ty Ω → nf M → Σ[ S ∈ MeaningShape ] Σ[ φ ∈ Meaning V S ] M ≡ decode-Meaning φ

Ectxt : ∀ {V} → Context V → Set
Ectxt {V} Γ = (∀ (p : Var V -Proof) → E Γ (ty Ω) (typeof p Γ)) × 
              (∀ (e : Var V -Path) → E-eq Γ (typeof e Γ))

idSubC : ∀ {V} {Γ : Context V} → valid Γ → Ectxt Γ → idSub V ∶ Γ ⇒C Γ
\end{code}

\AgdaHide{
\begin{code}
idSubC {Γ = Γ} validΓ EctxtΓ {K = -Proof} p = subst (λ a → E Γ a (var p)) (Prelims.sym sub-idSub) (E-varP validΓ (proj₁ EctxtΓ p))
idSubC {Γ = Γ} validΓ EctxtΓ {K = -Term} x = subst (λ a → E Γ a (var x)) (Prelims.sym sub-idSub) (E-varT validΓ)
idSubC {Γ = Γ} validΓ EctxtΓ {K = -Path} e = subst (λ a → E Γ a (var e)) (Prelims.sym sub-idSub) (E-varE validΓ (proj₂ EctxtΓ e))
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
postulate •RSC : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                 ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒C Δ → ρ •RS σ ∶ Γ ⇒C Θ

postulate •SRC : ∀ {U} {V} {W} {σ : Sub V W} {ρ : Rep U V} {Γ} {Δ} {Θ} →
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
                    E Γ A M → x₀:= M ∶ (Γ , A) ⇒C Γ
\end{code}

\AgdaHide{
\begin{code}
postulate botsub₃C : ∀ {V} {Γ : Context V} {A} {M} {N} {P} →
                   E Γ (ty A) M → E Γ (ty A) N → E Γ (M ≡〈 A 〉 N) P →
                   (x₂:= M ,x₁:= N ,x₀:= P) ∶ Γ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀ ⇒C Γ
\end{code}
}
\item
If $\sigma : \Gamma \Rightarrow_C \Delta$ and $M \in E_\Delta(A)$ then $(\sigma , x := M) : (\Gamma , x : A) \Rightarrow_C \Delta$.

\begin{code}
postulate extendSubC : ∀ {U} {V} {σ : Sub U V} {K} {M} {Γ} {Δ} {A} →
                          σ ∶ Γ ⇒C Δ → E Δ (A ⟦ σ ⟧) M → extendSub σ M ∶ _,_ {K = K} Γ A ⇒C Δ
\end{code}
\end{enumerate}
\end{lemma}

Let us say that a path substitution $\tau : \rho \sim \sigma : \Gamma \Rightarrow \Delta$ is
\emph{computable} iff, for all $x : A \in \Gamma$, we have $\tau(x) \in E_\Delta(\rho(x) =_A \sigma(x))$.

\begin{code}
_∶_∼_∶_⇒C_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ = ∀ x → E Δ (ρ _ x ≡〈 typeof' x Γ 〉 σ _ x) (τ x)
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
                         τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ → E Δ (N ≡〈 A 〉 N') Q → extendPS τ Q ∶ extendSub ρ N ∼ extendSub σ N' ∶ Γ ,T A ⇒C Δ
\end{code}

\AgdaHide{
\begin{code}
postulate •RPC : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} {σ} {σ'} {Γ} {Δ} {Θ} →
                         τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → ρ ∶ Δ ⇒R Θ → ρ •RP τ ∶ ρ •RS σ ∼ ρ •RS σ' ∶ Γ ⇒C Θ

\end{code}
}
\end{lemma}
