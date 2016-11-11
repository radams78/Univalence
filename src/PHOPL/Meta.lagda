\AgdaHide{
\begin{code}
module PHOPL.Meta where
open import Data.Fin
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Red
open import PHOPL.Rules
open import PHOPL.PathSub

valid-addpath : ∀ {V} {Γ : Context V} {A} → valid Γ → valid (addpath Γ A)
valid-addpath validΓ = ctxER (varR x₁ (ctxTR (ctxTR validΓ))) (varR x₀ (ctxTR (ctxTR validΓ)))

context-validity' : ∀ {V} {Γ : Context V} {A} → valid (addpath Γ A) → valid Γ
context-validity' (ctxER (varR _ (ctxTR (ctxTR validΓ))) _) = validΓ

postulate change-type : ∀ {V} {Γ} {K} {M : Expression V (varKind K)} {A} {B} →
                      Γ ⊢ M ∶ A → A ≡ B → Γ ⊢ M ∶ B

postulate liftsRep-typed : ∀ {U} {V} {ρ : Rep U V} {Γ} {Δ} {A} →
                           ρ ∶ Γ ⇒R Δ → liftsRep pathDom ρ ∶ addpath Γ A ⇒R addpath Δ A
\end{code}
}

\subsection{Metatheorems}

\label{section:meta}

In the lemmas that follow, the letter $\mathcal{J}$ stands for any of the expressions that may occur to the right of the turnstile in a judgement, i.e.~$\mathrm{valid}$, $M : A$, $\delta : \phi$, or $P : M =_A N$.

\begin{lemma}[Context Validity]
$ $
Every derivation of $\Gamma, \Delta \vdash \mathcal{J}$ has a subderivation of $\Gamma \vald$.

\begin{code}
context-validity : ∀ {V} {Γ} {K} {M : Expression V (varKind K)} {A} →
                   Γ ⊢ M ∶ A → valid Γ
\end{code}
\end{lemma}

\begin{proof}
Induction on derivations.

\AgdaHide{
\begin{code}
context-validity (varR _ validΓ) = validΓ
context-validity (appR Γ⊢M∶A⇛B _) = context-validity Γ⊢M∶A⇛B
context-validity (ΛR Γ,A⊢M∶B) with context-validity Γ,A⊢M∶B
context-validity (ΛR _) | ctxTR validΓ = validΓ
context-validity (⊥R validΓ) = validΓ
context-validity (⊃R Γ⊢φ∶Ω _) = context-validity Γ⊢φ∶Ω
context-validity (appPR Γ⊢δ∶φ⊃ψ _) = context-validity Γ⊢δ∶φ⊃ψ
context-validity (ΛPR Γ⊢φ∶Ω _ _) = context-validity Γ⊢φ∶Ω
context-validity (convR Γ⊢M∶A _ _) = context-validity Γ⊢M∶A
context-validity (refR Γ⊢M∶A) = context-validity Γ⊢M∶A
context-validity (⊃*R Γ⊢φ∶Ω _) = context-validity Γ⊢φ∶Ω
context-validity (univR Γ⊢δ∶φ⊃ψ _) = context-validity Γ⊢δ∶φ⊃ψ
context-validity (plusR Γ⊢P∶φ≡ψ) = context-validity Γ⊢P∶φ≡ψ
context-validity (minusR Γ⊢P∶φ≡ψ) = context-validity Γ⊢P∶φ≡ψ
context-validity (lllR addpathΓ⊢P∶M≡N) = context-validity' (context-validity addpathΓ⊢P∶M≡N)
context-validity (app*R Γ⊢N∶A _ _ _) = context-validity Γ⊢N∶A
context-validity (convER Γ⊢P∶M≡N _ _ _ _) = context-validity Γ⊢P∶M≡N
\end{code}
}
\end{proof}

\begin{lemma}[Weakening]
If $\Gamma \vdash \mathcal{J}$, $\Gamma \subseteq \Delta$ and $\Delta \vald$ then $\Delta \vdash \mathcal{J}$.

\begin{code}
weakening : ∀ {U} {V} {ρ : Rep U V} {K}
           {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
           Γ ⊢ M ∶ A → valid Δ → ρ ∶ Γ ⇒R Δ → Δ ⊢ M 〈 ρ 〉 ∶ A 〈 ρ 〉
weakening {ρ = ρ} (varR x _) validΔ ρ∶Γ⇒RΔ = change-type (varR (ρ _ x) validΔ) (ρ∶Γ⇒RΔ x)
weakening (appR Γ⊢M∶A⇛B Γ⊢N∶A) validΔ ρ∶Γ⇒RΔ = appR (weakening Γ⊢M∶A⇛B validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢N∶A validΔ ρ∶Γ⇒RΔ)
weakening (ΛR Γ,A⊢M∶B) validΔ ρ∶Γ⇒RΔ = ΛR (weakening Γ,A⊢M∶B (ctxTR validΔ) (liftRep-typed ρ∶Γ⇒RΔ))
weakening (⊥R _) validΔ _ = ⊥R validΔ
weakening (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ ρ∶Γ⇒RΔ = ⊃R (weakening Γ⊢φ∶Ω validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢ψ∶Ω validΔ ρ∶Γ⇒RΔ)
weakening (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) validΔ ρ∶Γ⇒RΔ = appPR (weakening Γ⊢δ∶φ⊃ψ validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢ε∶φ validΔ ρ∶Γ⇒RΔ)
weakening {ρ = ρ} {Δ = Δ} (ΛPR {φ = φ} {ψ} Γ⊢φ∶Ω Γ⊢ψ∶Ω Γ,φ⊢δ∶ψ) validΔ ρ∶Γ⇒RΔ = 
  let Δ⊢φ∶Ω : Δ ⊢ φ 〈 ρ 〉 ∶ ty Ω
      Δ⊢φ∶Ω = weakening Γ⊢φ∶Ω validΔ ρ∶Γ⇒RΔ in
  ΛPR Δ⊢φ∶Ω
      (weakening Γ⊢ψ∶Ω validΔ ρ∶Γ⇒RΔ) 
      (change-type (weakening Γ,φ⊢δ∶ψ (ctxPR Δ⊢φ∶Ω) (liftRep-typed ρ∶Γ⇒RΔ)) (liftRep-upRep ψ))
weakening (convR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ) validΔ ρ∶Γ⇒RΔ = convR (weakening Γ⊢δ∶φ validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢ψ∶Ω validΔ ρ∶Γ⇒RΔ) (conv-rep φ≃ψ)
weakening (refR Γ⊢M∶A) validΔ ρ∶Γ⇒RΔ = refR (weakening Γ⊢M∶A validΔ ρ∶Γ⇒RΔ)
weakening (⊃*R Γ⊢P∶φ≡φ' Γ⊢Q∶ψ≡ψ') validΔ ρ∶Γ⇒RΔ = ⊃*R (weakening Γ⊢P∶φ≡φ' validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢Q∶ψ≡ψ' validΔ ρ∶Γ⇒RΔ)
weakening (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) validΔ ρ∶Γ⇒RΔ = univR (weakening Γ⊢δ∶φ⊃ψ validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢ε∶ψ⊃φ validΔ ρ∶Γ⇒RΔ)
weakening (plusR Γ⊢P∶φ≡ψ) validΔ ρ∶Γ⇒RΔ = plusR (weakening Γ⊢P∶φ≡ψ validΔ ρ∶Γ⇒RΔ)
weakening (minusR Γ⊢P∶φ≡ψ) validΔ ρ∶Γ⇒RΔ = minusR (weakening Γ⊢P∶φ≡ψ validΔ ρ∶Γ⇒RΔ)
weakening (lllR {B = B} {M = M} {N} ΓAAE⊢P∶Mx≡Ny) validΔ ρ∶Γ⇒RΔ = lllR (change-type (weakening ΓAAE⊢P∶Mx≡Ny (valid-addpath validΔ) (liftRep-typed (liftRep-typed (liftRep-typed ρ∶Γ⇒RΔ)))) 
  (cong₂ (λ x y → appT x (var x₂) ≡〈 B 〉 appT y (var x₁)) (liftRep-upRep₃ M) (liftRep-upRep₃ N)))
weakening (app*R Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') validΔ ρ∶Γ⇒RΔ = app*R (weakening Γ⊢N∶A validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢N'∶A validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢P∶M≡M' validΔ ρ∶Γ⇒RΔ) 
  (weakening Γ⊢Q∶N≡N' validΔ ρ∶Γ⇒RΔ)
weakening (convER Γ⊢M∶N₁≡N₂ Γ⊢N₁'∶A Γ⊢N₂'∶A N₁≃N₁' N₂≃N₂') validΔ ρ∶Γ⇒RΔ =
  convER (weakening Γ⊢M∶N₁≡N₂ validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢N₁'∶A validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢N₂'∶A validΔ ρ∶Γ⇒RΔ) (conv-rep N₁≃N₁') (conv-rep N₂≃N₂')
\end{code}
\end{lemma}

\begin{proof}
Induction on derivations.
\end{proof}

\begin{lemma}[Type Validity]
$ $
\begin{enumerate}
\item
If $\Gamma \vdash \delta : \phi$ then $\Gamma \vdash \phi : \Omega$.
\item
If $\Gamma \vdash P : M =_A N$ then $\Gamma \vdash M : A$ and $\Gamma \vdash N : A$.
\end{enumerate}
\end{lemma}

\begin{proof}
Induction on derivations.  The cases where $\delta$ or $P$ is a variable use Context Validity.
\end{proof}

\AgdaHide{
\begin{code}
postulate Prop-Validity : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} → 
                        Γ ⊢ δ ∶ φ → Γ ⊢ φ ∶ ty Ω

postulate change-codR : ∀ {U} {V} {ρ : Rep U V} {Γ : Context U} {Δ Δ' : Context V} →
                      ρ ∶ Γ ⇒R Δ → Δ ≡ Δ' → ρ ∶ Γ ⇒R Δ'

postulate upRep-typed : ∀ {V} {Γ : Context V} {K} A → upRep ∶ Γ ⇒R _,_ {K = K} Γ A
\end{code}
}

\begin{lemma}[Generation]
$ $
\begin{enumerate}
\item
If $\Gamma \vdash x : A$ then $x : A \in \Gamma$.
\item
If $\Gamma \vdash \bot : A$ then $A \equiv \Omega$.
\item
If $\Gamma \vdash \phi \supset \psi : A$ then $\Gamma \vdash \phi : \Omega$, $\Gamma \vdash \psi : \Omega$ and $A \equiv \Omega$.
\item
If $\Gamma \vdash \lambda x:A.M : B$ then there exists $C$ such that $\Gamma, x : A \vdash M : C$ and $B \equiv A \rightarrow C$.
\item
If $\Gamma \vdash MN : A$ then there exists $B$ such that $\Gamma \vdash M : B \rightarrow A$ and $\Gamma \vdash N : B$.
\item
If $\Gamma \vdash p : \phi$, then there exists $\psi$ such that $p : \psi \in \Gamma$ and $\phi \simeq \psi$.
\item
If $\Gamma \vdash \lambda p:\phi.\delta : \psi$, then there exists $\chi$ such that $\Gamma, p : \phi \vdash \delta : \chi$ and $\psi \simeq \phi \supset \chi$.
\item
If $\Gamma \vdash \delta \epsilon : \phi$ then there exists $\psi$ such that $\Gamma \vdash \delta : \psi \supset \phi$ and $\Gamma \vdash \epsilon : \psi$.
\item
If $\Gamma \vdash e : M =_A N$, then there exist $M'$, $N'$ such that $e : M' =_A N' \in \Gamma$ and $M \simeq M'$, $N \simeq N'$.
\item
If $\Gamma \vdash \reff{M} : N =_A P$, then we have $\Gamma \vdash M : A$ and $M \simeq N \simeq P$.
\item
If $\Gamma \vdash P \supset^* Q : \phi =_A \psi$, then there exist $\phi_1$, $\phi_2$, $\psi_1$, $\psi_2$ such that
$\Gamma \vdash P : \phi_1 =_\Omega \psi_1$, $\Gamma \vdash Q : \phi_2 =_\Omega \psi_2$, $\phi \simeq \phi_1 \supset \psi_1$, $\psi \simeq \phi_2 \supset \psi_2$, and $A \equiv \Omega$.
\item
If $\Gamma \vdash \univ{\phi}{\psi}{P}{Q} : \chi =_A \theta$, then we have $\Gamma \vdash P : \phi \supset \psi$, $\Gamma \vdash Q : \psi \supset \phi$,
$\Gamma \vdash \chi \simeq_\Delta \phi : \Omega$, $\Gamma \vdash \theta \simeq_\Delta \psi : \Omega$ and $A \equiv \Omega$.
\item
If $\Gamma \vdash \triplelambda e : x =_A y. P : M =_B N$ then there exists $C$ such that $\Gamma, x : A, y : A, e : x =_A y \vdash P : M x =_C N y$
and $B \equiv A \rightarrow C$.
\item
If $\Gamma \vdash P_{M M'} Q : N =_A N'$, then there exist $B$, $F$ and $G$ such that $\Gamma \vdash P : F =_{B \rightarrow A} G$, $\Gamma \vdash Q : M =_B M'$, $N \simeq F M$
and $N' \simeq G M'$.
\item
If $\Gamma \vdash P^+ : \phi$, then there exist $\psi$, $\chi$ such that $\Gamma \vdash P : \psi =_\Omega \chi$ and $\phi \simeq (\psi \supset \chi)$.
\item
If $\Gamma \vdash P^- : \phi$, there exist $\psi$, $\chi$ such that $\Gamma \vdash P : \psi =_\Omega \chi$ and $\phi \simeq (\chi \supset \psi)$.
\end{enumerate}
\end{lemma}

\begin{proof}
Induction on derivations.
\end{proof}

\AgdaHide{
\begin{code}
postulate Generation-ΛP : ∀ {V} {Γ : Context V} {φ} {δ} {ε} {ψ} →
                          Γ ⊢ appP (ΛP φ δ) ε ∶ ψ →
                          Σ[ χ ∈ Term V ] 
                          (ψ ≃ φ ⊃ χ × Γ ,P φ ⊢ δ ∶ χ ⇑)

Generation-appT : ∀ {V} {Γ : Context V} {M N : Term V} {B} →
  Γ ⊢ appT M N ∶ ty B → Σ[ A ∈ Type ] Γ ⊢ M ∶ ty (A ⇛ B) × Γ ⊢ N ∶ ty A
Generation-appT (appR {V} {Γ} {M} {N} {A} {B} Γ⊢M∶A⇛B Γ⊢N∶A) = A ,p Γ⊢M∶A⇛B ,p Γ⊢N∶A
\end{code}
}

\subsubsection{Substitutions}

\begin{definition}
Let $\Gamma$ and $\Delta$ be contexts.  A \emph{substitution from $\Gamma$ to $\Delta$}\footnote{These have also been called \emph{context morphisms}, for example in Hoffman \cite{Hofmann97syntaxand}.  Note however that what we call a substitution from $\Gamma$ to $\Delta$ is what Hoffman calls a context morphism from $\Delta$ to $\Gamma$.}, $\sigma : \Gamma \Rightarrow \Delta$,
is a substitution whose domain is $\dom \Gamma$ such that:
\begin{itemize}
\item
for every term variable $x : A \in \Gamma$, we have $\Delta \vdash \sigma(x) : A$;
\item
for every proof variable $p : \phi \in \Gamma$, we have $\Delta \vdash \sigma(p) : \phi [ \sigma ]$;
\item
for every path variable $e : M =_A N \in \Gamma$, we have $\Delta \vdash \sigma(e) : M [ \sigma ] =_A N [ \sigma ]$.
\end{itemize}
\end{definition}

\begin{code}
postulate _∶_⇒_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set
\end{code}

\begin{lemma}[Well-Typed Substitution]
If $\Gamma \vdash \mathcal{J}$, $\sigma : \Gamma \Rightarrow \Delta$ and $\Delta \vald$, then $\Delta \vdash \mathcal{J} [\sigma]$.
\end{lemma}

\begin{proof}
Induction on derivations.
\end{proof}

\AgdaHide{
\begin{code}
postulate substitution : ∀ {U} {V} {σ : Sub U V} {K}
                       {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
                       Γ ⊢ M ∶ A → valid Δ → σ ∶ Γ ⇒ Δ → Δ ⊢ M ⟦ σ ⟧ ∶ A ⟦ σ ⟧

postulate •-typed : ∀ {U} {V} {W} {σ : Sub V W} {ρ : Sub U V} {Γ} {Δ} {Θ} →
                         σ ∶ Δ ⇒ Θ → ρ ∶ Γ ⇒ Δ → σ • ρ ∶ Γ ⇒ Θ

postulate •RS-typed : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                      ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒ Δ → ρ •RS σ ∶ Γ ⇒ Θ

postulate liftSub-typed : ∀ {U} {V} {K} {σ : Sub U V} {Γ} {Δ} {A} →
                     σ ∶ Γ ⇒ Δ → liftSub K σ ∶ Γ , A ⇒ Δ , A ⟦ σ ⟧

postulate botsub-typed : ∀ {V} {K} {Γ} {E : Expression V (varKind K)} {A} → Γ ⊢ E ∶ A → x₀:= E ∶ Γ , A ⇒ Γ

lemma : ∀ {U} {V} {W} {K} (M : Expression U K) Q N' N (ρ : Rep V W) (σ : Sub U V) → M ⇑ ⇑ ⇑ ⟦ x₀:= Q • liftSub -Path (x₀:= N' • liftSub -Term (x₀:= N • liftSub -Term (ρ •RS σ))) ⟧ ≡ M ⟦ σ ⟧ 〈 ρ 〉 --TODO Rename
lemma {U} {V} {W} M Q N' N ρ σ = let open ≡-Reasoning in 
          begin
            M ⇑ ⇑ ⇑ ⟦ x₀:= Q • liftSub -Path (x₀:= N' • liftSub -Term (x₀:= N • liftSub -Term (ρ •RS σ))) ⟧
          ≡⟨ sub-comp (M ⇑ ⇑ ⇑) ⟩
            M ⇑ ⇑ ⇑ ⟦ liftSub -Path (x₀:= N' • liftSub -Term (x₀:= N • liftSub -Term (ρ •RS σ))) ⟧ ⟦ x₀:= Q ⟧
          ≡⟨ sub-congl (liftSub-upRep (M ⇑ ⇑)) ⟩
            M ⇑ ⇑ ⟦ x₀:= N' • liftSub -Term (x₀:= N • liftSub -Term (ρ •RS σ)) ⟧ ⇑ ⟦ x₀:= Q ⟧
          ≡⟨ botSub-upRep _ ⟩
            M ⇑ ⇑ ⟦ x₀:= N' • liftSub -Term (x₀:= N • liftSub -Term (ρ •RS σ)) ⟧
          ≡⟨ sub-comp (M ⇑ ⇑) ⟩
            M ⇑ ⇑ ⟦ liftSub -Term (x₀:= N • liftSub -Term (ρ •RS σ)) ⟧ ⟦ x₀:= N' ⟧
          ≡⟨ sub-congl (liftSub-upRep (M ⇑)) ⟩
            M ⇑ ⟦ x₀:= N • liftSub -Term (ρ •RS σ) ⟧ ⇑ ⟦ x₀:= N' ⟧
          ≡⟨ botSub-upRep _ ⟩
            M ⇑ ⟦ x₀:= N • liftSub -Term (ρ •RS σ) ⟧
          ≡⟨ sub-comp (M ⇑) ⟩
            M ⇑ ⟦ liftSub -Term (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧
          ≡⟨ sub-congl (liftSub-upRep M) ⟩
            M ⟦ ρ •RS σ ⟧ ⇑ ⟦ x₀:= N ⟧
          ≡⟨ botSub-upRep _ ⟩
            M ⟦ ρ •RS σ ⟧
          ≡⟨ sub-compRS M ⟩
            M ⟦ σ ⟧ 〈 ρ 〉
          ∎

postulate change-cod' : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} → σ ∶ Γ ⇒ Δ → Δ ≡ Δ' → σ ∶ Γ ⇒ Δ'

extendSub : ∀ {U} {V} {K} → Sub U V → Expression V (varKind K) → Sub (U , K) V
extendSub σ M _ x₀ = M
extendSub σ M _ (↑ x) = σ _ x

postulate extendSub-typed : ∀ {U} {V} {σ : Sub U V} {M : Term V} {Γ} {Δ} {A} →
                          σ ∶ Γ ⇒ Δ → Δ ⊢ M ∶ ty A → extendSub σ M ∶ Γ ,T A ⇒ Δ
                                                                              
postulate extendSub-decomp : ∀ {U} {V} {σ : Sub U V} {K} {M : Expression V (varKind K)} {C} {L} (E : Subexp (U , K) C L) →
                           E ⟦ extendSub σ M ⟧ ≡ E ⟦ liftSub K σ ⟧ ⟦ x₀:= M ⟧

postulate extendSub-upRep : ∀ {U} {V} {σ : Sub U V} {K} {M : Expression V (varKind K)} {C L} {E : Subexp U C L} →
                          E ⇑ ⟦ extendSub σ M ⟧ ≡ E ⟦ σ ⟧

postulate ⊃-gen₁ : ∀ {V} {Γ : Context V} {φ} {ψ} → Γ ⊢ φ ⊃ ψ ∶ ty Ω → Γ ⊢ φ ∶ ty Ω

postulate ⊃-gen₂ : ∀ {V} {Γ : Context V} {φ} {ψ} → Γ ⊢ φ ⊃ ψ ∶ ty Ω → Γ ⊢ ψ ∶ ty Ω

postulate Type-Reduction : ∀ {V} {Γ : Context V} {K} {M : Expression V (varKind K)} {A} {B} →
                         Γ ⊢ M ∶ A → A ↠ B → Γ ⊢ M ∶ B

postulate change-cod : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} → σ ∶ Γ ⇒ Δ → Δ ≡ Δ' → σ ∶ Γ ⇒ Δ'
postulate sub↖-typed : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {A} → σ ∶ Γ ⇒ Δ → sub↖ σ ∶ Γ ,T A ⇒ Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀

postulate sub↗-typed : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {A} → σ ∶ Γ ⇒ Δ → sub↗ σ ∶ Γ ,T A ⇒ Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀
\end{code}
}

\begin{code}
_∶_∼_∶_⇒_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ σ ∼ σ' ∶ Γ ⇒ Δ = ∀ x → Δ ⊢ τ x ∶ σ -Term x ≡〈 typeof' x Γ 〉 σ' -Term x
\end{code}

\AgdaHide{
\begin{code}
change-cod-PS : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} {Δ'} →
                τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ → Δ ≡ Δ' → τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ'
change-cod-PS {τ = τ} {ρ} {σ} {Γ} τ∶ρ∼σ Δ≡Δ' = subst (λ x → τ ∶ ρ ∼ σ ∶ Γ ⇒ x) Δ≡Δ' τ∶ρ∼σ

postulate typeof'-up : ∀ {V} {Γ : Context V} {A} {x} → typeof' (↑ x) (Γ ,T A) ≡ typeof' x Γ

postulate rep-comp₃ : ∀ {U V₁ V₂ V₃ C K} (E : Subexp U C K) {ρ₃ : Rep V₂ V₃} {ρ₂ : Rep V₁ V₂} {ρ₁ : Rep U V₁} →
                    E 〈 ρ₃ •R ρ₂ •R ρ₁ 〉 ≡ E 〈 ρ₁ 〉 〈 ρ₂ 〉 〈 ρ₃ 〉

weakening-addpath : ∀ {V} {Γ : Context V} {K} {E : Expression V (varKind K)} {T : Expression V (parent K)} {A} → Γ ⊢ E ∶ T → addpath Γ A ⊢ E ⇑ ⇑ ⇑ ∶ T ⇑ ⇑ ⇑
weakening-addpath {Γ = Γ} {E = E} {T} {A = A} Γ⊢T∶E = subst₂ (λ t e → addpath Γ A ⊢ t ∶ e) (rep-comp₃ E) (rep-comp₃ T) (weakening Γ⊢T∶E (valid-addpath (context-validity Γ⊢T∶E)) 
  (•R-typed {Θ = addpath Γ A} (•R-typed {Θ = addpath Γ A} (upRep-typed (var x₁ ≡〈 A 〉 var x₀)) (upRep-typed (ty A))) (upRep-typed (ty A))))

liftPathSub-typed : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {A} {Δ} → 
  τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ → valid Δ → liftPathSub τ ∶ sub↖ ρ ∼ sub↗ σ ∶ Γ ,T A ⇒ Δ ,T  A ,T  A ,E var x₁ ≡〈 A 〉 var x₀
liftPathSub-typed _ validΔ x₀ = varR x₀ (valid-addpath validΔ)
liftPathSub-typed {U} {Γ = Γ} {A} {Δ = Δ} τ∶ρ∼σ validΔ (↑ x) = change-type (weakening-addpath (τ∶ρ∼σ x)) 
  (cong₃ _≡〈_〉_ refl (Prelims.sym (typeof'-up {U} {Γ = Γ} {A} {x = x})) refl)

postulate sub↖-decomp : ∀ {U} {V} {C} {K} (M : Subexp (U , -Term) C K) {ρ : Sub U V} → 
                     M ⟦ liftSub _ ρ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= var x₂ ⟧ ≡ M ⟦ sub↖ ρ ⟧

postulate sub↗-decomp : ∀ {U} {V} {C} {K} (M : Subexp (U , -Term) C K) {ρ : Sub U V} → 
                     M ⟦ liftSub _ ρ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= var x₁ ⟧ ≡ M ⟦ sub↗ ρ ⟧
\end{code}
}

\begin{definition}
If $\rho, \sigma : \Gamma \rightarrow \Delta$ and $\tau$ is a path substitution whose domain
is the term variables in $\dom \Gamma$, then we write
$\tau : \sigma \sim \rho : \Gamma \rightarrow \Delta$ iff, for each variable $x : A \in \Gamma$, we have
$\Delta \vdash \tau(x) : \sigma(x) =_A \rho(x)$.
\end{definition}

\begin{lemma}[Path Substitution]
\label{lm:pathsub}
If $\tau : \sigma \sim \rho : \Gamma \rightarrow \Delta$ and $\Gamma \vdash M : A$ and $\Delta \vald$,
then $\Delta \vdash M \{ \tau : \sigma \sim \rho \} : M [ \sigma ] =_A M [ \rho ]$.
\end{lemma}

\begin{proof}
Induction on derivations.
\end{proof}


\begin{code}
path-substitution : ∀ {U} {V} {Γ : Context U} {Δ : Context V} 
  {ρ} {σ} {τ} {M} {A} →
  (Γ ⊢ M ∶ A) → (τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ) →
  (ρ ∶ Γ ⇒ Δ) → (σ ∶ Γ ⇒ Δ) → 
  valid Δ → 
  Δ ⊢ M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ∶ M ⟦ ρ ⟧ ≡〈 yt A 〉 M ⟦ σ ⟧
\end{code}

\AgdaHide{
\begin{code}
path-substitution (varR x validΓ) τ∶ρ∼σ _ _ _ = τ∶ρ∼σ x
path-substitution (⊥R validΓ) _ _ _ validΔ = refR (⊥R validΔ)
path-substitution (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) τ∶ρ∼σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = ⊃*R (path-substitution Γ⊢φ∶Ω τ∶ρ∼σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ) (path-substitution Γ⊢ψ∶Ω τ∶ρ∼σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ)
path-substitution (appR {A = A} Γ⊢M∶A⇛B Γ⊢N∶A) τ∶σ∼σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = 
  app*R (substitution Γ⊢N∶A validΔ ρ∶Γ⇒Δ) (substitution Γ⊢N∶A validΔ σ∶Γ⇒Δ)
  (path-substitution Γ⊢M∶A⇛B τ∶σ∼σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ) (path-substitution Γ⊢N∶A τ∶σ∼σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ)
path-substitution {U} {V} {Γ} {Δ} {ρ} {σ} {τ} (ΛR .{U} .{Γ} {A} {M} {B} Γ,A⊢M∶B) τ∶σ∼σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = 
  let ΔAAE = Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀ in
  let validΔAA  : valid (Δ ,T A ,T A)
      validΔAA = ctxTR (ctxTR validΔ) in
  let validΔAAE : valid ΔAAE
      validΔAAE = ctxER (varR x₁ validΔAA) (varR x₀ validΔAA) in
  let Mσ-typed : ∀ {σ} {x} → σ ∶ Γ ⇒ Δ → typeof x ΔAAE ≡ ty A → ΔAAE ⊢ appT ((ΛT A M) ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x) ∶ ty B
      Mσ-typed = λ {σ} {x} σ∶Γ⇒Δ x∶A∈ΔAAE → appR (weakening-addpath (substitution (ΛR Γ,A⊢M∶B) validΔ σ∶Γ⇒Δ)) (change-type (varR x (valid-addpath validΔ)) x∶A∈ΔAAE) in
  let step1 : Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀ ⊢ 
              M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ∼ sub↗ σ ⟧⟧ ∶ 
              appT ((ΛT A M) ⟦ ρ ⟧ ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT ((ΛT A M) ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₁)
      step1 = convER 
               (path-substitution Γ,A⊢M∶B 
                 (liftPathSub-typed τ∶σ∼σ' validΔ) (sub↖-typed ρ∶Γ⇒Δ) (sub↗-typed σ∶Γ⇒Δ) 
                 validΔAAE)
                 (Mσ-typed ρ∶Γ⇒Δ refl)
                 (Mσ-typed σ∶Γ⇒Δ refl)
                 (RSTClose.sym (redex-conv (subst (R -appTerm ((ΛT A M ⟦ ρ ⟧) ⇑ ⇑ ⇑ ∷ var x₂ ∷ [])) (sub↖-decomp M) (βR βT)))) (RSTClose.sym (redex-conv (subst (R -appTerm ((ΛT A M ⟦ σ ⟧) ⇑ ⇑ ⇑ ∷ var x₁ ∷ [])) (sub↗-decomp M) (βR βT))))
  in lllR step1

postulate idPathSub : ∀ V → PathSub V V

infixr 75 _•RP_
_•RP_ : ∀ {U} {V} {W} → Rep V W → PathSub U V → PathSub U W
(ρ •RP τ) x = τ x 〈 ρ 〉

postulate compRP-typed : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} {σ σ' : Sub U V}
                           {Γ} {Δ} {Θ} →
                           ρ ∶ Δ ⇒R Θ → τ ∶ σ ∼ σ' ∶ Γ ⇒ Δ →
                           ρ •RP τ ∶ ρ •RS σ ∼ ρ •RS σ' ∶ Γ ⇒ Θ

postulate liftPathSub-compRP : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} →
                          liftPathSub (ρ •RP τ) ∼∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RP liftPathSub τ

extendPS : ∀ {U} {V} → PathSub U V → Path V → PathSub (U , -Term) V
extendPS τ P x₀ = P
extendPS τ P (↑ x) = τ x

postulate extendPS-typed : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} {P} {M} {N} {A} →
                           τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ → Δ ⊢ P ∶ M ≡〈 A 〉 N →
                           extendPS τ P ∶ extendSub ρ M ∼ extendSub σ N ∶ Γ ,T A ⇒ Δ

toPath : ∀ {U V} → Sub U V → PathSub U V
toPath σ x = reff (σ _ x)

postulate extendPS-decomp : ∀ {U V} {M : Term (U , -Term)} {σ : Sub U V} {P N N'} →
                          M ⟦⟦ extendPS (toPath σ) P ∶ extendSub σ N ∼ extendSub σ N' ⟧⟧ ≡ (M ⟦ liftSub _ σ ⟧) ⟦⟦ x₀::= P ∶ x₀:= N ∼ x₀:= N' ⟧⟧

postulate pathsub-extendPS : ∀ {U} {V} M {τ} {P : Path V} {N : Term V} {σ : Sub U V} {N' : Term V} {σ'} →
                           M ⟦⟦ extendPS τ P ∶ extendSub σ N ∼ extendSub σ' N' ⟧⟧
                           ≡ M ⟦⟦ liftPathSub τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= P ⟧

postulate pathsub-compRP : ∀ {U} {V} {W} M {ρ : Rep V W} {τ : PathSub U V} {σ σ' : Sub U V} →
                         M ⟦⟦ ρ •RP τ ∶ ρ •RS σ ∼ ρ •RS σ' ⟧⟧ ≡ M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧ 〈 ρ 〉

postulate sub↖-compRP : ∀ {U} {V} {W} {σ : Sub U V} {ρ : Rep V W} →
                      sub↖ (ρ •RS σ) ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↖ σ

postulate sub↗-compRP : ∀ {U} {V} {W} {σ : Sub U V} {ρ : Rep V W} →
                      sub↗ (ρ •RS σ) ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↗ σ

postulate ⋆-typed : ∀ {V} {M : Term V} {P N N' Γ A B} → 
                  Γ ⊢ M ∶ ty (A ⇛ B) → Γ ⊢ P ∶ N ≡〈 A 〉 N' → Γ ⊢ M ⋆[ P ∶ N ∼ N' ] ∶ appT M N ≡〈 B 〉 appT M N'
\end{code}
}

\begin{lemma}
\label{lm:pathsubcomp}
If $\sigma : \Gamma \rightarrow \Delta$ and $\tau : \rho \sim \rho' : \Delta \rightarrow \Theta$ then $\tau \bullet_{\rho, \rho'} \sigma : \rho \circ \sigma \sim \rho' \circ \sigma : \Gamma \rightarrow \Theta$.
\end{lemma}

\begin{proof}
Let $x : A \in \Gamma$.
We have $\Delta \vdash \sigma(x) : A$, hence $\Theta \vdash \sigma(x) \{ \tau : \rho \sim \rho' \} : \sigma(x) [ \rho ] =_A \sigma(x) [ \rho' ]$.
\end{proof}

\begin{proposition}[Subject Reduction]
If $\Gamma \vdash s : T$ and $s \twoheadrightarrow t$ then $\Gamma \vdash t : T$.
\end{proposition}

\begin{proof}
It is sufficient to prove the case $s \rightarrow t$.  The proof is by a case analysis on $s \rightarrow t$, using the Generation Lemma.
\end{proof}

\AgdaHide{
\begin{code}
postulate Subject-Reduction-R : ∀ {V} {K} {C} 
                              {c : Con (SK C (varKind K))} {E : ListAbs V C} {F : Expression V (varKind K)} {Γ} {A} →
                              Γ ⊢ app c E ∶ A → R c E F → Γ ⊢ F ∶ A

{-Subject-Reduction-R : ∀ {V} {K} {C} 
  {c : Constructor C} {E : ListAbs V C} {F : Expression V (varKind K)} {Γ} {A} →
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
postulate subject-reduction : ∀ {V} {K} {Γ}
                            {E F : Expression V (varKind K)} {A} → 
                            (Γ ⊢ E ∶ A) → (E ↠ F) → (Γ ⊢ F ∶ A)

postulate equation-validity₁ : ∀ {V} {Γ : Context V} {P : Path V} {M} {A} {N} →
                             Γ ⊢ P ∶ M ≡〈 A 〉 N → Γ ⊢ M ∶ ty A

postulate equation-validity₂ : ∀ {V} {Γ : Context V} {P : Path V} {M} {A} {N} →
                             Γ ⊢ P ∶ M ≡〈 A 〉 N → Γ ⊢ N ∶ ty A

app*R' : ∀ {V} {Γ : Context V} {P Q : Path V} {M M' N N' : Term V} {A B : Type} →
    Γ ⊢ P ∶ M ≡〈 A ⇛ B 〉 M' → Γ ⊢ Q ∶ N ≡〈 A 〉 N' →
  -------------------------------------------------
    Γ ⊢ app* N N' P Q ∶ appT M N ≡〈 B 〉 appT M' N'
app*R' Γ⊢P∶M≡M' Γ⊢Q∶N≡N' = app*R (equation-validity₁ Γ⊢Q∶N≡N') (equation-validity₂ Γ⊢Q∶N≡N') Γ⊢P∶M≡M' Γ⊢Q∶N≡N'

APP*-typed : ∀ {n} {V} {Γ : Context V} {MM NN : snocVec (Term V) n} {P QQ M N AA B} →
  Γ ⊢ P ∶ M ≡〈 Pi AA B 〉 N → (∀ i → Γ ⊢ lookup i QQ ∶ lookup i MM ≡〈 lookup i AA 〉 lookup i NN ) →
  Γ ⊢ APP* MM NN P QQ ∶ APP M MM ≡〈 B 〉 APP N NN
APP*-typed {MM = []} {[]} {QQ = []} {AA = []} Γ⊢P∶M≡N _ = Γ⊢P∶M≡N
APP*-typed {MM = MM snoc M} {NN = NN snoc N} {QQ = QQ snoc Q} {AA = AA snoc A} Γ⊢P∶M≡N Γ⊢QQ∶MM≡NN = 
  app*R' (APP*-typed Γ⊢P∶M≡N (λ i → Γ⊢QQ∶MM≡NN (suc i))) (Γ⊢QQ∶MM≡NN zero)
\end{code}

\subsubsection{Canonicity}

\begin{definition}[Canonical Object]
$ $
\begin{itemize}
\item
The canonical objects $\theta$ of $\Omega$ are given by the grammar
\[ \theta ::= \bot \mid \theta \supset \theta \]
\item
A canonical object of type $A \rightarrow B$ has the form $\lambda x:A.M$, where
$x : A \vdash M : B$ and $M$ is in normal form.
\end{itemize}
We define the \emph{canonical proofs} of a canonical object $\theta$ of $\Omega$ as follows:
\begin{itemize}
\item
There is no canonical proof of $\bot$.
\item
A canonical proof of $\phi \supset \psi$ has the form $\lambda p : \phi . \delta$, where $p : \phi \vdash \delta : \psi$ and $\delta$ is in normal form.
\end{itemize}
We define the \emph{canonical paths} of an equation $M =_A N$, where $M$ and $N$ are canonical objects of $A$, as follows:
\begin{itemize}
\item
A canonical path of $\phi =_\Omega \psi$ is either $\reff{\phi}$ if $\phi \simeq \psi$, or $\univ{\phi}{\psi}{\delta}{\epsilon}$, where $\delta$ is a canonical
proof of $\phi \supset \psi$ and $\epsilon$ is a canonical proof of $\psi \supset \phi$.
\item
A canonical path of $F =_{A \rightarrow B} G$ is either $\reff{F}$ if $F \simeq G$, or $\triplelambda e:x =_A y.P$ where $x : A, y : A, e : x =_A y \vdash P : Fx =_B Gy$ and $P$ is in normal form.
\end{itemize}
\end{definition}

\begin{proposition}[Canonicity]
If $\vdash t : T$ and $t$ is in normal form, then $t$ is a canonical object (proof, path) of $T$.
\end{proposition}

\begin{proof}
This follows easily from the Generation Lemma.
\end{proof}
