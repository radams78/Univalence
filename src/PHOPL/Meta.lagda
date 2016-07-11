\AgdaHide{
\begin{code}
module PHOPL.Meta where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Red
open import PHOPL.Rules
open import PHOPL.PathSub

valid-addpath : ∀ {V} {Γ : Context V} {A} → valid Γ → valid (addpath Γ A)
valid-addpath validΓ = ctxER (varR x₁ (ctxTR (ctxTR validΓ))) (varR x₀ (ctxTR (ctxTR validΓ)))
\end{code}
}

\subsection{Metatheorems}

\begin{lemma}[Context Validity]
$ $
\begin{enumerate}
\item
Every derivation of $\Gamma, \Delta \vdash \mathcal{J}$ has a subderivation of $\Gamma \vald$.
\item
Every derivation of $\Gamma, p : \phi, \Delta \vdash \mathcal{J}$ has a subderivation of $\Gamma \vdash \phi : \Omega$.
\item
Every derivation of $\Gamma, e : M =_A N, \Delta \vdash \mathcal{J}$ has subderivations of $\Gamma \vdash M : A$ and $\Gamma \vdash N : A$.
\end{enumerate}
\end{lemma}

\begin{proof}
Part 1 is proven by induction on derivations.  Parts 2 and 3 follow by inversion.
\end{proof}

\AgdaHide{
\begin{code}
context-validity : ∀ {V} {Γ} {K} {M : Expression V (varKind K)} {A} →
                   Γ ⊢ M ∶ A → valid Γ
context-validity'' : ∀ {V} {Γ : Context V} {A} → valid (addpath Γ A) → valid Γ
--BUG "with" does not work on lines 8 and 15 below

context-validity (varR _ validΓ) = validΓ
context-validity (appR Γ⊢M∶A⇛B _) = context-validity Γ⊢M∶A⇛B
context-validity (ΛR Γ,A⊢M∶B) with context-validity Γ,A⊢M∶B
context-validity (ΛR _) | ctxTR validΓ = validΓ
context-validity (⊥R validΓ) = validΓ
context-validity (⊃R Γ⊢φ∶Ω _) = context-validity Γ⊢φ∶Ω
context-validity (appPR Γ⊢δ∶φ⊃ψ _) = context-validity Γ⊢δ∶φ⊃ψ
context-validity (ΛPR Γ⊢φ∶Ω _) = context-validity Γ⊢φ∶Ω
context-validity (convR Γ⊢M∶A _ _) = context-validity Γ⊢M∶A
context-validity (refR Γ⊢M∶A) = context-validity Γ⊢M∶A
context-validity (⊃*R Γ⊢φ∶Ω _) = context-validity Γ⊢φ∶Ω
context-validity (univR Γ⊢δ∶φ⊃ψ _) = context-validity Γ⊢δ∶φ⊃ψ
context-validity (plusR Γ⊢P∶φ≡ψ) = context-validity Γ⊢P∶φ≡ψ
context-validity (minusR Γ⊢P∶φ≡ψ) = context-validity Γ⊢P∶φ≡ψ
context-validity (lllR addpathΓ⊢P∶M≡N) = context-validity'' (context-validity addpathΓ⊢P∶M≡N)
context-validity (app*R Γ⊢N∶A _ _ _) = context-validity Γ⊢N∶A
context-validity (convER Γ⊢P∶M≡N _ _ _ _) = context-validity Γ⊢P∶M≡N

context-validity'' (ctxER (varR .(↑ x₀) (ctxTR (ctxTR validΓ))) _) = validΓ
\end{code}
}

\begin{theorem}[Weakening]
If $\Gamma \vdash \mathcal{J}$, $\Gamma \subseteq \Delta$ and $\Delta \vald$ then $\Delta \vdash \mathcal{J}$.
\end{theorem}

\begin{proof}
Induction on derivations.
\end{proof}

\AgdaHide{
\begin{code}
postulate _∶_⇒R_ : ∀ {U} {V} → Rep U V → Context U → Context V → Set

postulate weakening : ∀ {U} {V} {ρ : Rep U V} {K}
                    {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
                    Γ ⊢ M ∶ A → valid Δ → ρ ∶ Γ ⇒R Δ → Δ ⊢ M 〈 ρ 〉 ∶ A 〈 ρ 〉
\end{code}
}

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

postulate idRep-typed : ∀ {V} {Γ : Context V} → idRep V ∶ Γ ⇒R Γ

postulate upRep-typed : ∀ {V} {Γ : Context V} {K} {A} → upRep ∶ Γ ⇒R _,_ {K = K} Γ A

postulate liftRep-typed : ∀ {U} {V} {ρ : Rep U V} {K} {Γ} {Δ} {A} →
                     ρ ∶ Γ ⇒R Δ → liftRep K ρ ∶ (Γ , A) ⇒R (Δ , A 〈 ρ 〉)

postulate compR-typed : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Rep U V} {Γ} {Δ} {Θ : Context W} →
                        ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒R Δ → ρ •R σ ∶ Γ ⇒R Θ
\end{code}
}

Let $\Gamma$ and $\Delta$ be contexts.  A \emph{substitution} $\sigma : \Gamma \Rightarrow \Delta$
is a function mapping a term $\sigma(x)$ to every term variable $x \in \dom \Gamma$, a proof $\sigma(p)$ to
every proof variable $p \in \dom \Gamma$, and a path $\sigma(e)$ to every path variable $e \in \dom \Gamma$, such that:
\begin{itemize}
\item
for every term variable $x : A \in \Gamma$, we have $\Delta \vdash \sigma(x) : A$;
\item
for every proof variable $p : \phi \in \Gamma$, we have $\Delta \vdash \sigma(p) : \phi [ \sigma ]$;
\item
for every path variable $e : M =_A N \in \Gamma$, we have $\Delta \vdash \sigma(e) : M [ \sigma ] =_A N [ \sigma ]$
\end{itemize}
where $\phi [ \sigma ]$ is the result of substituting $\sigma(x)$ for every term variable $x$ in $\phi$.

\begin{code}
postulate _∶_⇒_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set
\end{code}

\begin{theorem}[Substitution]
If $\Gamma \vdash \mathcal{J}$, $\sigma : \Gamma \Rightarrow \Delta$ and $\Delta \vald$, then $\Delta \vdash \mathcal{J} [\sigma]$.
\end{theorem}

\begin{proof}
Induction on derivations.
\end{proof}

\AgdaHide{
\begin{code}
postulate substitution : ∀ {U} {V} {σ : Sub U V} {K}
                       {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
                       Γ ⊢ M ∶ A → valid Δ → σ ∶ Γ ⇒ Δ → Δ ⊢ M ⟦ σ ⟧ ∶ A ⟦ σ ⟧

postulate comp-typed : ∀ {U} {V} {W} {σ : Sub V W} {ρ : Sub U V} {Γ} {Δ} {Θ} →
                         σ ∶ Δ ⇒ Θ → ρ ∶ Γ ⇒ Δ → σ • ρ ∶ Γ ⇒ Θ

postulate compRS-typed : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                      ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒ Δ → ρ •RS σ ∶ Γ ⇒ Θ

postulate liftSub-typed : ∀ {U} {V} {K} {σ : Sub U V} {Γ} {Δ} {A} →
                     σ ∶ Γ ⇒ Δ → liftSub K σ ∶ Γ , A ⇒ Δ , A ⟦ σ ⟧

postulate change-type : ∀ {V} {Γ} {K} {M : Expression V (varKind K)} {A} {B} →
                      Γ ⊢ M ∶ A → A ≡ B → Γ ⊢ M ∶ B

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

extendSub : ∀ {U} {V} → Sub U V → Term V → Sub (U , -Term) V
extendSub σ M _ x₀ = M
extendSub σ M _ (↑ x) = σ _ x

postulate extendSub-typed : ∀ {U} {V} {σ : Sub U V} {M : Term V} {Γ} {Δ} {A} →
                          σ ∶ Γ ⇒ Δ → Δ ⊢ M ∶ ty A → extendSub σ M ∶ Γ ,T A ⇒ Δ
                                                                              
postulate extendSub-decomp : ∀ {U} {V} {σ : Sub U V} {M : Term V} {C} {K} (E : Subexpression (U , -Term) C K) →
                           E ⟦ liftSub -Term σ ⟧ ⟦ x₀:= M ⟧ ≡ E ⟦ extendSub σ M ⟧

postulate ⊃-gen₁ : ∀ {V} {Γ : Context V} {φ} {ψ} → Γ ⊢ φ ⊃ ψ ∶ ty Ω → Γ ⊢ φ ∶ ty Ω

postulate ⊃-gen₂ : ∀ {V} {Γ : Context V} {φ} {ψ} → Γ ⊢ φ ⊃ ψ ∶ ty Ω → Γ ⊢ ψ ∶ ty Ω

postulate Type-Reduction : ∀ {V} {Γ : Context V} {K} {M : Expression V (varKind K)} {A} {B} →
                         Γ ⊢ M ∶ A → A ↠ B → Γ ⊢ M ∶ B

postulate change-cod : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} → σ ∶ Γ ⇒ Δ → Δ ≡ Δ' → σ ∶ Γ ⇒ Δ'
postulate sub↖-typed : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {A} → σ ∶ Γ ⇒ Δ → sub↖ σ ∶ Γ ,T A ⇒ Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀

postulate sub↗-typed : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {A} → σ ∶ Γ ⇒ Δ → sub↗ σ ∶ Γ ,T A ⇒ Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀
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
If $\Gamma \vdash p : \phi$, then there exists $\psi$ such that $p : \psi \in \Gamma$ and $\phi \simeq_\beta \psi$.
\item
If $\Gamma \vdash \lambda p:\phi.\delta : \psi$, then there exists $\chi$ such that $\Gamma, p : \phi \vdash \delta : \chi$ and $\psi \simeq_\beta \phi \supset \chi$.
\item
If $\Gamma \vdash \delta \epsilon : \phi$ then there exists $\psi$ such that $\Gamma \vdash \delta : \psi \supset \phi$ and $\Gamma \vdash \epsilon : \psi$.
\item
If $\Gamma \vdash e : M =_A N$, then there exist $M'$, $N'$ such that $e : M' =_A N' \in \Gamma$ and $M \simeq_\beta M'$, $N \simeq_\beta N'$.
\item
If $\Gamma \vdash \reff{M} : N =_A P$, then we have $\Gamma \vdash M : A$ and $M \simeq_\beta N \simeq_\beta P$.
\item
If $\Gamma \vdash P \supset^* Q : \phi =_A \psi$, then there exist $\phi_1$, $\phi_2$, $\psi_1$, $\psi_2$ such that
$\Gamma \vdash P : \phi_1 =_\Omega \psi_1$, $\Gamma \vdash Q : \phi_2 =_\Omega \psi_2$, $\phi \simeq_\beta \phi_1 \supset \psi_1$, $\psi \simeq_\beta \phi_2 \supset \psi_2$, and $A \equiv \Omega$.
\item
If $\Gamma \vdash \univ{\phi}{\psi}{P}{Q} : \chi =_A \theta$, then we have $\Gamma \vdash P : \phi \supset \psi$, $\Gamma \vdash Q : \psi \supset \phi$,
$\Gamma \vdash \chi \simeq_\Delta \phi : \Omega$, $\Gamma \vdash \theta \simeq_\Delta \psi : \Omega$ and $A \equiv \Omega$.
\item
If $\Gamma \vdash \triplelambda e : x =_A y. P : M =_B N$ then there exists $C$ such that $\Gamma, x : A, y : A, e : x =_A y \vdash P : M x =_C N y$
and $B \equiv A \rightarrow C$.
\item
If $\Gamma \vdash P_{M M'} Q : N =_A N'$, then there exist $B$, $F$ and $G$ such that $\Gamma \vdash P : F =_{B \rightarrow A} G$, $\Gamma \vdash Q : M =_B M'$, $N \simeq_\beta F M$
and $N' \simeq_\beta G M'$.
\item
If $\Gamma \vdash P^+ : \phi$, then there exist $\psi$, $\chi$ such that $\Gamma \vdash P : \psi =_\Omega \chi$ and $\phi \simeq_\beta \psi \supset \chi$.
\item
If $\Gamma \vdash P^- : \phi$, there exist $\psi$, $\chi$ such that $\Gamma \vdash P : \psi =_\Omega \chi$ and $\phi \simeq_\beta \chi \supset \psi$.
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
\end{code}
}

Given substitutions $\sigma, \rho : \Gamma \rightarrow \Delta$, a \emph{path substitution} $\tau : \sigma \sim \rho$
is a function mapping every term variable $x \in \Gamma$ to a path $\tau(x)$ such that:
\begin{itemize}
\item
if $x : A \in \Gamma$ then $\Delta \vdash \tau(x) : \sigma(x) =_A \rho(x)$.
\end{itemize}

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

liftPathSub-typed : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {A} {Δ} → 
  τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ → valid Δ → liftPathSub τ ∶ sub↖ ρ ∼ sub↗ σ ∶ Γ ,T A ⇒ Δ ,T  A ,T  A ,E var x₁ ≡〈 A 〉 var x₀
liftPathSub-typed _ validΔ x₀ = varR x₀ (valid-addpath validΔ)
liftPathSub-typed {U} {Γ = Γ} {A} τ∶ρ∼σ validΔ (↑ x) = change-type (weakening (weakening (weakening (τ∶ρ∼σ x) (ctxTR validΔ) upRep-typed) 
                                                                           (ctxTR (ctxTR validΔ)) upRep-typed) 
                                                                (valid-addpath validΔ) upRep-typed) 
                                                    (cong₃ _≡〈_〉_ refl (sym (typeof'-up {U} {Γ = Γ} {A} {x = x})) refl)

postulate sub↖-decomp : ∀ {U} {V} {C} {K} (M : Subexpression (U , -Term) C K) {ρ : Sub U V} → 
                     M ⟦ liftSub _ ρ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= var x₂ ⟧ ≡ M ⟦ sub↖ ρ ⟧

postulate sub↗-decomp : ∀ {U} {V} {C} {K} (M : Subexpression (U , -Term) C K) {ρ : Sub U V} → 
                     M ⟦ liftSub _ ρ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= var x₁ ⟧ ≡ M ⟦ sub↗ ρ ⟧
\end{code}
}

\begin{prop}[Path Substitution]
If $\tau : \sigma \sim \rho : \Gamma \rightarrow \Delta$ and $\Gamma \vdash M : A$,
then $\Delta \vdash M \{ \tau : \sigma \sim \rho \} : M [ \sigma ] =_A M [ \rho ]$.
\end{prop}

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
      Mσ-typed = λ {σ} {x} σ∶Γ⇒Δ x∶A∈ΔAAE → appR (ΛR (weakening (weakening (weakening (substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed σ∶Γ⇒Δ)) 
                                                                                      (ctxTR (ctxTR validΔ)) (liftRep-typed upRep-typed)) 
                                                                           (ctxTR (ctxTR (ctxTR validΔ))) (liftRep-typed upRep-typed)) 
                                                                (ctxTR validΔAAE) (liftRep-typed upRep-typed))) 
                                                     (change-type (varR x validΔAAE) x∶A∈ΔAAE) in
  let step1 : Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀ ⊢ 
              M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ∼ sub↗ σ ⟧⟧ ∶ 
              appT ((ΛT A M) ⟦ ρ ⟧ ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT ((ΛT A M) ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₁)
      step1 = convER 
               (path-substitution Γ,A⊢M∶B 
                 (liftPathSub-typed τ∶σ∼σ' validΔ) (sub↖-typed ρ∶Γ⇒Δ) (sub↗-typed σ∶Γ⇒Δ) 
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

postulate liftPathSub-compRP : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} →
                          liftPathSub (ρ •RP τ) ∼∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RP liftPathSub τ

extendPS : ∀ {U} {V} → PathSub U V → Path V → PathSub (U , -Term) V
extendPS τ P x₀ = P
extendPS τ P (↑ x) = τ x

postulate extendPS-typed : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} {P} {M} {N} {A} →
                           τ ∶ ρ ∼ σ ∶ Γ ⇒ Δ → Δ ⊢ P ∶ M ≡〈 A 〉 N →
                           extendPS τ P ∶ extendSub ρ M ∼ extendSub σ N ∶ Γ ,T A ⇒ Δ

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

\begin{theorem}[Subject Reduction]
If $\Gamma \vdash s : T$ and $s \twoheadrightarrow t$ then $\Gamma \vdash t : T$.
\end{theorem}

\begin{proof}
It is sufficient to prove the case $s \rightarrow t$.  The proof is by a case analysis on $s \rightarrow t$, using the Generation Lemma.
\end{proof}

\AgdaHide{
\begin{code}
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
\end{code}

