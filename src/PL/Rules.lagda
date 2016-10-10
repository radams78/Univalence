\AgdaHide{
\begin{code}
module PL.Rules where
open import Data.Empty
open import Prelims
open import PL.Grammar
open PLgrammar
open import Grammar Propositional-Logic
open import Reduction Propositional-Logic β
\end{code}
}

\subsection{Rules of Deduction}

The rules of deduction of the system are as follows.

\[ \infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald} \]

\[ \infer{\Gamma \vdash \delta \epsilon : \psi}{\Gamma \vdash \delta : \phi \rightarrow \psi}{\Gamma \vdash \epsilon : \phi} \]

\[ \infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \rightarrow \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]

\begin{code}
infix 10 _⊢_∶_
data _⊢_∶_ : ∀ {P} → Context P → Proof P → Prop → Set where
  var : ∀ {P} {Γ : Context P} (p : Var P -proof) → 
    Γ ⊢ var p ∶ unprp (typeof p Γ)
  app : ∀ {P} {Γ : Context P} {δ} {ε} {φ} {ψ} → 
    Γ ⊢ δ ∶ φ ⇛ ψ → Γ ⊢ ε ∶ φ → Γ ⊢ appP δ ε ∶ ψ
  Λ : ∀ {P} {Γ : Context P} {φ} {δ} {ψ} → 
    Γ ,P φ ⊢ δ ∶ ψ → Γ ⊢ ΛP φ δ ∶ φ ⇛ ψ
\end{code}

\AgdaHide{
\begin{code}
change-type : ∀ {P} {Γ : Context P} {δ φ ψ} →
  φ ≡ ψ → Γ ⊢ δ ∶ φ → Γ ⊢ δ ∶ ψ
change-type = subst (λ A → _ ⊢ _ ∶ A)
\end{code}
}

Let $\rho$ be a replacement.  We say $\rho$ is a replacement from $\Gamma$ to $\Delta$, $\rho : \Gamma \rightarrow \Delta$,
iff for all $x : \phi \in \Gamma$ we have $\rho(x) : \phi \in \Delta$.

\begin{code}
_∶_⇒R_ : ∀ {P} {Q} → Rep P Q → Context P → Context Q → Set
ρ ∶ Γ ⇒R Δ = ∀ x → unprp (typeof {K = -proof} (ρ _ x) Δ) ≡ unprp (typeof x Γ )
\end{code}

\begin{lemma}$ $
\begin{enumerate}
\item
$\id{P}$ is a replacement $\Gamma \rightarrow \Gamma$.
\item
$\uparrow$ is a replacement $\Gamma \rightarrow \Gamma , \phi$.
\item
If $\rho : \Gamma \rightarrow \Delta$ then $(\rho , \mathrm{Proof}) : (\Gamma , x : \phi) \rightarrow (\Delta , x : \phi)$.
\item
If $\rho : \Gamma \rightarrow \Delta$ and $\sigma : \Delta \rightarrow \Theta$ then $\sigma \circ \rho : \Gamma \rightarrow \Delta$.
\item
(\textbf{Weakening})
If $\rho : \Gamma \rightarrow \Delta$ and $\Gamma \vdash \delta : \phi$ then $\Delta \vdash \delta \langle \rho \rangle : \phi$.
\end{enumerate}
\end{lemma}

\begin{code}
idRep-typed : ∀ {P} {Γ : Context P} → idRep P ∶ Γ ⇒R Γ
\end{code}

\AgdaHide{
\begin{code}
idRep-typed {P} {Γ} x = refl
\end{code}
}

\begin{code}
unprp-rep : ∀ {U V} φ (ρ : Rep U V) → unprp (φ 〈 ρ 〉) ≡ unprp φ
unprp-rep (app (-prp _) []) _ = refl

↑-typed : ∀ {P} {Γ : Context P} {φ : Prop} → upRep ∶ Γ ⇒R (Γ ,P φ)
\end{code}

\AgdaHide{
\begin{code}
↑-typed {P} {Γ} {φ} x = unprp-rep (typeof x Γ) upRep
\end{code}
}

\begin{code}
liftRep-typed : ∀ {P} {Q} {ρ} {Γ : Context P} {Δ : Context Q} {φ : Prop} → 
  ρ ∶ Γ ⇒R Δ → liftRep -proof ρ ∶ (Γ ,P φ) ⇒R (Δ ,P φ)
\end{code}

\AgdaHide{
\begin{code}
liftRep-typed {P} {Q = Q} {ρ = ρ} {Γ} {Δ = Δ} {φ = φ} ρ∶Γ→Δ x₀ = refl
liftRep-typed {Q = Q} {ρ = ρ} {Γ = Γ} {Δ = Δ} {φ} ρ∶Γ→Δ (↑ x) = 
  let open ≡-Reasoning in 
  begin
    unprp (typeof (liftRep -proof ρ -proof (↑ x)) (Δ ,P φ))
  ≡⟨⟩
    unprp (typeof (↑ (ρ -proof x)) (Δ ,P φ))
  ≡⟨⟩
    unprp (typeof (ρ -proof x) Δ 〈 upRep 〉)
  ≡⟨ unprp-rep (typeof (ρ -proof x) Δ) upRep ⟩
    unprp (typeof (ρ -proof x) Δ)
  ≡⟨ ρ∶Γ→Δ x ⟩
    unprp (typeof x Γ)
  ≡⟨⟨ unprp-rep (typeof x Γ) upRep ⟩⟩
    unprp (typeof x Γ 〈 upRep 〉)
  ≡⟨⟩
    unprp (typeof (↑ x) (Γ ,P φ))
  ∎
\end{code}
}

\begin{code}
•R-typed : ∀ {P} {Q} {R} {σ : Rep Q R} {ρ : Rep P Q} {Γ} {Δ} {Θ} → 
  ρ ∶ Γ ⇒R Δ → σ ∶ Δ ⇒R Θ → (σ •R ρ) ∶ Γ ⇒R Θ
\end{code}

\AgdaHide{
\begin{code}
•R-typed {R = R} {σ} {ρ} {Γ} {Δ} {Θ} ρ∶Γ→Δ σ∶Δ→Θ x = let open ≡-Reasoning in 
  begin 
    unprp (typeof (σ -proof (ρ -proof x)) Θ)
  ≡⟨ σ∶Δ→Θ (ρ -proof x) ⟩
    unprp (typeof (ρ -proof x) Δ)
  ≡⟨ ρ∶Γ→Δ x ⟩
    unprp (typeof x Γ)
  ∎
\end{code}
}

\begin{code}
Weakening : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} {ρ} {δ} {φ} → 
  Γ ⊢ δ ∶ φ → ρ ∶ Γ ⇒R Δ → Δ ⊢ δ 〈 ρ 〉 ∶ φ
\end{code}

\AgdaHide{
\begin{code}
Weakening {P} {Q} {Γ} {Δ} {ρ} (var p) ρ∶Γ→Δ = change-type (ρ∶Γ→Δ p) (var (ρ _ p))
Weakening (app Γ⊢δ∶φ→ψ Γ⊢ε∶φ) ρ∶Γ→Δ = app (Weakening Γ⊢δ∶φ→ψ ρ∶Γ→Δ) (Weakening Γ⊢ε∶φ ρ∶Γ→Δ)
Weakening .{P} {Q} .{Γ} {Δ} {ρ} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∶ψ) ρ∶Γ→Δ = Λ 
  (Weakening {P , -proof} {Q , -proof} {Γ ,P φ} {Δ ,P φ} {liftRep -proof ρ} {δ} {ψ} 
    Γ,φ⊢δ∶ψ (liftRep-typed ρ∶Γ→Δ))
\end{code}
}
A \emph{substitution} $\sigma$ from a context $\Gamma$ to a context $\Delta$, $\sigma : \Gamma \rightarrow \Delta$,  is a substitution $\sigma$ such that
for every $x : \phi$ in $\Gamma$, we have $\Delta \vdash \sigma(x) : \phi$.

\begin{code}
_∶_⇒_ : ∀ {P} {Q} → Sub P Q → Context P → Context Q → Set
σ ∶ Γ ⇒ Δ = ∀ x → Δ ⊢ σ _ x ∶ unprp (typeof x Γ)
\end{code}

\begin{lemma}$ $
\begin{enumerate}
\item
If $\sigma : \Gamma \rightarrow \Delta$ then $(\sigma , \mathrm{Proof}) : (\Gamma , p : \phi) \rightarrow (\Delta , p : \phi [ \sigma ])$.
\item
If $\Gamma \vdash \delta : \phi$ then $(p := \delta) : (\Gamma, p : \phi) \rightarrow \Gamma$.
\item
(\textbf{substitution Lemma})

If $\Gamma \vdash \delta : \phi$ and $\sigma : \Gamma \rightarrow \Delta$ then $\Delta \vdash \delta [ \sigma ] : \phi [ \sigma ]$.
\end{enumerate}
\end{lemma}

\begin{code}
liftSub-typed : ∀ {P} {Q} {σ} 
  {Γ : Context P} {Δ : Context Q} {φ : Prop} → 
  σ ∶ Γ ⇒ Δ → liftSub -proof σ ∶ (Γ ,P φ) ⇒ (Δ ,P φ)
\end{code}

\AgdaHide{
\begin{code}
liftSub-typed {σ = σ} {Γ} {Δ} {φ} σ∶Γ⇒Δ x =
  change-type (sym (unprp-rep (pretypeof x (Γ ,P φ)) upRep)) (pre-LiftSub-typed x) where
  pre-LiftSub-typed : ∀ x → Δ ,P φ ⊢ liftSub -proof σ -proof x ∶ unprp (pretypeof x (Γ ,P φ))
  pre-LiftSub-typed x₀ = var x₀
  pre-LiftSub-typed (↑ x) = Weakening (σ∶Γ⇒Δ x) (↑-typed {φ = φ})
\end{code}
}

\begin{code}
botSub-typed : ∀ {P} {Γ : Context P} {φ : Prop} {δ} →
  Γ ⊢ δ ∶ φ → x₀:= δ ∶ (Γ ,P φ) ⇒ Γ
\end{code}

\AgdaHide{
\begin{code}
botSub-typed {P} {Γ} {φ} {δ} Γ⊢δ:φ x = 
  change-type (sym (unprp-rep (pretypeof x (Γ ,P φ)) upRep)) (pre-botSub-typed x) where
  pre-botSub-typed : ∀ x → Γ ⊢ (x₀:= δ) -proof x ∶ unprp (pretypeof x (Γ ,P φ))
  pre-botSub-typed x₀ = Γ⊢δ:φ
  pre-botSub-typed (↑ x) = var x
\end{code}
}

\begin{code}
substitution : ∀ {P} {Q}
  {Γ : Context P} {Δ : Context Q} {δ} {φ} {σ} → 
  Γ ⊢ δ ∶ φ → σ ∶ Γ ⇒ Δ → Δ ⊢ δ ⟦ σ ⟧ ∶ φ
\end{code}

\AgdaHide{
\begin{code}
substitution (var _) σ∶Γ→Δ = σ∶Γ→Δ _
substitution (app Γ⊢δ∶φ→ψ Γ⊢ε∶φ) σ∶Γ→Δ = app (substitution Γ⊢δ∶φ→ψ σ∶Γ→Δ) (substitution Γ⊢ε∶φ σ∶Γ→Δ)
substitution {Q = Q} {Δ = Δ} {σ = σ} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∶ψ) σ∶Γ→Δ = Λ 
  (substitution Γ,φ⊢δ∶ψ (liftSub-typed σ∶Γ→Δ))
\end{code}
}

\begin{lemma}[Subject Reduction]
If $\Gamma \vdash \delta : \phi$ and $\delta \rightarrow_\beta \epsilon$ then $\Gamma \vdash \epsilon : \phi$.
\end{lemma}

\begin{code}
subject-reduction : ∀ {P} {Γ : Context P} {δ ε : Proof ( P)} {φ} → 
  Γ ⊢ δ ∶ φ → δ ⇒ ε → Γ ⊢ ε ∶ φ
\end{code}

\AgdaHide{
\begin{code}
subject-reduction (var _) ()
subject-reduction (app {ε = ε} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∶ψ) Γ⊢ε∶φ) (redex βI) = 
  substitution Γ,φ⊢δ∶ψ (botSub-typed Γ⊢ε∶φ)
subject-reduction (app Γ⊢δ∶φ→ψ Γ⊢ε∶φ) (app (appl δ→δ')) = app (subject-reduction Γ⊢δ∶φ→ψ δ→δ') Γ⊢ε∶φ
subject-reduction (app Γ⊢δ∶φ→ψ Γ⊢ε∶φ) (app (appr (appl ε→ε'))) = app Γ⊢δ∶φ→ψ (subject-reduction Γ⊢ε∶φ ε→ε')
subject-reduction (app Γ⊢δ∶φ→ψ Γ⊢ε∶φ) (app (appr (appr ())))
subject-reduction (Λ _) (redex ())
subject-reduction (Λ Γ,φ⊢δ∶ψ) (app (appl δ⇒ε)) = Λ (subject-reduction Γ,φ⊢δ∶ψ δ⇒ε)
subject-reduction (Λ Γ⊢δ∶φ) (app (appr ()))
\end{code}
}

