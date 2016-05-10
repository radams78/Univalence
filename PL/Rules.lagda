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
data _⊢_∶_ : ∀ {P} → Context P → Proof P → Prp P → Set where
  var : ∀ {P} {Γ : Context P} {p : Var P -proof} → 
    Γ ⊢ var p ∶ typeof p Γ
  app : ∀ {P} {Γ : Context P} {δ} {ε} {φ} {ψ} → 
    Γ ⊢ δ ∶ φ ⇛ ψ → Γ ⊢ ε ∶ φ → Γ ⊢ appP δ ε ∶ ψ
  Λ : ∀ {P} {Γ : Context P} {φ} {δ} {ψ} → 
    Γ ,P φ ⊢ δ ∶ ψ 〈 upRep 〉 → Γ ⊢ ΛP φ δ ∶ φ ⇛ ψ
\end{code}

Let $\rho$ be a replacement.  We say $\rho$ is a replacement from $\Gamma$ to $\Delta$, $\rho : \Gamma \rightarrow \Delta$,
iff for all $x : \phi \in \Gamma$ we have $\rho(x) : \phi \in \Delta$.

\begin{code}
_∶_⇒R_ : ∀ {P} {Q} → Rep P Q → Context P → Context Q → Set
ρ ∶ Γ ⇒R Δ = ∀ x → typeof {K = -proof} (ρ _ x) Δ ≡ typeof x Γ 〈 ρ 〉
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
--TODO Replace idOpRep with idRep
idRep-typed : ∀ {P} {Γ : Context P} → idOpRep P ∶ Γ ⇒R Γ
\end{code}

\AgdaHide{
\begin{code}
idRep-typed {P} {Γ} x = sym rep-idOp
\end{code}
}

\begin{code}
↑-typed : ∀ {P} {Γ : Context P} {φ : Prp P} → upRep ∶ Γ ⇒R (Γ ,P φ)
\end{code}

\AgdaHide{
\begin{code}
↑-typed {P} {Γ} {φ} x = refl
\end{code}
}

\begin{code}
Rep↑-typed : ∀ {P} {Q} {ρ} {Γ : Context P} {Δ : Context Q} {φ : Prp P} → 
  ρ ∶ Γ ⇒R Δ → Rep↑ -proof ρ ∶ (Γ ,P φ) ⇒R (Δ ,P φ 〈 ρ 〉)
\end{code}

\AgdaHide{
\begin{code}
Rep↑-typed {P} {Q = Q} {ρ = ρ} {Γ} {Δ = Δ} {φ = φ} ρ∶Γ→Δ x₀ = sym (Rep↑-upRep φ)
Rep↑-typed {Q = Q} {ρ = ρ} {Γ = Γ} {Δ = Δ} {φ} ρ∶Γ→Δ (↑ x) = let open ≡-Reasoning in 
  begin
    typeof (Rep↑ -proof ρ -proof (↑ x)) (Δ ,P φ 〈 ρ 〉)
  ≡⟨⟩
    typeof (↑ (ρ -proof x)) (Δ ,P φ 〈 ρ 〉)
  ≡⟨⟩
    typeof (ρ -proof x) Δ 〈 upRep 〉
  ≡⟨ cong (λ x₁ → x₁ 〈 upRep 〉) (ρ∶Γ→Δ x) ⟩
    typeof x Γ 〈 ρ 〉 〈 upRep 〉
  ≡⟨⟨ Rep↑-upRep (typeof x Γ) ⟩⟩
    typeof x Γ 〈 upRep 〉 〈 Rep↑ -proof ρ 〉
  ≡⟨⟩
    typeof (↑ x) (Γ ,P φ) 〈 Rep↑ -proof ρ 〉
  ∎
\end{code}
}

\begin{code}
•R-typed : ∀ {P} {Q} {R} {σ : Rep Q R} {ρ : Rep P Q} {Γ} {Δ} {Θ} → 
  ρ ∶ Γ ⇒R Δ → σ ∶ Δ ⇒R Θ → (σ •R ρ) ∶ Γ ⇒R Θ
\end{code}

\AgdaHide{
\begin{code}
•R-typed {R = R} {σ} {ρ} {Γ} {Δ} {Θ} ρ∶Γ→Δ σ∶Δ→Θ x = let open ≡-Reasoning {A = Expression R prp} in 
  begin 
    typeof (σ -proof (ρ -proof x)) Θ
  ≡⟨ σ∶Δ→Θ (ρ -proof x) ⟩
    (typeof (ρ -proof x) Δ) 〈  σ 〉     
  ≡⟨ cong (λ x₁ → x₁ 〈  σ 〉) (ρ∶Γ→Δ x) ⟩
    typeof x Γ 〈  ρ 〉 〈  σ 〉            
  ≡⟨⟨ rep-comp (typeof x Γ) ⟩⟩
    typeof x Γ 〈  σ •R  ρ 〉    
  ∎
\end{code}
}

\begin{code}
Weakening : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} {ρ} {δ} {φ} → 
  Γ ⊢ δ ∶ φ → ρ ∶ Γ ⇒R Δ → Δ ⊢ δ 〈 ρ 〉 ∶ φ 〈 ρ 〉
\end{code}

\AgdaHide{
\begin{code}
Weakening {P} {Q} {Γ} {Δ} {ρ} (var {p = p}) ρ∶Γ→Δ = subst (λ x → Δ ⊢ var (ρ -proof p) ∶ x) 
  (ρ∶Γ→Δ p) 
  var
Weakening (app Γ⊢δ∶φ→ψ Γ⊢ε∶φ) ρ∶Γ→Δ = app (Weakening Γ⊢δ∶φ→ψ ρ∶Γ→Δ) (Weakening Γ⊢ε∶φ ρ∶Γ→Δ)
Weakening .{P} {Q} .{Γ} {Δ} {ρ} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∶ψ) ρ∶Γ→Δ = Λ 
  (subst (λ P → (Δ ,P φ 〈 ρ 〉) ⊢ δ 〈 Rep↑ -proof ρ 〉 ∶ P) 
  (Rep↑-upRep ψ)
  (Weakening {P , -proof} {Q , -proof} {Γ ,P φ} {Δ ,P φ 〈  ρ 〉} {Rep↑ -proof ρ} {δ} {ψ 〈 upRep 〉} 
    Γ,φ⊢δ∶ψ 
    claim)) where
  claim : ∀ (x : Var (P , -proof) -proof) → typeof (Rep↑ -proof ρ -proof x) (Δ ,P φ 〈 ρ 〉) ≡ typeof x (Γ ,P φ) 〈 Rep↑ -proof ρ 〉
  claim x₀ = sym (Rep↑-upRep φ)
  claim (↑ x) = let open ≡-Reasoning in 
    begin 
      typeof (ρ -proof x) Δ 〈 upRep 〉
    ≡⟨ cong (λ x → x 〈 upRep 〉) (ρ∶Γ→Δ x) ⟩
      typeof x Γ 〈 ρ 〉 〈 upRep 〉
    ≡⟨⟨ Rep↑-upRep (typeof x Γ) ⟩⟩
      typeof x Γ 〈 upRep 〉 〈 Rep↑ -proof ρ 〉     
    ∎
\end{code}
}
A \emph{substitution} $\sigma$ from a context $\Gamma$ to a context $\Delta$, $\sigma : \Gamma \rightarrow \Delta$,  is a substitution $\sigma$ such that
for every $x : \phi$ in $\Gamma$, we have $\Delta \vdash \sigma(x) : \phi$.

\begin{code}
_∶_⇒_ : ∀ {P} {Q} → Sub P Q → Context P → Context Q → Set
σ ∶ Γ ⇒ Δ = ∀ x → Δ ⊢ σ _ x ∶ typeof x Γ ⟦ σ ⟧
\end{code}

\begin{lemma}$ $
\begin{enumerate}
\item
If $\sigma : \Gamma \rightarrow \Delta$ then $(\sigma , \mathrm{Proof}) : (\Gamma , p : \phi) \rightarrow (\Delta , p : \phi [ \sigma ])$.
\item
If $\Gamma \vdash \delta : \phi$ then $(p := \delta) : (\Gamma, p : \phi) \rightarrow \Gamma$.
\item
(\textbf{Substitution Lemma})

If $\Gamma \vdash \delta : \phi$ and $\sigma : \Gamma \rightarrow \Delta$ then $\Delta \vdash \delta [ \sigma ] : \phi [ \sigma ]$.
\end{enumerate}
\end{lemma}

\begin{code}
Sub↑-typed : ∀ {P} {Q} {σ} 
  {Γ : Context P} {Δ : Context Q} {φ : Prp P} → 
  σ ∶ Γ ⇒ Δ → Sub↑ -proof σ ∶ (Γ ,P φ) ⇒ (Δ ,P φ ⟦ σ ⟧)
\end{code}

\AgdaHide{
\begin{code}
Sub↑-typed {P} {Q} {σ} {Γ} {Δ} {φ} σ∶Γ→Δ x₀ = subst (λ T → (Δ ,P φ ⟦ σ ⟧) ⊢ var x₀ ∶ T) 
  (sym (liftOp-up-mixed' COMP₂ COMP₁ (λ {_} {_} {_} {_} {E} → sym (up-is-up' {E = E})) {E = φ})) 
  (var {p = x₀})
Sub↑-typed {Q = Q} {σ = σ} {Γ = Γ} {Δ = Δ} {φ = φ} σ∶Γ→Δ (↑ x) = 
  subst
  (λ P → (Δ ,P φ ⟦ σ ⟧) ⊢ Sub↑ -proof σ -proof (↑ x) ∶ P)
  (sym (liftOp-up-mixed' COMP₂ COMP₁ (λ {_} {_} {_} {_} {E} → sym (up-is-up' {E = E})) {E = typeof x Γ}))
  (Weakening (σ∶Γ→Δ x) (↑-typed {φ = φ ⟦ σ ⟧}))
\end{code}
}

\begin{code}
botsub-typed : ∀ {P} {Γ : Context P} {φ : Prp P} {δ} →
  Γ ⊢ δ ∶ φ → x₀:= δ ∶ (Γ ,P φ) ⇒ Γ
\end{code}

\AgdaHide{
\begin{code}
botsub-typed {P} {Γ} {φ} {δ} Γ⊢δ∶φ x₀ = subst (λ P₁ → Γ ⊢ δ ∶ P₁) 
  (sym botsub-upRep) Γ⊢δ∶φ
botsub-typed {P} {Γ} {φ} {δ} _ (↑ x) = subst (λ P₁ → Γ ⊢ var x ∶ P₁) 
  (sym botsub-upRep) var
\end{code}
}

\begin{code}
Substitution : ∀ {P} {Q}
  {Γ : Context P} {Δ : Context Q} {δ} {φ} {σ} → 
  Γ ⊢ δ ∶ φ → σ ∶ Γ ⇒ Δ → Δ ⊢ δ ⟦ σ ⟧ ∶ φ ⟦ σ ⟧
\end{code}

\AgdaHide{
\begin{code}
Substitution var σ∶Γ→Δ = σ∶Γ→Δ _
Substitution (app Γ⊢δ∶φ→ψ Γ⊢ε∶φ) σ∶Γ→Δ = app (Substitution Γ⊢δ∶φ→ψ σ∶Γ→Δ) (Substitution Γ⊢ε∶φ σ∶Γ→Δ)
Substitution {Q = Q} {Δ = Δ} {σ = σ} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∶ψ) σ∶Γ→Δ = Λ 
  (subst (λ p → (Δ ,P φ ⟦ σ ⟧) ⊢ δ ⟦ Sub↑ -proof σ ⟧ ∶ p) 
  (let open ≡-Reasoning {A = Expression ( Q , -proof) prp} in
  begin 
    ψ 〈 upRep 〉 ⟦ Sub↑ -proof σ ⟧
  ≡⟨⟨ sub-comp₂ ψ ⟩⟩
    ψ ⟦ Sub↑ -proof σ •₂ (λ _ → ↑) ⟧  
  ≡⟨ sub-comp₁ ψ ⟩
    ψ ⟦ σ ⟧ 〈 upRep 〉
  ∎)
  (Substitution Γ,φ⊢δ∶ψ (Sub↑-typed σ∶Γ→Δ)))

prop-triv-red : ∀ {P} {φ ψ : Expression P prp} → φ ⇒ ψ → ⊥
prop-triv-red {_} {app -bot out} (redex ())
prop-triv-red {P} {app -bot out} (app ())
prop-triv-red {P} {app -imp (_,,_ _ (_,,_ _ out))} (redex ())
prop-triv-red {P} {app -imp (_,,_ φ (_,,_ ψ out))} (app (appl φ→φ')) = prop-triv-red {P} φ→φ'
prop-triv-red {P} {app -imp (_,,_ φ (_,,_ ψ out))} (app (appr (appl ψ→ψ'))) = prop-triv-red {P} ψ→ψ'
prop-triv-red {P} {app -imp (_,,_ _ (_,,_ _ out))} (app (appr (appr ())))
\end{code}
}

\begin{lemma}[Subject Reduction]
If $\Gamma \vdash \delta : \phi$ and $\delta \rightarrow_\beta \epsilon$ then $\Gamma \vdash \epsilon : \phi$.
\end{lemma}

\begin{code}
SR : ∀ {P} {Γ : Context P} {δ ε : Proof ( P)} {φ} → 
  Γ ⊢ δ ∶ φ → δ ⇒ ε → Γ ⊢ ε ∶ φ
\end{code}

\AgdaHide{
\begin{code}
SR var ()
SR (app {ε = ε} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∶ψ) Γ⊢ε∶φ) (redex βI) = 
  subst (λ P₁ → Γ ⊢ δ ⟦ x₀:= ε ⟧ ∶ P₁) 
  (let open ≡-Reasoning in
  begin 
    ψ 〈 upRep 〉 ⟦ x₀:= ε ⟧
  ≡⟨⟨ sub-comp₂ ψ ⟩⟩
    ψ ⟦ idOpSub P ⟧                 
  ≡⟨ sub-idOp ⟩
    ψ                           
  ∎) 
  (Substitution Γ,φ⊢δ∶ψ (botsub-typed Γ⊢ε∶φ))
SR (app Γ⊢δ∶φ→ψ Γ⊢ε∶φ) (app (appl δ→δ')) = app (SR Γ⊢δ∶φ→ψ δ→δ') Γ⊢ε∶φ
SR (app Γ⊢δ∶φ→ψ Γ⊢ε∶φ) (app (appr (appl ε→ε'))) = app Γ⊢δ∶φ→ψ (SR Γ⊢ε∶φ ε→ε')
SR (app Γ⊢δ∶φ→ψ Γ⊢ε∶φ) (app (appr (appr ())))
SR (Λ _) (redex ())
SR (Λ {P = P} {φ = φ} {δ = δ} {ψ = ψ} Γ⊢δ∶φ) (app (appl {E' = φ'} δ→ε)) = ⊥-elim (prop-triv-red {P = P} δ→ε)
SR (Λ Γ⊢δ∶φ) (app (appr (appl δ→ε))) = Λ (SR Γ⊢δ∶φ δ→ε)
SR (Λ _) (app (appr (appr ())))
\end{code}
}

