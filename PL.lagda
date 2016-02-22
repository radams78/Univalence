\begin{code}
module PL where

open import Prelims hiding (Rep)
open import Grammar
import Reduction
\end{code}

\section{Propositional Logic}

Fix sets of \emph{proof variables} and \emph{term variables}.

The syntax of the system is given by the following grammar.

\newcommand{\vald}{\ensuremath{\ \mathrm{valid}}}
\[ \begin{array}{lrcl}
\text{Proof} & \delta & ::= & p \mid \delta \delta \mid \lambda p : \phi . \delta \\
\text{Proposition} & φ & ::= & ⊥ \mid \phi \rightarrow \phi \\
\text{Context} & \Gamma & ::= & \langle \rangle \mid \Gamma, p : \phi \\
\text{Judgement} & \mathcal{J} & ::= & \Gamma \vdash \delta : \phi
\end{array} \]
where $p$ ranges over proof variables and $x$ ranges over term variables.  The variable $p$ is bound within $\delta$ in the proof $\lambda p : \phi . \delta$,
and the variable $x$ is bound within $M$ in the term $\lambda x : A . M$.  We identify proofs and terms up to $\alpha$-conversion.

\begin{code}
data PLVarKind : Set where
  -Proof : PLVarKind

data PLNonVarKind : Set where
  -Prp   : PLNonVarKind

PLtaxonomy : Taxonomy
PLtaxonomy = record { 
  VarKind = PLVarKind; 
  NonVarKind = PLNonVarKind }

module PLgrammar where
  open Grammar.Taxonomy PLtaxonomy

  data PLCon : ∀ {K : ExpressionKind} → ConstructorKind K → Set where
    app : PLCon (Π₂ (out (varKind -Proof)) (Π₂ (out (varKind -Proof)) (out₂ {K = varKind -Proof})))
    lam : PLCon (Π₂ (out (nonVarKind -Prp)) (Π₂ (Π (varKind -Proof) (out (varKind -Proof))) (out₂ {K = varKind -Proof})))
    bot : PLCon (out₂ {K = nonVarKind -Prp})
    imp : PLCon (Π₂ (out (nonVarKind -Prp)) (Π₂ (out (nonVarKind -Prp)) (out₂ {K = nonVarKind -Prp})))

  PLparent : VarKind → ExpressionKind
  PLparent -Proof = nonVarKind -Prp

open PLgrammar

Propositional-Logic : Grammar
Propositional-Logic = record { 
  taxonomy = PLtaxonomy; 
  toGrammar = record { 
    Constructor = PLCon; 
    parent = PLparent } }

open Grammar.Grammar Propositional-Logic
open Reduction Propositional-Logic

Prp : Set
Prp = Expression'' ∅ (nonVarKind -Prp)

⊥P : Prp
⊥P = app bot out₂

_⇒_ : ∀ {P} → Expression'' P (nonVarKind -Prp) → Expression'' P (nonVarKind -Prp) → Expression'' P (nonVarKind -Prp)
φ ⇒ ψ = app imp (app₂ (out φ) (app₂ (out ψ) out₂))

Proof : Alphabet → Set
Proof P = Expression'' P (varKind -Proof)

appP : ∀ {P} → Expression'' P (varKind -Proof) → Expression'' P (varKind -Proof) → Expression'' P (varKind -Proof)
appP δ ε = app app (app₂ (out δ) (app₂ (out ε) out₂))

ΛP : ∀ {P} → Expression'' P (nonVarKind -Prp) → Expression'' (P , -Proof) (varKind -Proof) → Expression'' P (varKind -Proof)
ΛP φ δ = app lam (app₂ (out φ) (app₂ (Λ (out δ)) out₂))

data β : Reduction where
  βI : ∀ {V} {φ} {δ} {ε} → β {V} app (Grammar.app₂ (Grammar.out (ΛP φ δ)) (Grammar.app₂ (Grammar.out ε) Grammar.out₂)) (δ ⟦ x₀:= ε ⟧)

β-respects-rep : respect-rep β
β-respects-rep {U} {V} {ρ = ρ} (βI .{U} {φ} {δ} {ε}) = subst (β app _) 
  (let open Equational-Reasoning (Expression'' V (varKind -Proof)) in
  ∵ (δ 〈 Rep↑ ρ 〉) ⟦ x₀:= (ε 〈 ρ 〉) ⟧
   ≡ δ ⟦ x₀:= (ε 〈 ρ 〉) •₂ Rep↑ ρ ⟧ [[ sub-comp₂ {E = δ} ]]
   ≡ δ ⟦ ρ •₁ x₀:= ε ⟧ [[ sub-wd {E = δ} comp₁-botsub ]]
   ≡ δ ⟦ x₀:= ε ⟧ 〈 ρ 〉 [ sub-comp₁ {E = δ} ]) 
  βI
\end{code}

The rules of deduction of the system are as follows.

\[ \infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald} \]

\[ \infer{\Gamma \vdash \delta \epsilon : \psi}{\Gamma \vdash \delta : \phi \rightarrow \psi}{\Gamma \vdash \epsilon : \phi} \]

\[ \infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \rightarrow \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]

\begin{code}
infix 10 _⊢_∷_
data _⊢_∷_ : ∀ {P} → Context P → Proof P → Expression'' P (nonVarKind -Prp) → Set where
  var : ∀ {P} {Γ : Context P} {p : Var P -Proof} → Γ ⊢ var p ∷ typeof p Γ
  app : ∀ {P} {Γ : Context P} {δ} {ε} {φ} {ψ} → Γ ⊢ δ ∷ φ ⇒ ψ → Γ ⊢ ε ∷ φ → Γ ⊢ appP δ ε ∷ ψ
  Λ : ∀ {P} {Γ : Context P} {φ} {δ} {ψ} → (_,_ {K = -Proof} Γ φ) ⊢ δ ∷ ψ 〈 (λ _ → ↑) 〉 → Γ ⊢ ΛP φ δ ∷ φ ⇒ ψ
\end{code}

A \emph{replacement} $\rho$ from a context $\Gamma$ to a context $\Delta$, $\rho : \Gamma \rightarrow \Delta$, is a replacement on the syntax such that,
for every $x : \phi$ in $\Gamma$, we have $\rho(x) : \phi \in \Delta$.

\begin{code}
_∷_⇒R_ : ∀ {P} {Q} → Rep P Q → Context P → Context Q → Set
ρ ∷ Γ ⇒R Δ = ∀ x → typeof (ρ -Proof x) Δ ≡ (typeof x Γ) 〈 ρ 〉

Rep↑-typed : ∀ {P} {Q} {ρ} {Γ : Context P} {Δ : Context Q} {φ : Expression'' P (nonVarKind -Prp)} → ρ ∷ Γ ⇒R Δ → 
  Rep↑ ρ ∷ (_,_ {P} { -Proof} Γ φ) ⇒R (_,_ {Q} { -Proof} Δ (φ 〈 ρ 〉))
Rep↑-typed {Q = Q} {ρ = ρ} {φ = φ} ρ∷Γ→Δ x₀ = let open Equational-Reasoning (Expression'' (Q , -Proof) (nonVarKind -Prp)) in 
  ∵ φ 〈 ρ 〉 〈 (λ _ → ↑) 〉
  ≡ φ 〈 (λ K x → ↑ (ρ K x)) 〉 [[ rep-comp {E = φ} ]]
  ≡ φ 〈 (λ _ → ↑) 〉 〈 Rep↑ ρ 〉 [ rep-comp {E = φ} ]
Rep↑-typed {Q = Q} {ρ = ρ} {Γ = Γ} {Δ = Δ} ρ∷Γ→Δ (↑ x) = let open Equational-Reasoning (Expression'' (Q , -Proof) (nonVarKind -Prp)) in
  ∵ typeof (ρ -Proof x) Δ 〈 (λ _ → ↑) 〉
  ≡ typeof x Γ 〈 ρ 〉 〈 (λ _ → ↑) 〉      [ wd (λ p → p 〈 (λ _ → ↑) 〉) (ρ∷Γ→Δ x) ]
  ≡ typeof x Γ 〈 (λ K x → ↑ (ρ K x)) 〉 [[ rep-comp {E = typeof x Γ} ]]
  ≡ typeof x Γ 〈 (λ _ → ↑) 〉 〈 Rep↑ ρ 〉 [ rep-comp {E = typeof x Γ} ]
\end{code}

Weakening Lemma

\begin{code}
Weakening : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} {ρ} {δ} {φ} → Γ ⊢ δ ∷ φ → ρ ∷ Γ ⇒R Δ → Δ ⊢ δ 〈 ρ 〉 ∷ φ 〈 ρ 〉
Weakening {P} {Q} {Γ} {Δ} {ρ} (var {p = p}) ρ∷Γ→Δ = subst (λ P → Δ ⊢ var (ρ -Proof p) ∷ P) (ρ∷Γ→Δ p) var
Weakening (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) ρ∷Γ→Δ = app (Weakening Γ⊢δ∷φ→ψ ρ∷Γ→Δ) (Weakening Γ⊢ε∷φ ρ∷Γ→Δ)
Weakening .{P} {Q} .{Γ} {Δ} {ρ} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∷ψ) ρ∷Γ→Δ = Λ (subst (λ P → (_,_ {Q} { -Proof} Δ (φ 〈 ρ 〉)) ⊢ δ 〈 Rep↑ ρ 〉 ∷ P) 
  (let open Equational-Reasoning (Expression'' (Q , -Proof) (nonVarKind -Prp)) in
  ∵ ψ 〈 (λ _ → ↑) 〉 〈 Rep↑ ρ 〉
  ≡ ψ 〈 (λ _ x → ↑ (ρ _ x)) 〉      [[ rep-comp {E = ψ} ]] 
  ≡ ψ 〈 ρ 〉 〈 (λ _ → ↑) 〉          [ rep-comp {E = ψ} ] ) 
  (Weakening Γ,φ⊢δ∷ψ (Rep↑-typed ρ∷Γ→Δ)))
\end{code}

A \emph{substitution} $\sigma$ from a context $\Gamma$ to a context $\Delta$, $\sigma : \Gamma \rightarrow \Delta$,  is a substitution $\sigma$ on the syntax such that,
for every $x : \phi$ in $\Gamma$, we have $\Delta \vdash \sigma(x) : \phi$.

\begin{code}
_∷_⇒_ : ∀ {P} {Q} → Sub P Q → Context P → Context Q → Set
σ ∷ Γ ⇒ Δ = ∀ x → Δ ⊢ σ _ x ∷ typeof x Γ ⟦ σ ⟧

Sub↑-typed : ∀ {P} {Q} {σ} {Γ : Context P} {Δ : Context Q} {φ : Expression'' P (nonVarKind -Prp)} → σ ∷ Γ ⇒ Δ → Sub↑ σ ∷ (_,_ {P} { -Proof} Γ φ) ⇒ (_,_ {Q} { -Proof} Δ (φ ⟦ σ ⟧))
Sub↑-typed {P} {Q} {σ} {Γ} {Δ} {φ} σ∷Γ→Δ x₀ = subst (λ p → (_,_ {Q} { -Proof} Δ (φ ⟦ σ ⟧)) ⊢ var x₀ ∷ p) 
  (let open Equational-Reasoning (Expression'' (Q , -Proof) (nonVarKind -Prp)) in
  ∵ φ ⟦ σ ⟧ 〈 (λ _ → ↑) 〉
  ≡ φ ⟦ (λ _ → ↑) •₁ σ ⟧      [[ sub-comp₁ {E = φ} ]]
  ≡ φ 〈 (λ _ → ↑) 〉 ⟦ Sub↑ σ ⟧ [ sub-comp₂ {E = φ} ]) 
  var
Sub↑-typed {Q = Q} {σ = σ} {Δ = Δ} {φ = φ} σ∷Γ→Δ (↑ x) = subst
  (λ P → _,_ {Q} { -Proof} Δ (φ ⟦ σ ⟧) ⊢ σ -Proof x 〈 (λ _ → ↑) 〉 ∷ P) 
  {!!} 
  (Weakening {!!} {!!})
\end{code}

Substitution Lemma

\begin{code}
Substitution : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} {δ} {φ} {σ} → Γ ⊢ δ ∷ φ → σ ∷ Γ ⇒ Δ → Δ ⊢ δ ⟦ σ ⟧ ∷ φ ⟦ σ ⟧
Substitution var σ∷Γ→Δ = σ∷Γ→Δ _
Substitution (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) σ∷Γ→Δ = app (Substitution Γ⊢δ∷φ→ψ σ∷Γ→Δ) (Substitution Γ⊢ε∷φ σ∷Γ→Δ)
Substitution {Q = Q} {Δ = Δ} {σ = σ} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∷ψ) σ∷Γ→Δ = Λ (subst (λ p → _,_ {Q} { -Proof} Δ (φ ⟦ σ ⟧) ⊢ δ ⟦ Sub↑ σ ⟧ ∷ p) 
  (let open Equational-Reasoning (Expression'' (Q , -Proof) (nonVarKind -Prp)) in
  ∵ ψ 〈 (λ _ → ↑) 〉 ⟦ Sub↑ σ ⟧
  ≡ ψ ⟦ Sub↑ σ •₂ (λ _ → ↑) ⟧  [[ sub-comp₂ {E = ψ} ]]
  ≡ (ψ ⟦ σ ⟧) 〈 (λ _ → ↑) 〉    [ sub-comp₁ {E = ψ} ]) 
  (Substitution Γ,φ⊢δ∷ψ {!!}))
\end{code}

Subject Reduction

\begin{code}
SR : ∀ {P} {Γ : Context P} {δ ε : Proof P} {φ} → Γ ⊢ δ ∷ φ → δ →〈 β 〉 ε → Γ ⊢ ε ∷ φ
SR var ()
SR (app (Λ Γ,φ⊢δ∷ψ) Γ⊢ε∷φ) (redex βI) = {!!}
SR (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) (Reduction.app x) = {!!}
SR (Λ Γ⊢δ∷φ) δ→ε = {!!}
\end{code}
We define the sets of \emph{computable} proofs $C_\Gamma(\phi)$ for each context $\Gamma$ and proposition $\phi$ as follows:

\begin{align*}
C_\Gamma(\bot) & = \{ \delta \mid \Gamma \vdash \delta : \bot, \delta \in SN \} \\
C_\Gamma(\phi \rightarrow \psi) & = \{ \delta \mid \Gamma : \delta : \phi \rightarrow \psi, \forall \epsilon \in C_\Gamma(\phi). \delta \epsilon \in C_\Gamma(\psi) \}
\end{align*}

\begin{code}
C : ∀ {P} → Context P → Prp → Proof P → Set
C Γ (app bot out₂) δ = (Γ ⊢ δ ∷ ⊥P 〈 (λ _ ()) 〉 ) ∧ SN β δ
C Γ (app imp (app₂ (out φ) (app₂ (out ψ) out₂))) δ = (Γ ⊢ δ ∷ (φ ⇒ ψ) 〈 (λ _ ()) 〉) ∧ 
  (∀ Q {Δ : Context Q} ρ ε → C Δ φ ε → C Δ ψ (appP (δ 〈 ρ 〉) ε))
\end{code}

The \emph{neutral terms} are those that begin with a variable.

\begin{code}
data Neutral {P} : Proof P → Set where
  varNeutral : ∀ x → Neutral (var x)
  appNeutral : ∀ δ ε → Neutral δ → Neutral (appP δ ε)
\end{code}

\begin{lemma}
Let $\Gamma \vdash \delta : \phi$.  
If $\delta$ is neutral and, for all $\epsilon$ such that $\delta \rightarrow_\beta \epsilon$, we have $\epsilon \in C_\Gamma(\phi)$, then $\delta \in C_\Gamma(\phi)$.
\end{lemma}

\begin{code}
NeutralC : ∀ {P} {Γ : Context P} {δ : Proof P} {φ : Prp} →
  Γ ⊢ δ ∷ (φ 〈 (λ _ ()) 〉) → Neutral δ →
  (∀ ε → δ →〈 β 〉 ε → C Γ φ ε) →
  C Γ φ δ
NeutralC {P} {Γ} {δ} {app bot out₂} Γ⊢δ∷⊥ Neutralδ hyp = Γ⊢δ∷⊥ , SNI δ (λ ε δ→ε → π₂ (NeutralC {φ = ⊥P} {!!} {!!} {!!}))
NeutralC {P} {Γ} {δ} {ToGrammar.app imp φ} Γ⊢δ∷φ Neutralδ hyp = {!!}
\end{code}

\begin{lemma}
\[ C_\Gamma(\phi) \subseteq SN \]
\end{lemma}

\begin{code}
CsubSN : ∀ {P} {Γ : Context P} {φ} {δ} → C Γ φ δ → SN β δ
CsubSN {P} {Γ} {ToGrammar.app bot ToGrammar.out₂} P₁ = π₂ P₁
CsubSN {P} {Γ} {app imp (app₂ (out φ) (app₂ (out ψ) out₂))} {δ} P₁ = SNrep' β-respects-rep (SNoutA (SNsubbodyl (SNsubexp (CsubSN {φ = ψ} (π₂ P₁ (P , -Proof) (λ _ → ↑) (var x₀) {!!})))))
\end{code}
