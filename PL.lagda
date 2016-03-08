\begin{code}
module PL where

open import Prelims
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
  βI : ∀ {V} {φ} {δ} {ε} → β {V} app (app₂ (out (ΛP φ δ)) (app₂ (out ε) out₂)) (δ ⟦ x₀:= ε ⟧)

β-respects-rep : respect-rep β
β-respects-rep {U} {V} {ρ = ρ} (βI .{U} {φ} {δ} {ε}) = subst (β app _) 
  (let open Equational-Reasoning (Expression'' V (varKind -Proof)) in
  ∵ (rep δ (Rep↑ ρ)) ⟦ x₀:= (rep ε ρ) ⟧
   ≡ δ ⟦ x₀:= (rep ε ρ) •₂ Rep↑ ρ ⟧ [[ sub-comp₂ {E = δ} ]]
   ≡ δ ⟦ ρ •₁ x₀:= ε ⟧ [[ sub-wd {E = δ} comp₁-botsub ]]
   ≡ rep (δ ⟦ x₀:= ε ⟧) ρ [ sub-comp₁ {E = δ} ]) 
  βI

β-creates-rep : create-rep β
β-creates-rep = record { 
  created = created;
  red-created = red-created; 
  rep-created = rep-created } where
  created : ∀ {U V : Alphabet} {K} {C} {c : PLCon C} {EE : Expression' U (-Constructor K) C} {F} {ρ} → β {V} c (rep EE ρ) F → Expression'' U K
  created {c = app} {EE = app₂ (out (var _)) _} ()
  created {c = app} {EE = app₂ (out (app app _)) _} ()
  created {c = app} {EE = app₂ (out (app lam (app₂ (out φ) (app₂ (Λ (out δ)) out₂)))) (app₂ (out ε) out₂)} βI = δ ⟦ x₀:= ε ⟧
  created {c = lam} ()
  created {c = bot} ()
  created {c = imp} ()
  red-created : ∀ {U} {V} {K} {C} {c : PLCon C} {EE : Expression' U (-Constructor K) C} {F} {ρ : Rep U V} (δ : β c (rep EE ρ) F) → β {U} c EE (created {U} {V} {K} {C} δ)
  red-created {c = app} {EE = app₂ (out (var _)) _} ()
  red-created {c = app} {EE = app₂ (out (app app _)) _} ()
  red-created {c = app} {EE = app₂ (out (app lam (app₂ (out φ) (app₂ (Λ (out δ)) out₂)))) (app₂ (out ε) out₂)} βI = βI
  red-created {c = lam} ()
  red-created {c = bot} ()
  red-created {c = imp} ()
  rep-created : ∀ {U} {V} {K} {C} {c : PLCon C} {EE : Expression' U (-Constructor K) C} {F} {ρ} δ → rep (created {U} {V} {K} {C} {c} {EE} {F} {ρ} δ) ρ ≡ F
  rep-created {c = app} {EE = app₂ (out (var _)) _} ()
  rep-created {c = app} {EE = app₂ (out (app app _)) _} ()
  rep-created {c = app} {EE = app₂ (out (app lam (app₂ (out φ) (app₂ (Λ (out δ)) out₂)))) (app₂ (out ε) out₂)} {ρ = ρ} βI = let open Equational-Reasoning (Expression'' _ (varKind -Proof)) in 
    ∵ rep (δ ⟦ x₀:= ε ⟧) ρ
    ≡ δ ⟦ ρ •₁ x₀:= ε ⟧                 [[ sub-comp₁ {E = δ} ]]
    ≡ δ ⟦ x₀:= (rep ε ρ) •₂ Rep↑ ρ ⟧    [ sub-wd {E = δ} comp₁-botsub ]
    ≡ rep δ (Rep↑ ρ) ⟦ x₀:= (rep ε ρ) ⟧ [ sub-comp₂ {E = δ} ]
  rep-created {c = lam} ()
  rep-created {c = bot} ()
  rep-created {c = imp} ()
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
  Λ : ∀ {P} {Γ : Context P} {φ} {δ} {ψ} → (_,_ {K = -Proof} Γ φ) ⊢ δ ∷ lift ψ → Γ ⊢ ΛP φ δ ∷ φ ⇒ ψ
\end{code}

A \emph{replacement} $\rho$ from a context $\Gamma$ to a context $\Delta$, $\rho : \Gamma \rightarrow \Delta$, is a replacement on the syntax such that,
for every $x : \phi$ in $\Gamma$, we have $\rho(x) : \phi \in \Delta$.

\begin{code}
_∷_⇒R_ : ∀ {P} {Q} → Rep P Q → Context P → Context Q → Set
ρ ∷ Γ ⇒R Δ = ∀ x → typeof (ρ -Proof x) Δ ≡ rep (typeof x Γ) ρ

↑-typed : ∀ {P} {Γ : Context P} {φ : Expression'' P (nonVarKind -Prp)} → 
  (λ _ → ↑) ∷ Γ ⇒R (_,_ {P} { -Proof} Γ φ)
↑-typed x₀ = ref
↑-typed (↑ _) = ref

Rep↑-typed : ∀ {P} {Q} {ρ} {Γ : Context P} {Δ : Context Q} {φ : Expression'' P (nonVarKind -Prp)} → ρ ∷ Γ ⇒R Δ → 
  Rep↑ ρ ∷ (_,_ {P} { -Proof} Γ φ) ⇒R (_,_ {Q} { -Proof} Δ (rep φ ρ))
Rep↑-typed {Q = Q} {ρ = ρ} {φ = φ} ρ∷Γ→Δ x₀ = let open Equational-Reasoning (Expression'' (Q , -Proof) (nonVarKind -Prp)) in 
  ∵ rep (rep φ ρ) (λ _ → ↑)
  ≡ rep φ (λ K x → ↑ (ρ K x))      [[ rep-comp {E = φ} ]]
  ≡ rep (rep φ (λ _ → ↑)) (Rep↑ ρ) [ rep-comp {E = φ} ]
Rep↑-typed {Q = Q} {ρ = ρ} {Γ = Γ} {Δ = Δ} ρ∷Γ→Δ (↑ x) = let open Equational-Reasoning (Expression'' (Q , -Proof) (nonVarKind -Prp)) in
  ∵ rep (typeof (ρ -Proof x) Δ) (λ _ → ↑)
  ≡ rep (rep (typeof x Γ) ρ) (λ _ → ↑)        [ wd (λ p → rep p (λ _ → ↑)) (ρ∷Γ→Δ x) ]
  ≡ rep (typeof x Γ) (λ K x → ↑ (ρ K x))      [[ rep-comp {E = typeof x Γ} ]]
  ≡ rep (rep (typeof x Γ) (λ _ → ↑)) (Rep↑ ρ) [ rep-comp {E = typeof x Γ} ]
\end{code}

The replacements between contexts are closed under composition.

\begin{code}
•R-typed : ∀ {P} {Q} {R} {σ : Rep Q R} {ρ : Rep P Q} {Γ} {Δ} {Θ} → ρ ∷ Γ ⇒R Δ → σ ∷ Δ ⇒R Θ →
  σ •R ρ ∷ Γ ⇒R Θ
•R-typed {R = R} {σ} {ρ} {Γ} {Δ} {Θ} ρ∷Γ→Δ σ∷Δ→Θ x = let open Equational-Reasoning (Expression'' R (nonVarKind -Prp)) in 
  ∵ typeof (σ -Proof (ρ -Proof x)) Θ
  ≡ rep (typeof (ρ -Proof x) Δ) σ     [ σ∷Δ→Θ (ρ -Proof x) ]
  ≡ rep (rep (typeof x Γ) ρ) σ        [ wd (λ x₁ → rep x₁ σ) (ρ∷Γ→Δ x) ]
  ≡ rep (typeof x Γ) (σ •R ρ)         [[ rep-comp ]]
\end{code}

Weakening Lemma

\begin{code}
Weakening : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} {ρ} {δ} {φ} → Γ ⊢ δ ∷ φ → ρ ∷ Γ ⇒R Δ → Δ ⊢ rep δ ρ ∷ rep φ ρ
Weakening {P} {Q} {Γ} {Δ} {ρ} (var {p = p}) ρ∷Γ→Δ = subst (λ P → Δ ⊢ var (ρ -Proof p) ∷ P) (ρ∷Γ→Δ p) var
Weakening (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) ρ∷Γ→Δ = app (Weakening Γ⊢δ∷φ→ψ ρ∷Γ→Δ) (Weakening Γ⊢ε∷φ ρ∷Γ→Δ)
Weakening .{P} {Q} .{Γ} {Δ} {ρ} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∷ψ) ρ∷Γ→Δ = Λ 
  (subst (λ P → (_,_ {Q} { -Proof} Δ (rep φ ρ)) ⊢ rep δ (Rep↑ ρ) ∷ P) 
  (let open Equational-Reasoning (Expression'' (Q , -Proof) (nonVarKind -Prp)) in
  ∵ rep (rep ψ (λ _ → ↑)) (Rep↑ ρ)
  ≡ rep ψ (λ _ x → ↑ (ρ _ x))      [[ rep-comp {E = ψ} ]] 
  ≡ rep (rep ψ ρ) (λ _ → ↑)          [ rep-comp {E = ψ} ] ) 
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
  ∵ rep (φ ⟦ σ ⟧) (λ _ → ↑)
  ≡ φ ⟦ (λ _ → ↑) •₁ σ ⟧      [[ sub-comp₁ {E = φ} ]]
  ≡ rep φ (λ _ → ↑) ⟦ Sub↑ σ ⟧ [ sub-comp₂ {E = φ} ]) 
  var
Sub↑-typed {Q = Q} {σ = σ} {Γ = Γ} {Δ = Δ} {φ = φ} σ∷Γ→Δ (↑ x) = 
  subst
  (λ P → _,_ {Q} { -Proof} Δ (φ ⟦ σ ⟧) ⊢ Sub↑ σ -Proof (↑ x) ∷ P)
  (let open Equational-Reasoning (Expression'' (Q , -Proof) (nonVarKind -Prp)) in 
  ∵ rep (typeof x Γ ⟦ σ ⟧) (λ _ → ↑)
  ≡ typeof x Γ ⟦ (λ _ → ↑) •₁ σ ⟧      [[ sub-comp₁ {E = typeof x Γ} ]]
  ≡ rep (typeof x Γ) (λ _ → ↑) ⟦ Sub↑ σ ⟧ [ sub-comp₂ {E = typeof x Γ} ])
  (Weakening (σ∷Γ→Δ x) (↑-typed {φ = φ ⟦ σ ⟧}))

botsub-typed : ∀ {P} {Γ : Context P} {φ : Expression'' P (nonVarKind -Prp)} {δ} →
  Γ ⊢ δ ∷ φ → x₀:= δ ∷ (_,_ {P} { -Proof} Γ φ) ⇒ Γ
botsub-typed {P} {Γ} {φ} {δ} Γ⊢δ∷φ x₀ = subst (λ P₁ → Γ ⊢ δ ∷ P₁) 
  (let open Equational-Reasoning (Expression'' P (nonVarKind -Prp)) in 
  ∵ φ
  ≡ φ ⟦ idSub ⟧                   [[ subid ]]
  ≡ rep φ (λ _ → ↑) ⟦ x₀:= δ ⟧     [ sub-comp₂ {E = φ} ]) 
  Γ⊢δ∷φ
botsub-typed {P} {Γ} {φ} {δ} _ (↑ x) = subst (λ P₁ → Γ ⊢ var x ∷ P₁) 
  (let open Equational-Reasoning (Expression'' P (nonVarKind -Prp)) in 
  ∵ typeof x Γ
  ≡ typeof x Γ ⟦ idSub ⟧                [[ subid ]]
  ≡ rep (typeof x Γ) (λ _ → ↑) ⟦ x₀:= δ ⟧ [ sub-comp₂ {E = typeof x Γ} ]) 
  var
\end{code}

Substitution Lemma

\begin{code}
Substitution : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} {δ} {φ} {σ} → Γ ⊢ δ ∷ φ → σ ∷ Γ ⇒ Δ → Δ ⊢ δ ⟦ σ ⟧ ∷ φ ⟦ σ ⟧
Substitution var σ∷Γ→Δ = σ∷Γ→Δ _
Substitution (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) σ∷Γ→Δ = app (Substitution Γ⊢δ∷φ→ψ σ∷Γ→Δ) (Substitution Γ⊢ε∷φ σ∷Γ→Δ)
Substitution {Q = Q} {Δ = Δ} {σ = σ} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∷ψ) σ∷Γ→Δ = Λ 
  (subst (λ p → _,_ {Q} { -Proof} Δ (φ ⟦ σ ⟧) ⊢ δ ⟦ Sub↑ σ ⟧ ∷ p) 
  (let open Equational-Reasoning (Expression'' (Q , -Proof) (nonVarKind -Prp)) in
  ∵ rep ψ (λ _ → ↑) ⟦ Sub↑ σ ⟧
  ≡ ψ ⟦ Sub↑ σ •₂ (λ _ → ↑) ⟧  [[ sub-comp₂ {E = ψ} ]]
  ≡ rep (ψ ⟦ σ ⟧) (λ _ → ↑)    [ sub-comp₁ {E = ψ} ])
  (Substitution Γ,φ⊢δ∷ψ (Sub↑-typed σ∷Γ→Δ)))
\end{code}

Subject Reduction

\begin{code}
prop-triv-red : ∀ {P} {φ ψ : Expression'' P (nonVarKind -Prp)} → φ →〈 β 〉 ψ → False
prop-triv-red {_} {app bot out₂} (redex ())
prop-triv-red {P} {app bot out₂} (app ())
prop-triv-red {P} {app imp (app₂ _ (app₂ _ out₂))} (redex ())
prop-triv-red {P} {app imp (app₂ (out φ) (app₂ ψ out₂))} (app (appl (out φ→φ'))) = prop-triv-red φ→φ'
prop-triv-red {P} {app imp (app₂ φ (app₂ (out ψ) out₂))} (app (appr (appl (out ψ→ψ')))) = prop-triv-red ψ→ψ'
prop-triv-red {P} {app imp (app₂ _ (app₂ (out _) out₂))} (app (appr (appr ())))

SR : ∀ {P} {Γ : Context P} {δ ε : Proof P} {φ} → Γ ⊢ δ ∷ φ → δ →〈 β 〉 ε → Γ ⊢ ε ∷ φ
SR var ()
SR (app {ε = ε} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∷ψ) Γ⊢ε∷φ) (redex βI) = 
  subst (λ P₁ → Γ ⊢ δ ⟦ x₀:= ε ⟧ ∷ P₁) 
  (let open Equational-Reasoning (Expression'' P (nonVarKind -Prp)) in
  ∵ rep ψ (λ _ → ↑) ⟦ x₀:= ε ⟧
  ≡ ψ ⟦ idSub ⟧                 [[ sub-comp₂ {E = ψ} ]]
  ≡ ψ                           [ subid ]) 
  (Substitution Γ,φ⊢δ∷ψ (botsub-typed Γ⊢ε∷φ))
SR (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) (app (appl (out δ→δ'))) = app (SR Γ⊢δ∷φ→ψ δ→δ') Γ⊢ε∷φ
SR (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) (app (appr (appl (out ε→ε')))) = app Γ⊢δ∷φ→ψ (SR Γ⊢ε∷φ ε→ε')
SR (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) (app (appr (appr ())))
SR (Λ Γ⊢δ∷φ) (redex ())
SR (Λ Γ⊢δ∷φ) (app (appl (out φ→φ'))) with prop-triv-red φ→φ'
... | ()
SR (Λ Γ⊢δ∷φ) (app (appr (appl (Λ (out δ→δ'))))) = Λ (SR Γ⊢δ∷φ δ→δ')
SR (Λ Γ⊢δ∷φ) (app (appr (appr ())))
\end{code}
We define the sets of \emph{computable} proofs $C_\Gamma(\phi)$ for each context $\Gamma$ and proposition $\phi$ as follows:

\begin{align*}
C_\Gamma(\bot) & = \{ \delta \mid \Gamma \vdash \delta : \bot, \delta \in SN \} \\
C_\Gamma(\phi \rightarrow \psi) & = \{ \delta \mid \Gamma : \delta : \phi \rightarrow \psi, \forall \epsilon \in C_\Gamma(\phi). \delta \epsilon \in C_\Gamma(\psi) \}
\end{align*}

\begin{code}
C : ∀ {P} → Context P → Prp → Proof P → Set
C Γ (app bot out₂) δ = (Γ ⊢ δ ∷ rep ⊥P (λ _ ()) ) ∧ SN β δ
C Γ (app imp (app₂ (out φ) (app₂ (out ψ) out₂))) δ = (Γ ⊢ δ ∷ rep (φ ⇒ ψ) (λ _ ())) ∧ 
  (∀ Q {Δ : Context Q} ρ ε → ρ ∷ Γ ⇒R Δ → C Δ φ ε → C Δ ψ (appP (rep δ ρ) ε))

C-typed : ∀ {P} {Γ : Context P} {φ} {δ} → C Γ φ δ → Γ ⊢ δ ∷ rep φ (λ _ ())
C-typed {φ = app bot out₂} = π₁
C-typed {Γ = Γ} {φ = app imp (app₂ (out φ) (app₂ (out ψ) out₂))} {δ = δ} = λ x → subst (λ P → Γ ⊢ δ ∷ P) {a = rep φ _ ⇒ rep ψ _} {b = rep φ _ ⇒ rep ψ _} 
  (wd2 _⇒_ (rep-wd {E = φ} (λ ())) (rep-wd {E = ψ} (λ ())))
  (π₁ x)

C-rep : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} {φ} {δ} {ρ} → C Γ φ δ → ρ ∷ Γ ⇒R Δ → C Δ φ (rep δ ρ)
C-rep {φ = app bot out₂} (Γ⊢δ∷⊥ , SNδ) ρ∷Γ→Δ = (Weakening Γ⊢δ∷⊥ ρ∷Γ→Δ) , SNrep β-creates-rep SNδ
C-rep {P} {Q} {Γ} {Δ} {app imp (app₂ (out φ) (app₂ (out ψ) out₂))} {δ} {ρ} (Γ⊢δ∷φ⇒ψ , Cδ) ρ∷Γ→Δ = subst (λ x → Δ ⊢ rep δ ρ ∷ x) (wd2 _⇒_ 
  (let open Equational-Reasoning (Expression'' Q (nonVarKind -Prp)) in 
    ∵ rep (rep φ _) ρ
    ≡ rep φ _            [[ rep-comp ]]
    ≡ rep φ _            [ rep-wd (λ ()) ]) 
  (trans (sym rep-comp) (rep-wd (λ ())))) (Weakening Γ⊢δ∷φ⇒ψ ρ∷Γ→Δ) , 
  (λ R σ ε σ∷Δ→Θ ε∈Cφ → subst (C _ ψ) (wd (λ x → appP x ε) rep-comp) 
    (Cδ R (σ •R ρ) ε (•R-typed ρ∷Γ→Δ σ∷Δ→Θ) ε∈Cφ))

C-red : ∀ {P} {Γ : Context P} {φ} {δ} {ε} → C Γ φ δ → δ →〈 β 〉 ε → C Γ φ ε
C-red {φ = app bot out₂} (Γ⊢δ∷⊥ , SNδ) δ→ε = (SR Γ⊢δ∷⊥ δ→ε) , (SNred SNδ (osr-red δ→ε))
C-red {Γ = Γ} {φ = app imp (app₂ (out φ) (app₂ (out ψ) out₂))} {δ = δ} (Γ⊢δ∷φ⇒ψ , Cδ) δ→δ' = (SR (subst (λ x → Γ ⊢ δ ∷ x) 
  (wd2 _⇒_ (rep-wd (λ ())) (rep-wd (λ ()))) 
  Γ⊢δ∷φ⇒ψ) δ→δ') , 
  (λ Q ρ ε ρ∷Γ→Δ ε∈Cφ → C-red {φ = ψ} (Cδ Q ρ ε ρ∷Γ→Δ ε∈Cφ) (app (appl (out (reposr β-respects-rep δ→δ')))))
\end{code}

The \emph{neutral terms} are those that begin with a variable.

\begin{code}
data Neutral {P} : Proof P → Set where
  varNeutral : ∀ x → Neutral (var x)
  appNeutral : ∀ δ ε → Neutral δ → Neutral (appP δ ε)
\end{code}

\begin{lemma}
If $\delta$ is neutral and $\delta \rightarrow_\beta \epsilon$  then $\epsilon$  is neutral.
\end{lemma}

\begin{code}
neutral-red : ∀ {P} {δ ε : Proof P} → Neutral δ → δ →〈 β 〉 ε → Neutral ε
neutral-red (varNeutral _) ()
neutral-red (appNeutral .(app lam (app₂ (out _) (app₂ (Λ (out _)) out₂))) _ ()) (redex βI)
neutral-red (appNeutral _ ε neutralδ) (app (appl (out δ→δ'))) = appNeutral _ ε (neutral-red neutralδ δ→δ')
neutral-red (appNeutral δ _ neutralδ) (app (appr (appl (out ε→ε')))) = appNeutral δ _ neutralδ
neutral-red (appNeutral _ _ _) (app (appr (appr ())))

neutral-rep : ∀ {P} {Q} {δ : Proof P} {ρ : Rep P Q} → Neutral δ → Neutral (rep δ ρ)
neutral-rep {ρ = ρ} (varNeutral x) = varNeutral (ρ -Proof x)
neutral-rep {ρ = ρ} (appNeutral δ ε neutralδ) = appNeutral (rep δ ρ) (rep ε ρ) (neutral-rep neutralδ)
\end{code}

\begin{lemma}
Let $\Gamma \vdash \delta : \phi$.  
If $\delta$ is neutral and, for all $\epsilon$ such that $\delta \rightarrow_\beta \epsilon$, we have $\epsilon \in C_\Gamma(\phi)$, then $\delta \in C_\Gamma(\phi)$.
\end{lemma}

\begin{code}
NeutralC-lm : ∀ {P} {δ ε : Proof P} {X : Proof P → Set} →
  Neutral δ → 
  (∀ δ' → δ →〈 β 〉 δ' → X (appP δ' ε)) →
  (∀ ε' → ε →〈 β 〉 ε' → X (appP δ ε')) →
  ∀ χ → appP δ ε →〈 β 〉 χ → X χ
NeutralC-lm () _ _ ._ (redex βI)
NeutralC-lm _ hyp1 _ .(app app (app₂ (out _) (app₂ (out _) out₂))) (app (appl (out δ→δ'))) = hyp1 _ δ→δ'
NeutralC-lm _ _ hyp2 .(app app (app₂ (out _) (app₂ (out _) out₂))) (app (appr (appl (out ε→ε')))) = hyp2 _ ε→ε'
NeutralC-lm _ _ _ .(app app (app₂ (out _) (app₂ (out _) _))) (app (appr (appr ())))

mutual
  NeutralC : ∀ {P} {Γ : Context P} {δ : Proof P} {φ : Prp} →
    Γ ⊢ δ ∷ (rep φ (λ _ ())) → Neutral δ →
    (∀ ε → δ →〈 β 〉 ε → C Γ φ ε) →
    C Γ φ δ
  NeutralC {P} {Γ} {δ} {app bot out₂} Γ⊢δ∷⊥ Neutralδ hyp = Γ⊢δ∷⊥ , SNI δ (λ ε δ→ε → π₂ (hyp ε δ→ε))
  NeutralC {P} {Γ} {δ} {app imp (app₂ (out φ) (app₂ (out ψ) out₂))} Γ⊢δ∷φ→ψ neutralδ hyp = (subst (λ P₁ → Γ ⊢ δ ∷ P₁) (rep-wd (λ ())) Γ⊢δ∷φ→ψ) , 
    (λ Q ρ ε ρ∷Γ→Δ ε∈Cφ → claim ε (CsubSN {φ = φ} {δ = ε} ε∈Cφ) ρ∷Γ→Δ ε∈Cφ) where
    claim : ∀ {Q} {Δ} {ρ : Rep P Q} ε → SN β ε → ρ ∷ Γ ⇒R Δ → C Δ φ ε → C Δ ψ (appP (rep δ ρ) ε)
    claim {Q} {Δ} {ρ} ε (SNI .ε SNε) ρ∷Γ→Δ ε∈Cφ = NeutralC {Q} {Δ} {appP (rep δ ρ) ε} {ψ} 
      (app (subst (λ P₁ → Δ ⊢ rep δ ρ ∷ P₁) 
      (wd2 _⇒_ 
      (let open Equational-Reasoning (Expression'' Q (nonVarKind -Prp)) in 
        ∵ rep (rep φ _) ρ
        ≡ rep φ _       [[ rep-comp ]]
        ≡ rep φ _       [[ rep-wd (λ ()) ]]) 
      (  (let open Equational-Reasoning (Expression'' Q (nonVarKind -Prp)) in 
        ∵ rep (rep ψ _) ρ
        ≡ rep ψ _       [[ rep-comp ]]
        ≡ rep ψ _       [[ rep-wd (λ ()) ]]) 
        ))
      (Weakening Γ⊢δ∷φ→ψ ρ∷Γ→Δ)) 
      (C-typed {Q} {Δ} {φ} {ε} ε∈Cφ)) 
      (appNeutral (rep δ ρ) ε (neutral-rep neutralδ))
      (NeutralC-lm {X = C Δ ψ} (neutral-rep neutralδ) 
      (λ δ' δ〈ρ〉→δ' → 
      let δ₀ : Proof P
          δ₀ = create-reposr β-creates-rep δ〈ρ〉→δ'
      in let δ→δ₀ : δ →〈 β 〉 δ₀
             δ→δ₀ = red-create-reposr β-creates-rep δ〈ρ〉→δ'
      in let δ₀〈ρ〉≡δ' : rep δ₀ ρ ≡ δ'
             δ₀〈ρ〉≡δ' = rep-create-reposr β-creates-rep δ〈ρ〉→δ'
      in let δ₀∈C[φ⇒ψ] : C Γ (φ ⇒ ψ) δ₀
             δ₀∈C[φ⇒ψ] = hyp δ₀ δ→δ₀
      in let δ'∈C[φ⇒ψ] : C Δ (φ ⇒ ψ) δ'
             δ'∈C[φ⇒ψ] = subst (C Δ (φ ⇒ ψ)) δ₀〈ρ〉≡δ' (C-rep {φ = φ ⇒ ψ} δ₀∈C[φ⇒ψ] ρ∷Γ→Δ)
      in subst (C Δ ψ) (wd (λ x → appP x ε) δ₀〈ρ〉≡δ') (π₂ δ₀∈C[φ⇒ψ] Q ρ ε ρ∷Γ→Δ ε∈Cφ))
      (λ ε' ε→ε' → claim ε' (SNε ε' ε→ε') ρ∷Γ→Δ (C-red {φ = φ} ε∈Cφ ε→ε')))
\end{code}

\begin{lemma}
\[ C_\Gamma(\phi) \subseteq SN \]
\end{lemma}

\begin{code}
  CsubSN : ∀ {P} {Γ : Context P} {φ} {δ} → C Γ φ δ → SN β δ
  CsubSN {P} {Γ} {ToGrammar.app bot ToGrammar.out₂} P₁ = π₂ P₁
  CsubSN {P} {Γ} {app imp (app₂ (out φ) (app₂ (out ψ) out₂))} {δ} P₁ = 
    let φ' : Expression'' P (nonVarKind -Prp)
        φ' = rep φ (λ _ ()) in
    let Γ' : Context (P , -Proof)
        Γ' = _,_ {K = -Proof} Γ φ' in
    SNrep' {P} {P , -Proof} { varKind -Proof} {λ _ → ↑} β-respects-rep 
    (SNoutA 
      (SNsubbodyl (SNsubexp (CsubSN {Γ = Γ'} {φ = ψ} 
      (π₂ P₁ (P , -Proof) (λ _ → ↑) (var x₀) (λ _ → ref) 
        (NeutralC {φ = φ} (subst (λ x → Γ' ⊢ var x₀ ∷ x) (trans (sym rep-comp) (rep-wd (λ ()))) var) 
          (varNeutral x₀) 
          (λ _ ())))))))
--(subst (λ x → (_,_ {K = -Proof} Γ (rep φ _)) ⊢ var x₀ ∷ x) {rep (rep φ _) _} {rep φ _} (trans (sym rep-comp) (rep-wd (λ ()))) (var {P , -Proof} {_,_ {K = -Proof} Γ (rep φ (λ _ ()))} {x₀}))
{-        (π₂ P₁ (P , -Proof) (λ _ → ↑) (var x₀) 
          (↑-typed {Γ = Γ} {φ = rep φ (λ _ ())})
          (NeutralC {φ = φ} 
            (subst (λ x → _ ⊢ var x₀ ∷ x) {!!} var) 
            (varNeutral x₀) 
            (λ _ ())))))))) -}
\end{code}
