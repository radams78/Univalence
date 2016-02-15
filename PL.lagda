\begin{code}
module PL where

open import Prelims
open import Grammar
open import Reduction hiding (Context;typeof;SN;_,_;Reduction)
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

data PLExpKind : Set where
  -Proof : PLExpKind
  -Prp   : PLExpKind

PLVK2EK : PLVarKind → PLExpKind
PLVK2EK -Proof = -Proof

data PLCon : ∀ {K : PLExpKind} → ConstructorKind K → Set where
  app : PLCon (Π₂ (out -Proof) (Π₂ (out -Proof) (out₂ {K = -Proof})))
  lam : PLCon (Π₂ (out -Prp) (Π₂ (Π -Proof (out -Proof)) (out₂ {K = -Proof})))
  bot : PLCon (out₂ {K = -Prp})
  imp : PLCon (Π₂ (out -Prp) (Π₂ (out -Prp) (out₂ {K = -Prp})))

PLparent : PLVarKind → PLExpKind
PLparent -Proof = -Prp

Propositional-Logic : Grammar
Propositional-Logic = record { 
  VarKind = PLVarKind;
  ExpressionKind = PLExpKind; 
  VK2EK = PLVK2EK;
  Constructor = PLCon;
  parent = PLparent}

open Grammar.Grammar Propositional-Logic
open Reduction Propositional-Logic

Prp : Set
Prp = Expression'' ∅ -Prp

⊥P : Prp
⊥P = app bot out₂

_⇒_ : ∀ {P} → Expression'' P -Prp → Expression'' P -Prp → Expression'' P -Prp
φ ⇒ ψ = app imp (app₂ (out φ) (app₂ (out ψ) out₂))

Proof : Alphabet → Set
Proof P = Expression'' P -Proof

appP : ∀ {P} → Expression'' P -Proof → Expression'' P -Proof → Expression'' P -Proof
appP δ ε = app app (app₂ (out δ) (app₂ (out ε) out₂))

ΛP : ∀ {P} → Expression'' P -Prp → Expression'' (P , -Proof) -Proof → Expression'' P -Proof
ΛP φ δ = app lam (app₂ (out φ) (app₂ (Λ (out δ)) out₂))

data β : Reduction where
  βI : ∀ {V} {φ} {δ} {ε} → β {V} app (Grammar.app₂ (Grammar.out (ΛP φ δ)) (Grammar.app₂ (Grammar.out ε) Grammar.out₂)) (δ ⟦ x₀:= ε ⟧)
\end{code}

The rules of deduction of the system are as follows.

\[ \infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald} \]

\[ \infer{\Gamma \vdash \delta \epsilon : \psi}{\Gamma \vdash \delta : \phi \rightarrow \psi}{\Gamma \vdash \epsilon : \phi} \]

\[ \infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \rightarrow \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]

\begin{code}
infix 10 _⊢_∷_
data _⊢_∷_ : ∀ {P} → Context P → Proof P → Expression'' P -Prp → Set where
  var : ∀ {P} {Γ : Context P} {p : Var P -Proof} → Γ ⊢ var p ∷ typeof p Γ
  app : ∀ {P} {Γ : Context P} {δ} {ε} {φ} {ψ} → Γ ⊢ δ ∷ φ ⇒ ψ → Γ ⊢ ε ∷ φ → Γ ⊢ appP δ ε ∷ ψ
  Λ : ∀ {P} {Γ : Context P} {φ} {δ} {ψ} → (Γ , φ) ⊢ δ ∷ ψ 〈 (λ _ → ↑) 〉 → Γ ⊢ ΛP φ δ ∷ φ ⇒ ψ
\end{code}

We define the sets of \emph{computable} proofs $C_\Gamma(\phi)$ for each context $\Gamma$ and proposition $\phi$ as follows:

\begin{align*}
C_\Gamma(\bot) & = \{ \delta \mid \Gamma \vdash \delta : \bot, \delta \in SN \} \\
C_\Gamma(\phi \rightarrow \psi) & = \{ \delta \mid \Gamma : \delta : \phi \rightarrow \psi, \forall \epsilon \in C_\Gamma(\phi). \delta \epsilon \in C_\Gamma(\psi) \}
\end{align*}

\begin{code}
data C : ∀ {P} → Context P → Expression'' P -Prp → Proof P → Set₁ where
  C⊥ : ∀ {Γ} {δ} → Γ ⊢ δ ∷ ⊥P → SN β δ → C Γ ⊥P δ
  C⇒ : ∀ {Γ} {φ} {ψ} {δ} → Γ ⊢ δ ∷ φ ⇒ ψ →
    (∀ ε → C Γ φ ε → C Γ ψ (appP δ ε)) →
    C Γ (φ ⇒ ψ) δ
--  C Γ ⊥P δ = (Γ ⊢ δ ∷ ⊥) ∧ SN δ
--  C Γ (φ ⇒ ψ) δ = (Γ ⊢ δ ∷ φ ⇒ ψ) ∧ (∀ ε → C Γ φ ε → C Γ ψ (app δ ε))
\end{code}

\begin{lemma}
\[ C_\Gamma(\phi) \subseteq SN \]
\end{lemma}

\begin{code}
CsubSN : ∀ {P} {Γ : Context P} {φ} {δ} → C Γ φ δ → SN β δ
CsubSN P = {!!}
\end{code}
