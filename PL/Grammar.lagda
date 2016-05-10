\AgdaHide{
\begin{code}
module PL.Grammar where
open import Prelims
open import Grammar.Taxonomy
open import Grammar.Base
\end{code}
}

\section{Propositional Logic}

\subsection{Grammar}

The syntax of the system called \emph{propositional logic} is given by the following grammar.

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
  -proof : PLVarKind

data PLNonVarKind : Set where
  -prp   : PLNonVarKind

PLtaxonomy : Taxonomy
PLtaxonomy = record { 
  VarKind = PLVarKind; 
  NonVarKind = PLNonVarKind }

module PLgrammar where
  open Taxonomy PLtaxonomy

  proof = varKind -proof
  prp = nonVarKind -prp

  data PLCon : ∀ {K : ExpressionKind} → Kind (-Constructor K) → Set where
    -app : PLCon (Π [] proof (Π [] proof (out proof)))
    -lam : PLCon (Π [] prp (Π [ -proof ] proof (out proof)))
    -bot : PLCon (out prp)
    -imp : PLCon (Π [] prp (Π [] prp (out prp)))

  PLparent : VarKind → ExpressionKind
  PLparent -proof = prp

open PLgrammar

Propositional-Logic : Grammar
Propositional-Logic = record { 
  taxonomy = PLtaxonomy; 
  isGrammar = record { 
    Constructor = PLCon; 
    parent = PLparent } }

open import Grammar Propositional-Logic

Prp : Alphabet → Set
Prp P = Expression P prp

⊥P : ∀ {P} → Prp P
⊥P = app -bot out

_⇛_ : ∀ {P} → Prp P → Prp P → Prp P
φ ⇛ ψ = app -imp (φ ,, ψ ,, out)

close : ∀ {P} → Prp P → Prp ∅
close (app -bot out) = ⊥P
close (app -imp (φ ,, ψ ,, out)) = close φ ⇛ close ψ

close-magic : ∀ {P} {φ : Prp P} → close φ 〈 magic 〉 ≡ φ
close-magic {φ = app -bot out} = refl
close-magic {φ = app -imp (φ ,, ψ ,, out)} = cong₂ _⇛_ (close-magic {φ = φ}) (close-magic {φ = ψ})

close-magic' : ∀ {P} {Q} {φ : Prp P} {σ : Sub P Q} →
  φ ⟦ σ ⟧ ≡ close φ 〈 magic 〉
close-magic' {P} {Q} {φ} {σ} = 
  let open ≡-Reasoning in 
  begin
    φ ⟦ σ ⟧
  ≡⟨⟨ cong (λ M → M ⟦ σ ⟧) (close-magic {φ = φ}) ⟩⟩
    close φ 〈 magic 〉 ⟦ σ ⟧
  ≡⟨⟨ sub-comp₂ (close φ) ⟩⟩
    (close φ) ⟦ σ •₂ magic ⟧
  ≡⟨ sub-cong (close φ) (λ ()) ⟩
    (close φ) ⟦ rep2sub magic ⟧
  ≡⟨⟨ rep-is-sub (close φ) ⟩⟩
    (close φ) 〈 magic 〉
  ∎

_,P_ : ∀ {P} → Context P → Prp P → Context (P , -proof)
_,P_ = _,_

Proof : Alphabet → Set
Proof P = Expression P proof

appP : ∀ {P} → Proof P → Proof P → Proof P
appP δ ε = app -app (δ ,, ε ,, out)

ΛP : ∀ {P} → Prp P → Proof (P , -proof) → Proof P
ΛP φ δ = app -lam (φ ,, δ ,, out)
\end{code}

\subsubsection{$\beta$-reduction}

The relation of \emph{$\beta$-reduction} is defined by: $(\lambda x \delta) \epsilon
\rightarrow_\beta \delta [ x := \epsilon ]$.

\begin{code}
data β {V} : ∀ {K} {C : Kind (-Constructor K)} → 
  Constructor C → Subexpression V (-Constructor K) C → 
  Expression V K → Set where
  βI : ∀ {φ} {δ} {ε} → β -app (ΛP φ δ ,, ε ,, out) (δ ⟦ x₀:= ε ⟧)

open import Reduction Propositional-Logic β

β-respects-rep : respects' replacement
β-respects-rep (βI {δ = δ}) = 
  subst (β -app _) (sym (comp₁-botsub' δ)) βI

β-creates-rep : creates' replacement
β-creates-rep {c = -app} (var _ ,, _) ()
β-creates-rep {c = -app} (app -app _ ,, _) ()
β-creates-rep {c = -app} 
  (app -lam (_ ,, δ ,, out) ,, (ε ,, out)) βI = record { 
  created = δ ⟦ x₀:= ε ⟧ ; 
  red-created = βI ; 
  ap-created = comp₁-botsub' δ }
β-creates-rep {c = -lam} _ ()
β-creates-rep {c = -bot} _ ()
β-creates-rep {c = -imp} _ ()
\end{code}

\subsubsection{Neutral Terms}

The \emph{neutral terms} are the variables and applications.

\begin{code}
data Neutral {P} : Proof P → Set where
  varNeutral : ∀ x → Neutral (var x)
  appNeutral : ∀ δ ε → Neutral (appP δ ε)
  
\end{code}

\begin{lemma}$ $
\begin{enumerate}
\item
If $\delta$ is neutral and $\delta \rightarrow_\beta \epsilon$  then $\epsilon$  is neutral.
\item
If $\delta$ is neutral then $\delta \langle \rho \rangle$ is neutral.
\item
If $\delta \epsilon$ is neutral and $\delta \epsilon \rightarrow_\beta \chi$, then either $\chi \equiv \delta' \epsilon$ where $\delta \rightarrow_\beta \delta'$,
or $\chi \equiv \delta \epsilon'$ where $\epsilon \rightarrow_\beta \epsilon'$.
\end{enumerate}
\end{lemma}

\begin{code}
--neutral-red : ∀ {P} {δ ε : Proof P} → Neutral δ → δ ⇒ ε → Neutral ε
\end{code}

\AgdaHide{
\begin{code}
{-neutral-red (varNeutral _) ()
neutral-red (appNeutral .(app -lam (_,,_ _ (_,,_ _ out))) _) (redex βI)
neutral-red (appNeutral _ ε neutralδ) (app (appl δ→δ')) = appNeutral _ ε (neutral-red neutralδ δ→δ')
neutral-red (appNeutral δ _ neutralδ) (app (appr (appl ε→ε'))) = appNeutral δ _ neutralδ
neutral-red (appNeutral _ _ _) (app (appr (appr ())))-}
\end{code}
}

\begin{code}
neutral-rep : ∀ {P} {Q} {δ : Proof P} {ρ : Rep P Q} → Neutral δ → Neutral (δ 〈 ρ 〉)
\end{code}

\AgdaHide{
\begin{code}
neutral-rep {ρ = ρ} (varNeutral x) = varNeutral (ρ -proof x)
neutral-rep {ρ = ρ} (appNeutral δ ε) = appNeutral (δ 〈 ρ 〉) (ε 〈 ρ 〉)
\end{code}
}

\begin{code}
NeutralC-lm : ∀ {P} {δ ε : Proof P} {X : Proof P → Set} →
  Neutral δ → 
  (∀ δ' → δ ⇒ δ' → X (appP δ' ε)) →
  (∀ ε' → ε ⇒ ε' → X (appP δ ε')) →
  ∀ χ → appP δ ε ⇒ χ → X χ
\end{code}

\AgdaHide{
\begin{code}
NeutralC-lm () _ _ ._ (redex βI)
NeutralC-lm _ hyp1 _ .(app -app (_,,_ _ (_,,_ _ out))) (app (appl δ→δ')) = hyp1 _ δ→δ'
NeutralC-lm _ _ hyp2 .(app -app (_,,_ _ (_,,_ _ out))) (app (appr (appl ε→ε'))) = hyp2 _ ε→ε'
NeutralC-lm _ _ _ .(app -app (_,,_ _ (_,,_ _ _))) (app (appr (appr ())))
\end{code}
}

