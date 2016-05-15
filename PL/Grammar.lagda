\AgdaHide{
\begin{code}
module PL.Grammar where
open import Data.Empty
open import Prelims
open import Grammar.Taxonomy
open import Grammar.Base
\end{code}
}

\section{Propositional Logic}

\subsection{Grammar}

The syntax of the system called \emph{propositional logic} is given by the following grammar.

\[ \begin{array}{lrcl}
\text{Proof} & \delta & ::= & p \mid \delta \delta \mid \lambda p : \phi . \delta \\
\text{Proposition} & φ & ::= & ⊥ \mid \phi \rightarrow \phi \\
\end{array} \]

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
\end{code}

\AgdaHide{
\begin{code}
close : ∀ {P} → Prp P → Prp ∅
close (app -bot out) = ⊥P
close (app -imp (φ ,, ψ ,, out)) = close φ ⇛ close ψ

close-magic : ∀ {P} {φ : Prp P} → close φ 〈 magic 〉 ≡ φ
close-magic {φ = app -bot out} = refl
close-magic {φ = app -imp (φ ,, ψ ,, out)} = cong₂ _⇛_ close-magic close-magic

close-magic' : ∀ {P} {Q} {φ : Prp P} {σ : Sub P Q} →
  φ ⟦ σ ⟧ ≡ close φ 〈 magic 〉
close-magic' {P} {Q} {φ} {σ} = 
  let open ≡-Reasoning in 
  begin
    φ ⟦ σ ⟧
  ≡⟨⟨ sub-congl (close-magic {φ = φ}) ⟩⟩
    close φ 〈 magic 〉 ⟦ σ ⟧
  ≡⟨⟨ sub-comp₂ (close φ) ⟩⟩
    (close φ) ⟦ σ •₂ magic ⟧
  ≡⟨ sub-congr (close φ) (λ ()) ⟩
    (close φ) ⟦ rep2sub magic ⟧
  ≡⟨⟨ rep-is-sub (close φ) ⟩⟩
    (close φ) 〈 magic 〉
  ∎

close-sub : ∀ {P} {Q} φ {σ : Sub P Q} → close (φ ⟦ σ ⟧) ≡ close φ
close-sub (app -bot out) = refl
close-sub (app -imp (φ ,, ψ ,, out)) = cong₂ _⇛_ (close-sub φ) (close-sub ψ)

close-rep : ∀ {P} {Q} φ {ρ : Rep P Q} → close (φ 〈 ρ 〉) ≡ close φ
close-rep φ {ρ} = let open ≡-Reasoning in
  begin
    close (φ 〈 ρ 〉)
  ≡⟨ cong close (rep-is-sub φ) ⟩
    close (φ ⟦ rep2sub ρ ⟧)
  ≡⟨ close-sub φ ⟩
    close φ
  ∎
\end{code}
}

\begin{code}
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
\end{code}

It is easy to check that $\beta$-reduction respects and creates replacement, and respects substitution.

\begin{code}
β-respects-rep : respects' replacement
\end{code}

\AgdaHide{
\begin{code}
β-respects-rep (βI {δ = δ}) = 
  subst (β -app _) (sym (comp₁-botsub' δ)) βI
\end{code}
}

\begin{code}
β-creates-rep : creates' replacement
\end{code}

\AgdaHide{
\begin{code}
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
}

\begin{code}
β-respects-sub : respects' substitution
\end{code}

\AgdaHide{
\begin{code}
β-respects-sub {σ = σ} (βI {φ} {δ} {ε}) = subst
  (β -app _) (sym (comp-botsub' δ)) βI

prop-not-reduce : ∀ {P} {φ ψ : Prp P} → φ ⇒ ψ → ⊥
prop-not-reduce (redex ())
prop-not-reduce (app {c = -imp} (appl φ⇒ψ)) = prop-not-reduce φ⇒ψ
prop-not-reduce (app {c = -imp} (appr (appl φ⇒ψ))) = prop-not-reduce φ⇒ψ
prop-not-reduce (app {c = -imp} (appr (appr ())))

red-β-redex : ∀ {P} {φ} {δ} {ε} {χ} (S : Proof P → Set) → 
    appP (ΛP φ δ) ε ⇒ χ →
    S (δ ⟦ x₀:= ε ⟧) →
    (∀ δ' → δ ⇒ δ' → S (appP (ΛP φ δ') ε)) →
    (∀ ε' → ε ⇒ ε' → S (appP (ΛP φ δ) ε')) →
    S χ
red-β-redex _ (redex βI) δ[p∶=ε]∈CΓψ _ _ = δ[p∶=ε]∈CΓψ
red-β-redex _ (app (appl (redex ()))) _ _ 
red-β-redex _ (app (appl (app (appl φ⇒φ')))) _ _ = ⊥-elim (prop-not-reduce φ⇒φ')
red-β-redex _ (app (appl (app (appr (appl δ⇒δ'))))) _ hyp1 _ = hyp1 _ δ⇒δ'
red-β-redex _ (app (appl (app (appr (appr ()))))) _ _
red-β-redex _ (app (appr (appl {E' = ε'} ε⇒ε'))) _ _ hyp2 = hyp2 _ ε⇒ε'
red-β-redex _ (app (appr (appr ()))) _ _
\end{code}
}

\subsubsection{Neutral Terms}

The \emph{neutral terms} are the variables and applications.

\begin{code}
data Neutral {P} : Proof P → Set where
  varNeutral : ∀ x → Neutral (var x)
  appNeutral : ∀ δ ε → Neutral (appP δ ε)
  
\end{code}

\begin{lemma}
If $\delta$ is neutral then $\delta \langle \rho \rangle$ is neutral.
\end{lemma}

\begin{code}
neutral-rep : ∀ {P} {Q} {δ : Proof P} {ρ : Rep P Q} → 
  Neutral δ → Neutral (δ 〈 ρ 〉)
\end{code}

\AgdaHide{
\begin{code}
neutral-rep {ρ = ρ} (varNeutral x) = varNeutral (ρ -proof x)
neutral-rep {ρ = ρ} (appNeutral δ ε) = appNeutral (δ 〈 ρ 〉) (ε 〈 ρ 〉)

NeutralC-lm : ∀ {P} {δ ε : Proof P} {X : Proof P → Set} →
  Neutral δ → 
  (∀ δ' → δ ⇒ δ' → X (appP δ' ε)) →
  (∀ ε' → ε ⇒ ε' → X (appP δ ε')) →
  ∀ χ → appP δ ε ⇒ χ → X χ
NeutralC-lm () _ _ ._ (redex βI)
NeutralC-lm _ hyp1 _ .(app -app (_,,_ _ (_,,_ _ out))) (app (appl δ→δ')) = hyp1 _ δ→δ'
NeutralC-lm _ _ hyp2 .(app -app (_,,_ _ (_,,_ _ out))) (app (appr (appl ε→ε'))) = hyp2 _ ε→ε'
NeutralC-lm _ _ _ .(app -app (_,,_ _ (_,,_ _ _))) (app (appr (appr ())))
\end{code}
}

