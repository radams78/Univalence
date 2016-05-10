\AgdaHide{
\begin{code}
module PL where

open import Function
open import Data.Empty
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.List
open import Prelims
open import Grammar.Taxonomy
open import Grammar.Base
\end{code}
}

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

_,P_ : ∀ {P} → Context P → Prp P → Context (P , -proof)
_,P_ = _,_

Proof : Alphabet → Set
Proof P = Expression P proof

appP : ∀ {P} → Proof P → Proof P → Proof P
appP δ ε = app -app (δ ,, ε ,, out)

ΛP : ∀ {P} → Prp P → Proof (P , -proof) → Proof P
ΛP φ δ = app -lam (φ ,, δ ,, out)
\end{code}

The relation of \emph{$\beta$-reduction} is defined by: $(\lambda x \delta) \epsilon
\rightarrow_\beta \delta [ x := \epsilon ]$.

\begin{code}
data β {V} : ∀ {K} {C : Kind (-Constructor K)} → 
  Constructor C → Subexpression V (-Constructor K) C → 
  Expression V K → Set where
  βI : ∀ {φ} {δ} {ε} → β {V} -app (ΛP φ δ ,, ε ,, out) (δ ⟦ x₀:= ε ⟧)

open import Reduction Propositional-Logic β
open import Reduction.SN Propositional-Logic β

β-respects-rep : Respects-Creates.respects' replacement
β-respects-rep {U} {V} {σ = ρ} (βI {φ} {δ} {ε}) = subst (β -app _) (sym (comp₁-botsub' δ)) βI

β-creates-rep : Respects-Creates.creates' replacement
β-creates-rep {c = -app} (var _ ,, _) ()
β-creates-rep {c = -app} (app -app _ ,, _) ()
β-creates-rep {c = -app} (app -lam (A ,, δ ,, out) ,, (ε ,, out)) {σ = σ} βI = record { 
  created = δ ⟦ x₀:= ε ⟧ ; 
  red-created = βI ; 
  ap-created = comp₁-botsub' δ }
β-creates-rep {c = -lam} _ ()
β-creates-rep {c = -bot} _ ()
β-creates-rep {c = -imp} _ ()
\end{code}

The rules of deduction of the system are as follows.

\[ \infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald} \]

\[ \infer{\Gamma \vdash \delta \epsilon : \psi}{\Gamma \vdash \delta : \phi \rightarrow \psi}{\Gamma \vdash \epsilon : \phi} \]

\[ \infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \rightarrow \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]

\begin{code}
infix 10 _⊢_∶_
data _⊢_∶_ : ∀ {P} → Context P → Proof P → Prp P → Set where
  var : ∀ {P} {Γ : Context P} {p : Var P -proof} → Γ ⊢ var p ∶ typeof p Γ
  app : ∀ {P} {Γ : Context P} {δ} {ε} {φ} {ψ} → Γ ⊢ δ ∶ φ ⇛ ψ → Γ ⊢ ε ∶ φ → Γ ⊢ appP δ ε ∶ ψ
  Λ : ∀ {P} {Γ : Context P} {φ} {δ} {ψ} → (_,_ {K = -proof} Γ φ) ⊢ δ ∶ ψ 〈 upRep 〉 → Γ ⊢ ΛP φ δ ∶ φ ⇛ ψ

_∶_⇒R_ : ∀ {P} {Q} → Rep P Q → Context P → Context Q → Set
ρ ∶ Γ ⇒R Δ = ∀ x → typeof {K = -proof} (ρ _ x) Δ ≡ typeof x Γ 〈 ρ 〉

↑-typed : ∀ {P} {Γ : Context P} {φ : Prp P} → upRep ∶ Γ ⇒R (Γ ,P φ)
↑-typed {P} {Γ} {φ} x = refl

Rep↑-typed : ∀ {P} {Q} {ρ} {Γ : Context P} {Δ : Context Q} {φ : Prp P} → ρ ∶ Γ ⇒R Δ → 
  Rep↑ -proof ρ ∶ (Γ ,P φ) ⇒R (Δ ,P φ 〈 ρ 〉)
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

The replacements between contexts are closed under composition.

\begin{code}
•R-typed : ∀ {P} {Q} {R} {σ : Rep Q R} {ρ : Rep P Q} {Γ} {Δ} {Θ} → ρ ∶ Γ ⇒R Δ → σ ∶ Δ ⇒R Θ → (σ •R ρ) ∶ Γ ⇒R Θ
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

Weakening Lemma

\begin{code}
Weakening : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} {ρ} {δ} {φ} → 
  Γ ⊢ δ ∶ φ → ρ ∶ Γ ⇒R Δ → Δ ⊢ δ 〈 ρ 〉 ∶ φ 〈 ρ 〉
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

A \emph{substitution} $\sigma$ from a context $\Gamma$ to a context $\Delta$, $\sigma : \Gamma \rightarrow \Delta$,  is a substitution $\sigma$ on the syntax such that,
for every $x : \phi$ in $\Gamma$, we have $\Delta \vdash \sigma(x) : \phi$.

\begin{code}
_∶_⇒_ : ∀ {P} {Q} → Sub P Q → Context P → Context Q → Set
σ ∶ Γ ⇒ Δ = ∀ x → Δ ⊢ σ _ x ∶ typeof x Γ ⟦ σ ⟧

Sub↑-typed : ∀ {P} {Q} {σ} {Γ : Context P} {Δ : Context Q} {φ : Prp P} → σ ∶ Γ ⇒ Δ → Sub↑ -proof σ ∶ (Γ ,P φ) ⇒ (Δ ,P φ ⟦ σ ⟧)
Sub↑-typed {P} {Q} {σ} {Γ} {Δ} {φ} σ∶Γ→Δ x₀ = subst (λ T → (Δ ,P φ ⟦ σ ⟧) ⊢ var x₀ ∶ T) 
  (sym (liftOp-up-mixed' COMP₂ COMP₁ (λ {_} {_} {_} {_} {E} → sym (up-is-up' {E = E})) {E = φ})) 
  (var {p = x₀})
Sub↑-typed {Q = Q} {σ = σ} {Γ = Γ} {Δ = Δ} {φ = φ} σ∶Γ→Δ (↑ x) = 
  subst
  (λ P → (Δ ,P φ ⟦ σ ⟧) ⊢ Sub↑ -proof σ -proof (↑ x) ∶ P)
  (sym (liftOp-up-mixed' COMP₂ COMP₁ (λ {_} {_} {_} {_} {E} → sym (up-is-up' {E = E})) {E = typeof x Γ}))
  (Weakening (σ∶Γ→Δ x) (↑-typed {φ = φ ⟦ σ ⟧}))

botsub-typed : ∀ {P} {Γ : Context P} {φ : Expression ( P) prp} {δ} →
  Γ ⊢ δ ∶ φ → x₀:= δ ∶ (Γ ,P φ) ⇒ Γ
botsub-typed {P} {Γ} {φ} {δ} Γ⊢δ∶φ x₀ = subst (λ P₁ → Γ ⊢ δ ∶ P₁) 
  (sym botsub-upRep) Γ⊢δ∶φ
botsub-typed {P} {Γ} {φ} {δ} _ (↑ x) = subst (λ P₁ → Γ ⊢ var x ∶ P₁) 
  (sym botsub-upRep) var
\end{code}

Substitution Lemma

\begin{code}
Substitution : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} {δ} {φ} {σ} → Γ ⊢ δ ∶ φ → σ ∶ Γ ⇒ Δ → Δ ⊢ δ ⟦ σ ⟧ ∶ φ ⟦ σ ⟧
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
\end{code}

Subject Reduction

\begin{code}
prop-triv-red : ∀ {P} {φ ψ : Expression P prp} → φ ⇒ ψ → ⊥
prop-triv-red {_} {app -bot out} (redex ())
prop-triv-red {P} {app -bot out} (app ())
prop-triv-red {P} {app -imp (_,,_ _ (_,,_ _ out))} (redex ())
prop-triv-red {P} {app -imp (_,,_ φ (_,,_ ψ out))} (app (appl φ→φ')) = prop-triv-red {P} φ→φ'
prop-triv-red {P} {app -imp (_,,_ φ (_,,_ ψ out))} (app (appr (appl ψ→ψ'))) = prop-triv-red {P} ψ→ψ'
prop-triv-red {P} {app -imp (_,,_ _ (_,,_ _ out))} (app (appr (appr ())))

SR : ∀ {P} {Γ : Context P} {δ ε : Proof ( P)} {φ} → Γ ⊢ δ ∶ φ → δ ⇒ ε → Γ ⊢ ε ∶ φ
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
We define the sets of \emph{computable} proofs $C_\Gamma(\phi)$ for each context $\Gamma$ and proposition $\phi$ as follows:

\begin{align*}
C_\Gamma(\bot) & = \{ \delta \mid \Gamma \vdash \delta : \bot, \delta \in SN \} \\
C_\Gamma(\phi \rightarrow \psi) & = \{ \delta \mid \Gamma : \delta : \phi \rightarrow \psi, \forall \epsilon \in C_\Gamma(\phi). \delta \epsilon \in C_\Gamma(\psi) \}
\end{align*}

\begin{code}
C : ∀ {P} → Context P → Prp ∅ → Proof ( P) → Set
C Γ (app -bot out) δ = (Γ ⊢ δ ∶ ⊥P 〈 magic 〉 ) × SN δ
C Γ (app -imp (_,,_ φ (_,,_ ψ out))) δ = (Γ ⊢ δ ∶ (φ ⇛ ψ) 〈 magic 〉) × 
  (∀ Q {Δ : Context Q} ρ ε → ρ ∶ Γ ⇒R Δ → C Δ φ ε → C Δ ψ (appP (δ 〈 ρ 〉) ε))

C-typed : ∀ {P} {Γ : Context P} {φ} {δ} → C Γ φ δ → Γ ⊢ δ ∶ φ 〈 magic 〉
C-typed {φ = app -bot out} = proj₁
C-typed {φ = app -imp (_ ,, _ ,, out)} = proj₁

C-rep : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} {φ} {δ} {ρ} → C Γ φ δ → ρ ∶ Γ ⇒R Δ → C Δ φ (δ 〈 ρ 〉)
C-rep {φ = app -bot out} (Γ⊢δ∶x₀ , SNδ) ρ∶Γ→Δ = (Weakening Γ⊢δ∶x₀ ρ∶Γ→Δ) , SNap β-creates-rep SNδ
C-rep {P} {Q} {Γ} {Δ} {app -imp (φ ,, ψ ,, out)} {δ} {ρ} (Γ⊢δ∶φ⇒ψ , Cδ) ρ∶Γ→Δ = (subst 
  (λ x → Δ ⊢ δ 〈 ρ 〉 ∶ x) 
  (magic-unique' (φ ⇛ ψ))
  (Weakening Γ⊢δ∶φ⇒ψ ρ∶Γ→Δ)) , (λ R {Θ} σ ε σ∶Δ→Θ ε∈CΘ → subst (C Θ ψ) 
    (cong (λ x → appP x ε) (rep-comp δ))
    (Cδ R (σ •R ρ) ε (•R-typed {σ = σ} {ρ = ρ} ρ∶Γ→Δ σ∶Δ→Θ) ε∈CΘ))

C-red : ∀ {P} {Γ : Context P} {φ} {δ} {ε} → C Γ φ δ → δ ⇒ ε → C Γ φ ε
C-red {φ = app -bot out} (Γ⊢δ∶x₀ , SNδ) δ→ε = (SR Γ⊢δ∶x₀ δ→ε) , (SNred SNδ (osr-red δ→ε))
C-red {Γ = Γ} {φ = app -imp (_,,_ φ (_,,_ ψ out))} {δ = δ} (Γ⊢δ∶φ⇒ψ , Cδ) δ→δ' = SR Γ⊢δ∶φ⇒ψ δ→δ' , 
  (λ Q ρ ε ρ∶Γ→Δ ε∈Cφ → C-red {φ = ψ} (Cδ Q ρ ε ρ∶Γ→Δ ε∈Cφ) (app (appl (Respects-Creates.respects-osr replacement β-respects-rep δ→δ'))))
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
neutral-red : ∀ {P} {δ ε : Proof P} → Neutral δ → δ ⇒ ε → Neutral ε
neutral-red (varNeutral _) ()
neutral-red (appNeutral .(app -lam (_,,_ _ (_,,_ _ out))) _ ()) (redex βI)
neutral-red (appNeutral _ ε neutralδ) (app (appl δ→δ')) = appNeutral _ ε (neutral-red neutralδ δ→δ')
neutral-red (appNeutral δ _ neutralδ) (app (appr (appl ε→ε'))) = appNeutral δ _ neutralδ
neutral-red (appNeutral _ _ _) (app (appr (appr ())))

neutral-rep : ∀ {P} {Q} {δ : Proof P} {ρ : Rep P Q} → Neutral δ → Neutral (δ 〈 ρ 〉)
neutral-rep {ρ = ρ} (varNeutral x) = varNeutral (ρ -proof x)
neutral-rep {ρ = ρ} (appNeutral δ ε neutralδ) = appNeutral (δ 〈 ρ 〉) (ε 〈 ρ 〉) (neutral-rep neutralδ)
\end{code}

\begin{lemma}
Let $\Gamma \vdash \delta : \phi$.  
If $\delta$ is neutral and, for all $\epsilon$ such that $\delta \rightarrow_\beta \epsilon$, we have $\epsilon \in C_\Gamma(\phi)$, then $\delta \in C_\Gamma(\phi)$.
\end{lemma}

\begin{code}
NeutralC-lm : ∀ {P} {δ ε : Proof P} {X : Proof P → Set} →
  Neutral δ → 
  (∀ δ' → δ ⇒ δ' → X (appP δ' ε)) →
  (∀ ε' → ε ⇒ ε' → X (appP δ ε')) →
  ∀ χ → appP δ ε ⇒ χ → X χ
NeutralC-lm () _ _ ._ (redex βI)
NeutralC-lm _ hyp1 _ .(app -app (_,,_ _ (_,,_ _ out))) (app (appl δ→δ')) = hyp1 _ δ→δ'
NeutralC-lm _ _ hyp2 .(app -app (_,,_ _ (_,,_ _ out))) (app (appr (appl ε→ε'))) = hyp2 _ ε→ε'
NeutralC-lm _ _ _ .(app -app (_,,_ _ (_,,_ _ _))) (app (appr (appr ())))

mutual
  NeutralC : ∀ {P} {Γ : Context P} {δ : Proof ( P)} {φ : Prp ∅} →
    Γ ⊢ δ ∶ φ 〈 magic 〉 → Neutral δ →
    (∀ ε → δ ⇒ ε → C Γ φ ε) →
    C Γ φ δ
  NeutralC {P} {Γ} {δ} {app -bot out} Γ⊢δ∶x₀ Neutralδ hyp = Γ⊢δ∶x₀ , SNI δ (λ ε δ→ε → proj₂ (hyp ε δ→ε))
  NeutralC {P} {Γ} {δ} {app -imp (_,,_ φ (_,,_ ψ out))} Γ⊢δ∶φ→ψ neutralδ hyp = Γ⊢δ∶φ→ψ , 
    (λ Q ρ ε ρ∶Γ→Δ ε∈Cφ → claim ε (CsubSN {φ = φ} {δ = ε} ε∈Cφ) ρ∶Γ→Δ ε∈Cφ) where
    claim : ∀ {Q} {Δ} {ρ : Rep P Q} ε → SN ε → ρ ∶ Γ ⇒R Δ → C Δ φ ε → C Δ ψ (appP (δ 〈  ρ 〉) ε)
    claim {Q} {Δ} {ρ} ε (SNI .ε SNε) ρ∶Γ→Δ ε∈Cφ = NeutralC {Q} {Δ} {appP (δ 〈  ρ 〉) ε} {ψ} 
      (app (subst (λ P₁ → Δ ⊢ δ 〈 ρ 〉 ∶ P₁) 
      (magic-unique' (φ ⇛ ψ))
      (Weakening Γ⊢δ∶φ→ψ ρ∶Γ→Δ)) 
      (C-typed {Q} {Δ} {φ} {ε} ε∈Cφ)) 
      (appNeutral (δ 〈  ρ 〉) ε (neutral-rep neutralδ))
      (NeutralC-lm {X = C Δ ψ} (neutral-rep neutralδ) 
      (λ δ' δ〈ρ〉→δ' → 
        let δ-creation = create-osr β-creates-rep δ δ〈ρ〉→δ' in 
        let open Respects-Creates.creation δ-creation renaming (created to δ₀;red-created to δ⇒δ₀;ap-created to δ₀〈ρ〉≡δ') in
        let δ₀∈C[φ⇒ψ] : C Γ (φ ⇛ ψ) δ₀
            δ₀∈C[φ⇒ψ] = hyp δ₀ δ⇒δ₀
        in let δ'∈C[φ⇒ψ] : C Δ (φ ⇛ ψ) δ'
               δ'∈C[φ⇒ψ] = subst (C Δ (φ ⇛ ψ)) δ₀〈ρ〉≡δ' (C-rep {φ = φ ⇛ ψ} δ₀∈C[φ⇒ψ] ρ∶Γ→Δ)
        in subst (C Δ ψ) (cong (λ x → appP x ε) δ₀〈ρ〉≡δ') (proj₂ δ₀∈C[φ⇒ψ] Q ρ ε ρ∶Γ→Δ ε∈Cφ))
      (λ ε' ε→ε' → claim ε' (SNε ε' ε→ε') ρ∶Γ→Δ (C-red {φ = φ} ε∈Cφ ε→ε')))
\end{code}

\begin{lemma}
\[ C_\Gamma(\phi) \subseteq SN \]
\end{lemma}

\begin{code}
  CsubSN : ∀ {P} {Γ : Context P} {φ} {δ} → C Γ φ δ → SN δ
  CsubSN {P} {Γ} {app -bot out} = proj₂
  CsubSN {P} {Γ} {app -imp (φ ,, ψ ,, out)} {δ} P₁ = 
    SNap' {replacement} {P} {P , -proof} {E = δ} {σ = upRep} β-respects-rep
      (SNsubbodyl (SNsubexp (CsubSN {Γ = Γ ,P φ 〈 magic 〉} {φ = ψ} 
      (proj₂ P₁ (P , -proof) upRep (var x₀) (λ _ → refl)
      (NeutralC {φ = φ} 
        (subst (λ x → (Γ ,P φ 〈 magic 〉) ⊢ var x₀ ∶ x) 
          (magic-unique' φ) var) 
        (varNeutral x₀) 
        (λ _ ()))))))
\end{code}
