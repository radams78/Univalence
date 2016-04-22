\begin{code}
module PL where

open import Function
open import Data.Empty
open import Data.Product
open import Data.Nat
open import Data.Fin
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

  data PLCon : ∀ {K : ExpressionKind} → Kind (-Constructor K) → Set where
    app : PLCon (Π₂ (out (varKind -Proof)) (Π₂ (out (varKind -Proof)) (out₂ {K = varKind -Proof})))
    lam : PLCon (Π₂ (out (nonVarKind -Prp)) (Π₂ (Π -Proof (out (varKind -Proof))) (out₂ {K = varKind -Proof})))
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

Prp : Set
Prp = Expression ∅ (nonVarKind -Prp)

⊥P : Prp
⊥P = app bot out₂

_⇛_ : ∀ {P} → Expression P (nonVarKind -Prp) → Expression P (nonVarKind -Prp) → Expression P (nonVarKind -Prp)
φ ⇛ ψ = app imp (app₂ φ (app₂ ψ out₂))

Proof : Alphabet → Set
Proof P = Expression P (varKind -Proof)

appP : ∀ {P} → Expression P (varKind -Proof) → Expression P (varKind -Proof) → Expression P (varKind -Proof)
appP δ ε = app app (app₂ δ (app₂ ε out₂))

ΛP : ∀ {P} → Expression P (nonVarKind -Prp) → Expression (P , -Proof) (varKind -Proof) → Expression P (varKind -Proof)
ΛP φ δ = app lam (app₂ φ (app₂ δ out₂))

data β : ∀ {V} {K} {C : Kind (-Constructor K)} → Constructor C → Subexpression V (-Constructor K) C → Expression V K → Set where
  βI : ∀ {V} {φ} {δ} {ε} → β {V} app (app₂ (ΛP φ δ) (app₂ ε out₂)) (δ ⟦ x₀:= ε ⟧)

open Reduction Propositional-Logic β

β-respects-rep : Respects-Creates.respects' replacement
β-respects-rep {U} {V} {σ = ρ} (βI .{U} {φ} {δ} {ε}) = subst (β app _) 
  (let open ≡-Reasoning {A = Expression V (varKind -Proof)} in
  begin 
    δ 〈 Rep↑ ρ 〉 ⟦ x₀:= (ε 〈 ρ 〉) ⟧
  ≡⟨⟨ sub-comp₂ {E = δ} ⟩⟩
    δ ⟦ x₀:= (ε 〈 ρ 〉) •₂ Rep↑ ρ ⟧ 
  ≡⟨⟨ sub-cong {E = δ} comp₁-botsub ⟩⟩ 
    δ ⟦ ρ •₁ x₀:= ε ⟧ 
  ≡⟨ sub-comp₁ {E = δ} ⟩
    δ ⟦ x₀:= ε ⟧ 〈 ρ 〉 
  ∎) 
  βI

β-creates-rep : Respects-Creates.creates' replacement
β-creates-rep = record { 
  created = λ {U} {V} {K} {C} {c} {EE} {F} {ρ} → created {U} {V} {K} {C} {c} {EE} {F} {ρ};
  red-created = λ {U} {V} {K} {C} {c} {EE} {F} {ρ} → red-created {U} {V} {K} {C} {c} {EE} {F} {ρ};
  rep-created = λ {U} {V} {K} {C} {c} {EE} {F} {ρ} → rep-created {U} {V} {K} {C} {c} {EE} {F} {ρ} } where
  created : ∀ {U V : Alphabet} {K} {C} {c : PLCon C} {EE : Subexpression U (-Constructor K) C} {F} {ρ} → β {V} c (EE 〈 ρ 〉) F → Expression U K
  created {c = app} {EE = app₂ (var _) _} ()
  created {c = app} {EE = app₂ (app app _) _} ()
  created {c = app} {EE = app₂ (app lam (app₂ _ (app₂ δ out₂))) (app₂ ε out₂)} βI = δ ⟦ x₀:= ε ⟧
  created {c = lam} ()
  created {c = bot} ()
  created {c = imp} ()
  red-created : ∀ {U} {V} {K} {C} {c : PLCon C} {EE : Subexpression U (-Constructor K) C} {F} {ρ : Rep U V} (δ : β c (EE 〈 ρ 〉) F) → β {U} c EE (created {U} {V} {K} {C} {c} {EE} {F} {ρ} δ)
  red-created {c = app} {EE = app₂ (var _) _} ()
  red-created {c = app} {EE = app₂ (app app _) _} ()
  red-created {c = app} {EE = app₂ (app lam (app₂ φ (app₂ δ out₂))) (app₂ ε out₂)} βI = βI
  red-created {c = lam} ()
  red-created {c = bot} ()
  red-created {c = imp} ()
  rep-created : ∀ {U} {V} {K} {C} {c : PLCon C} {EE : Subexpression U (-Constructor K) C} {F} {ρ} δ → created {U} {V} {K} {C} {c} {EE} {F} {ρ} δ 〈 ρ 〉 ≡ F
  rep-created {c = app} {EE = app₂ (var _) _} ()
  rep-created {c = app} {EE = app₂ (app app _) _} ()
  rep-created {c = app} {EE = app₂ (app lam (app₂ φ (app₂ δ out₂))) (app₂ ε out₂)} {ρ = ρ} βI = let open Equational-Reasoning (Expression _ (varKind -Proof)) in 
    ∵ δ ⟦ x₀:= ε ⟧ 〈 ρ 〉
    ≡ δ ⟦ ρ •₁ x₀:= ε ⟧                 [[ sub-comp₁ {E = δ} ]]
    ≡ δ ⟦ x₀:= (ε 〈 ρ 〉) •₂ Rep↑ ρ ⟧    [ sub-wd {E = δ} comp₁-botsub ]
    ≡ δ 〈 Rep↑ ρ 〉 ⟦ x₀:= (ε 〈 ρ 〉) ⟧ [ sub-comp₂ {E = δ} ]
  rep-created {c = lam} ()
  rep-created {c = bot} ()
  rep-created {c = imp} ()
\end{code}

The rules of deduction of the system are as follows.

\[ \infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald} \]

\[ \infer{\Gamma \vdash \delta \epsilon : \psi}{\Gamma \vdash \delta : \phi \rightarrow \psi}{\Gamma \vdash \epsilon : \phi} \]

\[ \infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \rightarrow \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]

\begin{code}
PContext : ℕ → Set
PContext P = Context' ∅ -Proof P

Palphabet : ℕ → Alphabet
Palphabet P = extend ∅ -Proof P

Palphabet-faithful : ∀ {P} {Q} {ρ σ : Rep (Palphabet P) (Palphabet Q)} → (∀ x → ρ -Proof (embedr {∅} { -Proof} {P} x) ≡ σ -Proof (embedr x)) → ρ ∼R σ
Palphabet-faithful {∅} _ ()
Palphabet-faithful {suc _} ρ-is-σ x₀ = cong var (ρ-is-σ zero)
Palphabet-faithful {suc _} {Q} {ρ} {σ} ρ-is-σ (↑ x) = Palphabet-faithful {Q = Q} {ρ = ρ •R (λ _ → ↑)} {σ = σ •R (λ _ → ↑)} (λ y → ρ-is-σ (↑ y)) x

infix 10 _⊢_∷_
data _⊢_∷_ : ∀ {P} → PContext P → Proof (Palphabet P) → Expression (Palphabet P) (nonVarKind -Prp) → Set where
  var : ∀ {P} {Γ : PContext P} {p : Fin P} → Γ ⊢ var (embedr p) ∷ typeof' p Γ
  app : ∀ {P} {Γ : PContext P} {δ} {ε} {φ} {ψ} → Γ ⊢ δ ∷ φ ⇒ ψ → Γ ⊢ ε ∷ φ → Γ ⊢ appP δ ε ∷ ψ
  Λ : ∀ {P} {Γ : PContext P} {φ} {δ} {ψ} → (_,_ {K = -Proof} Γ φ) ⊢ δ ∷ liftE ψ → Γ ⊢ ΛP φ δ ∷ φ ⇒ ψ
\end{code}

A \emph{replacement} $\rho$ from a context $\Gamma$ to a context $\Delta$, $\rho : \Gamma \rightarrow \Delta$, is a replacement on the syntax such that,
for every $x : \phi$ in $\Gamma$, we have $\rho(x) : \phi \in \Delta$.

\begin{code}
toRep : ∀ {P} {Q} → (Fin P → Fin Q) → Rep (Palphabet P) (Palphabet Q)
toRep {∅} f K ()
toRep {suc P} f .-Proof x₀ = embedr (f zero)
toRep {suc P} {Q} f K (↑ x) = toRep {P} {Q} (f ∘ ↑) K x

toRep-embedr : ∀ {P} {Q} {f : Fin P → Fin Q} {x : Fin P} → toRep f -Proof (embedr x) ≡ embedr (f x)
toRep-embedr {∅} {_} {_} {()}
toRep-embedr {suc _} {_} {_} {⊥} = ref
toRep-embedr {suc P} {Q} {f} {↑ x} = toRep-embedr {P} {Q} {f ∘ ↑} {x}

toRep-comp : ∀ {P} {Q} {R} {g : Fin Q → Fin R} {f : Fin P → Fin Q} → toRep g •R toRep f ∼R toRep (g ∘ f)
toRep-comp {∅} ()
toRep-comp {suc _} {g = g} x₀ = cong var (toRep-embedr {f = g})
toRep-comp {suc _} {g = g} {f = f} (↑ x) = toRep-comp {g = g} {f = f ∘ ↑} x

_∷_⇒R_ : ∀ {P} {Q} → (Fin P → Fin Q) → PContext P → PContext Q → Set
ρ ∷ Γ ⇒R Δ = ∀ x → typeof' (ρ x) Δ ≡ (typeof' x Γ) 〈 toRep ρ 〉

toRep-↑ : ∀ {P} → toRep {P} {suc P} ↑ ∼R (λ _ → ↑)
toRep-↑ {∅} = λ ()
toRep-↑ {suc P} = Palphabet-faithful {suc P} {suc (suc P)} {toRep {suc P} {suc (suc P)} ↑} {λ _ → ↑} (λ x → toRep-embedr {f = ↑} {x = x})

toRep-lift : ∀ {P} {Q} {f : Fin P → Fin Q} → toRep (lift f) ∼R Rep↑ (toRep f)
toRep-lift x₀ = ref
toRep-lift {∅} (↑ ())
toRep-lift {suc _} (↑ x₀) = ref
toRep-lift {suc P} {Q} {f} (↑ (↑ x)) = trans 
  (sym (toRep-comp {g = ↑} {f = f ∘ ↑} x))
  (toRep-↑ {Q} (toRep (f ∘ ↑) _ x))

↑-typed : ∀ {P} {Γ : PContext P} {φ : Expression (Palphabet P) (nonVarKind -Prp)} → 
  ↑ ∷ Γ ⇒R (Γ , φ)
↑-typed {P} {Γ} {φ} x = rep-cong {E = typeof' x Γ} (λ x → sym (toRep-↑ {P} x))

Rep↑-typed : ∀ {P} {Q} {ρ} {Γ : PContext P} {Δ : PContext Q} {φ : Expression (Palphabet P) (nonVarKind -Prp)} → ρ ∷ Γ ⇒R Δ → 
  lift ρ ∷ (Γ , φ) ⇒R (Δ , φ 〈 toRep ρ 〉)
Rep↑-typed {P} {Q = Q} {ρ = ρ} {φ = φ} ρ∷Γ→Δ ⊥ = let open ≡-Reasoning (Expression (Palphabet Q , -Proof) (nonVarKind -Prp)) in 
  begin 
    φ 〈 toRep ρ 〉 〈 (λ _ → ↑) 〉
  ≡⟨⟨ rep-comp {E = φ} ⟩⟩
    φ 〈 (λ K x → ↑ (toRep ρ _ x)) 〉      
  ≡⟨ rep-cong {E = φ} (λ x → trans (sym (toRep-↑ {Q} (toRep ρ _ x) )) (toRep-comp {g = ↑} {f = ρ} x)) ⟩
    φ 〈 toRep (lift ρ) •R (λ _ → ↑) 〉  
  ≡⟨ rep-comp {E = φ} ⟩
    φ 〈 (λ _ → ↑) 〉 〈 toRep (lift ρ) 〉 
Rep↑-typed {Q = Q} {ρ = ρ} {Γ = Γ} {Δ = Δ} ρ∷Γ→Δ (↑ x) = let open ≡-Reasoning (Expression (Palphabet Q , -Proof) (nonVarKind -Prp)) in 
  begin
    liftE (typeof' (ρ x) Δ)
  ≡⟨ cong liftE (ρ∷Γ→Δ x) ⟩
    liftE ((typeof' x Γ) 〈 toRep ρ 〉)
  ≡⟨⟨ rep-comp {E = typeof' x Γ} ⟩⟩
    (typeof' x Γ) 〈 (λ K x → ↑ (toRep ρ K x)) 〉
  ≡⟨⟨ rep-cong {E = typeof' x Γ} (λ x → toRep-↑ {Q} (toRep ρ _ x)) ⟩⟩
    (typeof' x Γ) 〈 toRep {Q} ↑ •R toRep ρ 〉
  ≡⟨ rep-cong {E = typeof' x Γ} (toRep-comp {g = ↑} {f = ρ}) ⟩
    (typeof' x Γ) 〈 toRep (lift ρ) •R (λ _ → ↑) 〉 
  ≡⟨ rep-comp {E = typeof' x Γ} ⟩
    (liftE (typeof' x Γ)) 〈 toRep (lift ρ) 〉 
\end{code}

The replacements between contexts are closed under composition.

\begin{code}
•R-typed : ∀ {P} {Q} {R} {σ : Fin Q → Fin R} {ρ : Fin P → Fin Q} {Γ} {Δ} {Θ} → ρ ∷ Γ ⇒R Δ → σ ∷ Δ ⇒R Θ →
  σ ∘ ρ ∷ Γ ⇒R Θ
•R-typed {R = R} {σ} {ρ} {Γ} {Δ} {Θ} ρ∷Γ→Δ σ∷Δ→Θ x = let open ≡-Reasoning (Expression (Palphabet R) (nonVarKind -Prp)) in 
  begin 
    typeof' (σ (ρ x)) Θ
  ≡⟨ σ∷Δ→Θ (ρ x) ⟩
    (typeof' (ρ x) Δ) 〈 toRep σ 〉     
  ≡⟨ cong (λ x₁ → x₁ 〈 toRep σ 〉) (ρ∷Γ→Δ x) ⟩
    typeof' x Γ 〈 toRep ρ 〉 〈 toRep σ 〉            
  ≡⟨⟨ rep-comp {E = typeof' x Γ} ⟩⟩
    typeof' x Γ 〈 toRep σ •R toRep ρ 〉    
  ≡⟨ rep-cong {E = typeof' x Γ} (toRep-comp {g = σ} {f = ρ}) ⟩
    typeof' x Γ 〈 toRep (σ ∘ ρ) 〉         
  ∎
\end{code}

Weakening Lemma

\begin{code}
Weakening : ∀ {P} {Q} {Γ : PContext P} {Δ : PContext Q} {ρ} {δ} {φ} → Γ ⊢ δ ∷ φ → ρ ∷ Γ ⇒R Δ → Δ ⊢ δ 〈 toRep ρ 〉 ∷ φ 〈 toRep ρ 〉
Weakening {P} {Q} {Γ} {Δ} {ρ} (var {p = p}) ρ∷Γ→Δ = subst₂ (λ x y → Δ ⊢ var x ∷ y) 
  (sym (toRep-embedr {f = ρ} {x = p}))
  (ρ∷Γ→Δ p) 
  (var {p = ρ p})
Weakening (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) ρ∷Γ→Δ = app (Weakening Γ⊢δ∷φ→ψ ρ∷Γ→Δ) (Weakening Γ⊢ε∷φ ρ∷Γ→Δ)
Weakening .{P} {Q} .{Γ} {Δ} {ρ} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∷ψ) ρ∷Γ→Δ = Λ 
  (subst (λ P → (Δ , φ 〈 toRep ρ 〉) ⊢ δ 〈 Rep↑ (toRep ρ) 〉 ∷ P) 
  (let open ≡-Reasoning (Expression (Palphabet Q , -Proof) (nonVarKind -Prp)) in
  begin 
    liftE ψ 〈 Rep↑ (toRep ρ) 〉
  ≡⟨⟨ rep-comp {E = ψ} ⟩⟩
    ψ 〈 (λ _ x → ↑ (toRep ρ _ x)) 〉
  ≡⟨ rep-comp {E = ψ} ⟩
    liftE (ψ 〈 toRep ρ 〉)
  ∎) 
  (subst₂ (λ x y → Δ , φ 〈 toRep ρ 〉 ⊢ x ∷ y) 
    (rep-cong {E = δ} (toRep-lift {f = ρ}))
    (rep-cong {E = liftE ψ} (toRep-lift {f = ρ}))
    (Weakening {suc P} {suc Q} {Γ , φ} {Δ , φ 〈 toRep ρ 〉} {lift ρ} {δ} {liftE ψ} 
      Γ,φ⊢δ∷ψ 
      claim))) where
  claim : ∀ (x : Fin (suc P)) → typeof' (lift ρ x) (Δ , φ 〈 toRep ρ 〉) ≡ typeof' x (Γ , φ) 〈 toRep (lift ρ) 〉
  claim ⊥ = let open ≡-Reasoning (Expression (Palphabet (suc Q)) (nonVarKind -Prp)) in
    begin 
      liftE (φ 〈 toRep ρ 〉)
    ≡⟨⟨ rep-comp {E = φ} ⟩⟩
      φ 〈 (λ _ → ↑) •R toRep ρ 〉
    ≡⟨ rep-comp {E = φ} ⟩
      liftE φ 〈 Rep↑ (toRep ρ) 〉
    ≡⟨⟨ rep-cong {E = liftE φ} (toRep-lift {f = ρ}) ⟩⟩
      liftE φ 〈 toRep (lift ρ) 〉
    ∎
  claim (↑ x) = let open ≡-Reasoning (Expression (Palphabet (suc Q)) (nonVarKind -Prp)) in 
    begin 
      liftE (typeof' (ρ x) Δ)
    ≡⟨ cong liftE (ρ∷Γ→Δ x) ⟩
      liftE (typeof' x Γ 〈 toRep ρ 〉)
    ≡⟨⟨ rep-comp {E = typeof' x Γ} ⟩⟩
      typeof' x Γ 〈 (λ _ → ↑) •R toRep ρ 〉       
    ≡⟨ rep-comp {E = typeof' x Γ} ⟩
      liftE (typeof' x Γ) 〈 Rep↑ (toRep ρ) 〉     
    ≡⟨⟨ rep-cong {E = liftE (typeof' x Γ)} (toRep-lift {f = ρ}) ⟩⟩
      liftE (typeof' x Γ) 〈 toRep (lift ρ) 〉     
    ∎
\end{code}

A \emph{substitution} $\sigma$ from a context $\Gamma$ to a context $\Delta$, $\sigma : \Gamma \rightarrow \Delta$,  is a substitution $\sigma$ on the syntax such that,
for every $x : \phi$ in $\Gamma$, we have $\Delta \vdash \sigma(x) : \phi$.

\begin{code}
_∷_⇒_ : ∀ {P} {Q} → Sub (Palphabet P) (Palphabet Q) → PContext P → PContext Q → Set
σ ∷ Γ ⇒ Δ = ∀ x → Δ ⊢ σ _ (embedr x) ∷ typeof' x Γ ⟦ σ ⟧

Sub↑-typed : ∀ {P} {Q} {σ} {Γ : PContext P} {Δ : PContext Q} {φ : Expression (Palphabet P) (nonVarKind -Prp)} → σ ∷ Γ ⇒ Δ → Sub↑ σ ∷ (Γ , φ) ⇒ (Δ , φ ⟦ σ ⟧)
Sub↑-typed {P} {Q} {σ} {Γ} {Δ} {φ} σ∷Γ→Δ ⊥ = subst (λ p → (Δ , φ ⟦ σ ⟧) ⊢ var x₀ ∷ p) 
  (let open ≡-Reasoning (Expression (Palphabet Q , -Proof) (nonVarKind -Prp)) in
  begin 
    liftE (φ ⟦ σ ⟧)
  ≡⟨⟨ sub-comp₁ {E = φ} ⟩⟩
    φ ⟦ (λ _ → ↑) •₁ σ ⟧      
  ≡⟨ sub-comp₂ {E = φ} ⟩
    liftE φ ⟦ Sub↑ σ ⟧        
  ∎) 
  var
Sub↑-typed {Q = Q} {σ = σ} {Γ = Γ} {Δ = Δ} {φ = φ} σ∷Γ→Δ (↑ x) = 
  subst
  (λ P → Δ , φ ⟦ σ ⟧ ⊢ Sub↑ σ -Proof (↑ (embedr x)) ∷ P)
  (let open ≡-Reasoning (Expression (Palphabet Q , -Proof) (nonVarKind -Prp)) in 
  begin 
    liftE (typeof' x Γ ⟦ σ ⟧)
  ≡⟨⟨ sub-comp₁ {E = typeof' x Γ} ⟩⟩
    typeof' x Γ ⟦ (λ _ → ↑) •₁ σ ⟧
  ≡⟨ sub-comp₂ {E = typeof' x Γ} ⟩
    liftE (typeof' x Γ) ⟦ Sub↑ σ ⟧
  ∎)
  (subst₂ (λ x y → Δ , φ ⟦ σ ⟧ ⊢ x ∷ y) 
    (rep-cong {E = σ -Proof (embedr x)} (toRep-↑ {Q})) 
    (rep-cong {E = typeof' x Γ ⟦ σ ⟧} (toRep-↑ {Q}))
    (Weakening (σ∷Γ→Δ x) (↑-typed {φ = φ ⟦ σ ⟧})))

botsub-typed : ∀ {P} {Γ : PContext P} {φ : Expression (Palphabet P) (nonVarKind -Prp)} {δ} →
  Γ ⊢ δ ∷ φ → x₀:= δ ∷ (Γ , φ) ⇒ Γ
botsub-typed {P} {Γ} {φ} {δ} Γ⊢δ∷φ ⊥ = subst (λ P₁ → Γ ⊢ δ ∷ P₁) 
  (let open ≡-Reasoning (Expression (Palphabet P) (nonVarKind -Prp)) in 
  begin 
    φ
  ≡⟨⟨ sub-idOp ⟩⟩
    φ ⟦ idOpSub ⟧
  ≡⟨ sub-comp₂ {E = φ} ⟩
    liftE φ ⟦ x₀:= δ ⟧
  ∎) 
  Γ⊢δ∷φ
botsub-typed {P} {Γ} {φ} {δ} _ (↑ x) = subst (λ P₁ → Γ ⊢ var (embedr x) ∷ P₁) 
  (let open ≡-Reasoning (Expression (Palphabet P) (nonVarKind -Prp)) in 
  begin 
    typeof' x Γ
  ≡⟨⟨ sub-idOp ⟩⟩
    typeof' x Γ ⟦ idOpSub ⟧                
  ≡⟨ sub-comp₂ {E = typeof' x Γ} ⟩
    liftE (typeof' x Γ) ⟦ x₀:= δ ⟧       
  ∎) 
  var
\end{code}

Substitution Lemma

\begin{code}
Substitution : ∀ {P} {Q} {Γ : PContext P} {Δ : PContext Q} {δ} {φ} {σ} → Γ ⊢ δ ∷ φ → σ ∷ Γ ⇒ Δ → Δ ⊢ δ ⟦ σ ⟧ ∷ φ ⟦ σ ⟧
Substitution var σ∷Γ→Δ = σ∷Γ→Δ _
Substitution (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) σ∷Γ→Δ = app (Substitution Γ⊢δ∷φ→ψ σ∷Γ→Δ) (Substitution Γ⊢ε∷φ σ∷Γ→Δ)
Substitution {Q = Q} {Δ = Δ} {σ = σ} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∷ψ) σ∷Γ→Δ = Λ 
  (subst (λ p → Δ , φ ⟦ σ ⟧ ⊢ δ ⟦ Sub↑ σ ⟧ ∷ p) 
  (let open ≡-Reasoning (Expression (Palphabet Q , -Proof) (nonVarKind -Prp)) in
  begin 
    liftE ψ ⟦ Sub↑ σ ⟧
  ≡⟨⟨ sub-comp₂ {E = ψ} ⟩⟩
    ψ ⟦ Sub↑ σ •₂ (λ _ → ↑) ⟧  
  ≡⟨ sub-comp₁ {E = ψ} ⟩
    liftE (ψ ⟦ σ ⟧)            
  ∎)
  (Substitution Γ,φ⊢δ∷ψ (Sub↑-typed σ∷Γ→Δ)))
\end{code}

Subject Reduction

\begin{code}
prop-triv-red : ∀ {P} {φ ψ : Expression (Palphabet P) (nonVarKind -Prp)} → φ ⇒ ψ → ⊥
prop-triv-red {_} {app bot out₂} (redex ())
prop-triv-red {P} {app bot out₂} (app ())
prop-triv-red {P} {app imp (app₂ _ (app₂ _ out₂))} (redex ())
prop-triv-red {P} {app imp (app₂ (out φ) (app₂ ψ out₂))} (app (appl (out φ→φ'))) = prop-triv-red {P} φ→φ'
prop-triv-red {P} {app imp (app₂ φ (app₂ (out ψ) out₂))} (app (appr (appl (out ψ→ψ')))) = prop-triv-red {P} ψ→ψ'
prop-triv-red {P} {app imp (app₂ _ (app₂ (out _) out₂))} (app (appr (appr ())))

SR : ∀ {P} {Γ : PContext P} {δ ε : Proof (Palphabet P)} {φ} → Γ ⊢ δ ∷ φ → δ ⇒ ε → Γ ⊢ ε ∷ φ
SR var ()
SR (app {ε = ε} (Λ {P} {Γ} {φ} {δ} {ψ} Γ,φ⊢δ∷ψ) Γ⊢ε∷φ) (redex βI) = 
  subst (λ P₁ → Γ ⊢ δ ⟦ x₀:= ε ⟧ ∷ P₁) 
  (let open ≡-Reasoning (Expression (Palphabet P) (nonVarKind -Prp)) in
  begin 
    liftE ψ ⟦ x₀:= ε ⟧
  ≡⟨⟨ sub-comp₂ {E = ψ} ⟩⟩
    ψ ⟦ idOpSub ⟧                 
  ≡⟨ sub-idOp ⟩
    ψ                           
  ∎) 
  (Substitution Γ,φ⊢δ∷ψ (botsub-typed Γ⊢ε∷φ))
SR (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) (app (appl (out δ→δ'))) = app (SR Γ⊢δ∷φ→ψ δ→δ') Γ⊢ε∷φ
SR (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) (app (appr (appl (out ε→ε')))) = app Γ⊢δ∷φ→ψ (SR Γ⊢ε∷φ ε→ε')
SR (app Γ⊢δ∷φ→ψ Γ⊢ε∷φ) (app (appr (appr ())))
SR (Λ Γ⊢δ∷φ) (redex ())
SR {P} (Λ Γ⊢δ∷φ) (app (appl (out φ→φ'))) with prop-triv-red {P} φ→φ'
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
C : ∀ {P} → PContext P → Prp → Proof (Palphabet P) → Set
C Γ (app bot out₂) δ = (Γ ⊢ δ ∷ ⊥P 〈 (λ _ ()) 〉 ) × SN β δ
C Γ (app imp (app₂ (out φ) (app₂ (out ψ) out₂))) δ = (Γ ⊢ δ ∷ (φ ⇒ ψ) 〈 (λ _ ()) 〉) × 
  (∀ Q {Δ : PContext Q} ρ ε → ρ ∷ Γ ⇒R Δ → C Δ φ ε → C Δ ψ (appP (δ 〈 toRep ρ 〉) ε))

C-typed : ∀ {P} {Γ : PContext P} {φ} {δ} → C Γ φ δ → Γ ⊢ δ ∷ φ 〈 (λ _ ()) 〉
C-typed {φ = app bot out₂} = proj₁
C-typed {Γ = Γ} {φ = app imp (app₂ (out φ) (app₂ (out ψ) out₂))} {δ = δ} = λ x → subst (λ P → Γ ⊢ δ ∷ P) {a = φ 〈 _ 〉 ⇒ ψ 〈 _ 〉} {b = φ 〈 _ 〉 ⇒ ψ 〈 _ 〉} 
  (cong₂ _⇒_ (rep-cong {E = φ} (λ ())) (rep-cong {E = ψ} (λ ())))
  (proj₂ x)

C-rep : ∀ {P} {Q} {Γ : PContext P} {Δ : PContext Q} {φ} {δ} {ρ} → C Γ φ δ → ρ ∷ Γ ⇒R Δ → C Δ φ (δ 〈 toRep ρ 〉)
C-rep {φ = app bot out₂} (Γ⊢δ∷⊥ , SNδ) ρ∷Γ→Δ = (Weakening Γ⊢δ∷⊥ ρ∷Γ→Δ) , SNap β-creates-rep SNδ
C-rep {P} {Q} {Γ} {Δ} {app imp (app₂ (out φ) (app₂ (out ψ) out₂))} {δ} {ρ} (Γ⊢δ∷φ⇒ψ , Cδ) ρ∷Γ→Δ = (subst {i = zero} {A = Expression (Palphabet Q) (nonVarKind -Prp)} (λ x → Δ ⊢ δ 〈 toRep ρ 〉 ∷ x) {a = φ 〈 _ 〉 〈 toRep ρ 〉 ⇒ ψ 〈 _ 〉 〈 toRep ρ 〉} {b = (φ ⇒ ψ) 〈 _ 〉}
  (cong₂ _⇒_ 
  (let open ≡-Reasoning (Expression (Palphabet Q) (nonVarKind -Prp)) in 
    begin 
      (φ 〈 _ 〉) 〈 toRep ρ 〉
    ≡⟨⟨ rep-comp {E = φ} ⟩⟩
      φ 〈 _ 〉            
    ≡⟨ rep-cong {E = φ} (λ ()) ⟩
      φ 〈 _ 〉            
    ∎)
--TODO Refactor common pattern
  (let open ≡-Reasoning (Expression (Palphabet Q) (nonVarKind -Prp)) in 
    begin 
      ψ 〈 _ 〉 〈 toRep ρ 〉
    ≡⟨⟨ rep-comp {E = ψ} ⟩⟩
      ψ 〈 _ 〉            
    ≡⟨ rep-cong {E = ψ} (λ ()) ⟩
      ψ 〈 _ 〉            
    ∎))
  (Weakening Γ⊢δ∷φ⇒ψ ρ∷Γ→Δ)) ,
  (λ R σ ε σ∷Δ→Θ ε∈Cφ → subst (C _ ψ) (cong (λ x → appP x ε) 
    (trans (sym (rep-cong {E = δ} (toRep-comp {g = σ} {f = ρ}))) (rep-comp {E = δ}))) 
    (Cδ R (σ ∘ ρ) ε (•R-typed {σ = σ} {ρ = ρ} ρ∷Γ→Δ σ∷Δ→Θ) ε∈Cφ))

C-red : ∀ {P} {Γ : PContext P} {φ} {δ} {ε} → C Γ φ δ → δ ⇒ ε → C Γ φ ε
C-red {φ = app bot out₂} (Γ⊢δ∷⊥ , SNδ) δ→ε = (SR Γ⊢δ∷⊥ δ→ε) , (SNred SNδ (osr-red δ→ε))
C-red {Γ = Γ} {φ = app imp (app₂ (out φ) (app₂ (out ψ) out₂))} {δ = δ} (Γ⊢δ∷φ⇒ψ , Cδ) δ→δ' = (SR (subst (λ x → Γ ⊢ δ ∷ x) 
  (cong₂ _⇒_ (rep-cong {E = φ} (λ ())) (rep-cong {E = ψ} (λ ()))) 
  Γ⊢δ∷φ⇒ψ) δ→δ') , 
  (λ Q ρ ε ρ∷Γ→Δ ε∈Cφ → C-red {φ = ψ} (Cδ Q ρ ε ρ∷Γ→Δ ε∈Cφ) (app (appl (out (Respects-Creates.respects-osr β-respects-rep δ→δ')))))
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
neutral-red (appNeutral .(app lam (app₂ (out _) (app₂ (Λ (out _)) out₂))) _ ()) (redex βI)
neutral-red (appNeutral _ ε neutralδ) (app (appl (out δ→δ'))) = appNeutral _ ε (neutral-red neutralδ δ→δ')
neutral-red (appNeutral δ _ neutralδ) (app (appr (appl (out ε→ε')))) = appNeutral δ _ neutralδ
neutral-red (appNeutral _ _ _) (app (appr (appr ())))

neutral-rep : ∀ {P} {Q} {δ : Proof P} {ρ : Rep P Q} → Neutral δ → Neutral (δ 〈 ρ 〉)
neutral-rep {ρ = ρ} (varNeutral x) = varNeutral (ρ -Proof x)
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
NeutralC-lm _ hyp1 _ .(app app (app₂ (out _) (app₂ (out _) out₂))) (app (appl (out δ→δ'))) = hyp1 _ δ→δ'
NeutralC-lm _ _ hyp2 .(app app (app₂ (out _) (app₂ (out _) out₂))) (app (appr (appl (out ε→ε')))) = hyp2 _ ε→ε'
NeutralC-lm _ _ _ .(app app (app₂ (out _) (app₂ (out _) _))) (app (appr (appr ())))

mutual
  NeutralC : ∀ {P} {Γ : PContext P} {δ : Proof (Palphabet P)} {φ : Prp} →
    Γ ⊢ δ ∷ φ 〈 (λ _ ()) 〉 → Neutral δ →
    (∀ ε → δ ⇒ ε → C Γ φ ε) →
    C Γ φ δ
  NeutralC {P} {Γ} {δ} {app bot out₂} Γ⊢δ∷⊥ Neutralδ hyp = Γ⊢δ∷⊥ , SNI δ (λ ε δ→ε → proj₂ (hyp ε δ→ε))
  NeutralC {P} {Γ} {δ} {app imp (app₂ (out φ) (app₂ (out ψ) out₂))} Γ⊢δ∷φ→ψ neutralδ hyp = (subst (λ P₁ → Γ ⊢ δ ∷ P₁) (rep-cong {E = φ ⇒ ψ} (λ ())) Γ⊢δ∷φ→ψ) , 
    (λ Q ρ ε ρ∷Γ→Δ ε∈Cφ → claim ε (CsubSN {φ = φ} {δ = ε} ε∈Cφ) ρ∷Γ→Δ ε∈Cφ) where
    claim : ∀ {Q} {Δ} {ρ : Fin P → Fin Q} ε → SN β ε → ρ ∷ Γ ⇒R Δ → C Δ φ ε → C Δ ψ (appP (δ 〈 toRep ρ 〉) ε)
    claim {Q} {Δ} {ρ} ε (SNI .ε SNε) ρ∷Γ→Δ ε∈Cφ = NeutralC {Q} {Δ} {appP (δ 〈 toRep ρ 〉) ε} {ψ} 
      (app (subst (λ P₁ → Δ ⊢ δ 〈 toRep ρ 〉 ∷ P₁) 
      (cong₂ _⇒_ 
      (let open ≡-Reasoning (Expression (Palphabet Q) (nonVarKind -Prp)) in 
        begin 
          φ 〈 _ 〉 〈 toRep ρ 〉
        ≡⟨⟨ rep-comp {E = φ} ⟩⟩
          φ 〈 _ 〉       
        ≡⟨⟨ rep-cong {E = φ} (λ ()) ⟩⟩
          φ 〈 _ 〉       
        ∎) 
      (  (let open ≡-Reasoning (Expression (Palphabet Q) (nonVarKind -Prp)) in 
        begin 
          ψ 〈 _ 〉 〈 toRep ρ 〉
        ≡⟨⟨ rep-comp {E = ψ} ⟩⟩
          ψ 〈 _ 〉       
        ≡⟨⟨ rep-cong {E = ψ} (λ ()) ⟩⟩
          ψ 〈 _ 〉       
        ∎) 
        ))
      (Weakening Γ⊢δ∷φ→ψ ρ∷Γ→Δ)) 
      (C-typed {Q} {Δ} {φ} {ε} ε∈Cφ)) 
      (appNeutral (δ 〈 toRep ρ 〉) ε (neutral-rep neutralδ))
      (NeutralC-lm {X = C Δ ψ} (neutral-rep neutralδ) 
      (λ δ' δ〈ρ〉→δ' → 
      let δ₀ : Proof (Palphabet P)
          δ₀ = create-osr β-creates-rep {M = δ} {N = δ'} {ρ = toRep ρ} δ〈ρ〉→δ'
      in let δ→δ₀ : δ ⇒ δ₀
             δ→δ₀ = Respects-Creates.creation.red-created (create-osr β-creates-rep δ〈ρ〉→δ')
      in let δ₀〈ρ〉≡δ' : δ₀ 〈 toRep ρ 〉 ≡ δ'
             δ₀〈ρ〉≡δ' = Respects-Creates.creation.ap-created (create-osr β-creates-rep {M = δ} {N = δ'} {ρ = toRep ρ} δ〈ρ〉→δ')
      in let δ₀∈C[φ⇒ψ] : C Γ (φ ⇒ ψ) δ₀
             δ₀∈C[φ⇒ψ] = hyp δ₀ δ→δ₀
      in let δ'∈C[φ⇒ψ] : C Δ (φ ⇒ ψ) δ'
             δ'∈C[φ⇒ψ] = subst (C Δ (φ ⇒ ψ)) δ₀〈ρ〉≡δ' (C-rep {φ = φ ⇒ ψ} δ₀∈C[φ⇒ψ] ρ∷Γ→Δ)
      in subst (C Δ ψ) (cong (λ x → appP x ε) δ₀〈ρ〉≡δ') (proj₂ δ₀∈C[φ⇒ψ] Q ρ ε ρ∷Γ→Δ ε∈Cφ))
      (λ ε' ε→ε' → claim ε' (SNε ε' ε→ε') ρ∷Γ→Δ (C-red {φ = φ} ε∈Cφ ε→ε')))
\end{code}

\begin{lemma}
\[ C_\Gamma(\phi) \subseteq SN \]
\end{lemma}

\begin{code}
  CsubSN : ∀ {P} {Γ : PContext P} {φ} {δ} → C Γ φ δ → SN β δ
  CsubSN {P} {Γ} {app bot out₂} P₁ = proj₂ P₁
  CsubSN {P} {Γ} {app imp (app₂ (out φ) (app₂ (out ψ) out₂))} {δ} P₁ = 
    let φ' : Expression (Palphabet P) (nonVarKind -Prp)
        φ' = φ 〈 (λ _ ()) 〉 in
    let Γ' : PContext (suc P)
        Γ' = Γ , φ' in ?
{-    SNap' {Palphabet P} {Palphabet P , -Proof} { varKind -Proof} {λ _ → ↑} β-respects-rep (SNoutA 
      (SNsubbodyl (SNsubexp (CsubSN {Γ = Γ'} {φ = ψ} 
      (subst (C Γ' ψ) (cong (λ x → appP x (var x₀)) (rep-cong {E = δ} (toRep-↑ {P = P}))) 
      (proj₂ P₁ (suc P) ↑ (var x₀) (λ x → sym (rep-cong {E = typeof' x Γ} (toRep-↑ {P = P}))) 
      (NeutralC {φ = φ} 
        (subst (λ x → Γ' ⊢ var x₀ ∷ x) 
          (trans (sym (rep-comp {E = φ})) (rep-cong {E = φ} (λ ()))) 
          var) 
        (varNeutral x₀) 
        (λ _ ())))))))) -}
\end{code}
