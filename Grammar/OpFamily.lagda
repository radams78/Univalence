\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.OpFamily (G : Grammar) where

open import Prelims
open Grammar G
open import Grammar.OpFamily.LiftFamily G
open import Grammar.OpFamily.Composition G
\end{code}
}

A \emph{family of operations} is a pre-family with lift $F$ together with a composition $\circ : F;F \rightarrow F$.

\begin{code}
record IsOpFamily (F : LiftFamily) : Set₂ where
  open LiftFamily F public
  infix 50 _∘_
  field
    _∘_ : ∀ {U} {V} {W} → Op V W → Op U V → Op U W
    liftOp-comp : ∀ {U} {V} {W} {K} {σ : Op V W} {ρ : Op U V} →
      liftOp K (σ ∘ ρ) ∼op liftOp K σ ∘ liftOp K ρ
    apV-comp : ∀ {U} {V} {W} {K} {σ : Op V W} {ρ : Op U V} {x : Var U K} →
      apV (σ ∘ ρ) x ≡ ap σ (apV ρ x)

  COMP : Composition F F F
  COMP = record { 
    circ = _∘_ ; 
    liftOp-circ = liftOp-comp ; 
    apV-circ = apV-comp }

  open Composition COMP public
\end{code}

The following results about operationsare easy to prove.
\begin{lemma}
  \begin{enumerate}
  \item $(\sigma , K) \circ \uparrow \sim \uparrow \circ \sigma$
  \item $(\id{V} , K) \sim \id{V,K}$
  \item $\id{V}[E] \equiv E$
  \item $(\sigma \circ \rho)[E] \equiv \sigma[\rho[E]]$
  \end{enumerate}
\end{lemma}

\begin{code}
{-  liftOp-up : ∀ {U} {V} {K} {σ : Op U V} → liftOp K σ ∘ up ∼op up ∘ σ
  liftOp-up {U} {V} {K} {σ} {L} x = 
    let open ≡-Reasoning {A = Expression (V , K) (varKind L)} in 
      begin
        apV (liftOp K σ ∘ up) x
      ≡⟨ apV-comp ⟩
        ap (liftOp K σ) (apV up x)
      ≡⟨ cong (ap (liftOp K σ)) apV-up ⟩
        apV (liftOp K σ) (↑ x)         
      ≡⟨ liftOp-↑ x ⟩
        ap up (apV σ x)
      ≡⟨⟨ apV-comp ⟩⟩
        apV (up ∘ σ) x
      ∎ -}

  liftOp-up' : ∀ {U} {V} {C} {K} {L} {σ : Op U V} (E : Subexpression U C K) →
    ap (liftOp L σ) (ap up E) ≡ ap up (ap σ E)
  liftOp-up' E = liftOp-up-mixed' COMP COMP refl {E = E}
\end{code}

\newcommand{\Op}{\ensuremath{\mathbf{Op}}}

The extend'bets and operations up to equivalence form
a category, which we denote $\Op$.
The action of application associates, with every operator family, a functor $\Op \rightarrow \Set$,
which maps an extend'bet $U$ to the set of expressions over $U$, and every operation $\sigma$ to the function $\sigma[-]$.
This functor is faithful and injective on objects, and so $\Op$ can be seen as a subcategory of $\Set$.

\begin{code}
  assoc : ∀ {U} {V} {W} {X} {τ : Op W X} {σ : Op V W} {ρ : Op U V} → τ ∘ (σ ∘ ρ) ∼op (τ ∘ σ) ∘ ρ
  assoc {U} {V} {W} {X} {τ} {σ} {ρ} {K} x = let open ≡-Reasoning {A = Expression X (varKind K)} in 
    begin 
      apV (τ ∘ (σ ∘ ρ)) x
    ≡⟨ apV-comp ⟩
      ap τ (apV (σ ∘ ρ) x)
    ≡⟨ cong (ap τ) apV-comp ⟩
      ap τ (ap σ (apV ρ x))
    ≡⟨⟨ ap-circ (apV ρ x) ⟩⟩
      ap (τ ∘ σ) (apV ρ x)
    ≡⟨⟨ apV-comp ⟩⟩
      apV ((τ ∘ σ) ∘ ρ) x
    ∎

  unitl : ∀ {U} {V} {σ : Op U V} → idOp V ∘ σ ∼op σ
  unitl {U} {V} {σ} {K} x = let open ≡-Reasoning {A = Expression V (varKind K)} in 
    begin 
      apV (idOp V ∘ σ) x
    ≡⟨ apV-comp ⟩
      ap (idOp V) (apV σ x)
    ≡⟨ ap-idOp ⟩
      apV σ x
    ∎

  unitr : ∀ {U} {V} {σ : Op U V} → σ ∘ idOp U ∼op σ
  unitr {U} {V} {σ} {K} x = let open ≡-Reasoning {A = Expression V (varKind K)} in
    begin 
      apV (σ ∘ idOp U) x
    ≡⟨ apV-comp ⟩
      ap σ (apV (idOp U) x)
    ≡⟨ cong (ap σ) (apV-idOp x) ⟩
      apV σ x
    ∎

record OpFamily : Set₂ where
  field
    liftFamily : LiftFamily
    isOpFamily  : IsOpFamily liftFamily
  open IsOpFamily isOpFamily public
\end{code}
