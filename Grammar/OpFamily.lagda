\begin{code}
open import Prelims
open import Grammar
import Grammar.OpFamily.Composition

module Grammar.OpFamily (G : Grammar) where
  open Grammar.Grammar G
  open Grammar.OpFamily.Composition G
\end{code}

A \emph{family of operations} is a pre-family with lift $F$ together with a composition $\circ : F;F \rightarrow F$.

\begin{code}
--TODO Notation for comp
  record IsOpFamily (F : LiftFamily) : Set₂ where
    open LiftFamily F public
    field
      comp : ∀ {U} {V} {W} → Op V W → Op U V → Op U W
      liftOp-comp : ∀ {U} {V} {W} {K} {σ : Op V W} {ρ : Op U V} →
        liftOp K (comp σ ρ) ∼op comp (liftOp K σ) (liftOp K ρ)
      apV-comp : ∀ {U} {V} {W} {K} {σ : Op V W} {ρ : Op U V} {x : Var U K} →
        apV (comp σ ρ) x ≡ ap σ (apV ρ x)

    COMP : Composition F F F
    COMP = record { 
      circ = comp ; 
      liftOp-circ = liftOp-comp ; 
      apV-circ = apV-comp }

    open Composition COMP renaming (liftOp'-circ to liftOp'-comp;ap-circ to ap-comp;circ-cong to comp-cong) public
\end{code}

\newcommand{\id}[1]{\ensuremath{\mathrm{id}_{#1}}}
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
    liftOp-up : ∀ {U} {V} {K} {σ : Op U V} → comp (liftOp K σ) up ∼op comp up σ
    liftOp-up {U} {V} {K} {σ} {L} x = 
      let open ≡-Reasoning {A = Expression (V , K) (varKind L)} in 
        begin
          apV (comp (liftOp K σ) up) x
        ≡⟨ apV-comp ⟩
          ap (liftOp K σ) (apV up x)
        ≡⟨ cong (ap (liftOp K σ)) apV-up ⟩
          apV (liftOp K σ) (↑ x)         
        ≡⟨ liftOp-↑ x ⟩
          ap up (apV σ x)
        ≡⟨⟨ apV-comp ⟩⟩
          apV (comp up σ) x
        ∎
\end{code}

\newcommand{\Op}{\ensuremath{\mathbf{Op}}}

The extend'bets and operations up to equivalence form
a category, which we denote $\Op$.
The action of application associates, with every operator family, a functor $\Op \rightarrow \Set$,
which maps an extend'bet $U$ to the set of expressions over $U$, and every operation $\sigma$ to the function $\sigma[-]$.
This functor is faithful and injective on objects, and so $\Op$ can be seen as a subcategory of $\Set$.

\begin{code}
    assoc : ∀ {U} {V} {W} {X} {τ : Op W X} {σ : Op V W} {ρ : Op U V} → comp τ (comp σ ρ) ∼op comp (comp τ σ) ρ
    assoc {U} {V} {W} {X} {τ} {σ} {ρ} {K} x = let open ≡-Reasoning {A = Expression X (varKind K)} in 
      begin 
        apV (comp τ (comp σ ρ)) x
      ≡⟨ apV-comp ⟩
        ap τ (apV (comp σ ρ) x)
      ≡⟨ cong (ap τ) apV-comp ⟩
        ap τ (ap σ (apV ρ x))
      ≡⟨⟨ ap-comp (apV ρ x) ⟩⟩
        ap (comp τ σ) (apV ρ x)
      ≡⟨⟨ apV-comp ⟩⟩
        apV (comp (comp τ σ) ρ) x
      ∎

    unitl : ∀ {U} {V} {σ : Op U V} → comp (idOp V) σ ∼op σ
    unitl {U} {V} {σ} {K} x = let open ≡-Reasoning {A = Expression V (varKind K)} in 
      begin 
        apV (comp (idOp V) σ) x
      ≡⟨ apV-comp ⟩
        ap (idOp V) (apV σ x)
      ≡⟨ ap-idOp ⟩
        apV σ x
      ∎

    unitr : ∀ {U} {V} {σ : Op U V} → comp σ (idOp U) ∼op σ
    unitr {U} {V} {σ} {K} x = let open ≡-Reasoning {A = Expression V (varKind K)} in
      begin 
        apV (comp σ (idOp U)) x
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
