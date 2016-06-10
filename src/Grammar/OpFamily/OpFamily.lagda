\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.OpFamily.OpFamily (G : Grammar) where

open import Prelims
open Grammar G
open import Grammar.OpFamily.LiftFamily G
open import Grammar.OpFamily.Composition G
\end{code}
}

\subsubsection{Family of Operations}

Finally. we can define: a \emph{family of operations} is a pre-family with lift $F$ together with a composition $\circ : F;F \rightarrow F$.

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
\end{code}

\AgdaHide{
\begin{code}
record OpFamily : Set₂ where
  field
    liftFamily : LiftFamily
    isOpFamily  : IsOpFamily liftFamily
  open IsOpFamily isOpFamily public
\end{code}
}

\begin{code}
  COMP : Composition liftFamily liftFamily liftFamily
  COMP = record { 
    circ = _∘_ ; 
    liftOp-circ = liftOp-comp ; 
    apV-circ = apV-comp }

  open Composition COMP public

  postulate comp-congl : ∀ {U} {V} {W} {σ σ' : Op V W} {ρ : Op U V} →
                       σ ∼op σ' → σ ∘ ρ ∼op σ' ∘ ρ
  postulate comp-congr : ∀ {U} {V} {W} {σ : Op V W} {ρ ρ' : Op U V} →
                       ρ ∼op ρ' → σ ∘ ρ ∼op σ ∘ ρ'
\end{code}

The following results about operations are easy to prove.
\begin{lemma}$ $
  \begin{enumerate}
  \item $(\sigma , K) \circ \uparrow \sim \uparrow \circ \sigma$
  \item $(\id{V} , K) \sim \id{V,K}$
  \item $\id{V}[E] \equiv E$
  \item $(\sigma \circ \rho)[E] \equiv \sigma[\rho[E]]$
  \end{enumerate}
\end{lemma}

\begin{code}
  liftOp-up' : ∀ {U} {V} {C} {K} {L}
    {σ : Op U V} (E : Subexpression U C K) →
    ap (liftOp L σ) (ap up E) ≡ ap up (ap σ E)
\end{code}

\AgdaHide{
\begin{code}
  liftOp-up' E = liftOp-up-mixed COMP COMP refl {E = E}
\end{code}
}

\newcommand{\Op}{\ensuremath{\mathbf{Op}}}

The alphabets and operations up to equivalence form
a category, which we denote $\Op$.
The action of application associates, with every operator family, a functor $\Op \rightarrow \Set$,
which maps an alphabet $U$ to the set of expressions over $U$, and every operation $\sigma$ to the function $\sigma[-]$.
This functor is faithful and injective on objects, and so $\Op$ can be seen as a subcategory of $\Set$.

\begin{code}
  assoc : ∀ {U} {V} {W} {X} 
    {τ : Op W X} {σ : Op V W} {ρ : Op U V} → 
    τ ∘ (σ ∘ ρ) ∼op (τ ∘ σ) ∘ ρ
\end{code}

\AgdaHide{
\begin{code}
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
\end{code}
}

\begin{code}
  unitl : ∀ {U} {V} {σ : Op U V} → idOp V ∘ σ ∼op σ
\end{code}

\AgdaHide{
\begin{code}
  unitl {U} {V} {σ} {K} x = let open ≡-Reasoning {A = Expression V (varKind K)} in 
    begin 
      apV (idOp V ∘ σ) x
    ≡⟨ apV-comp ⟩
      ap (idOp V) (apV σ x)
    ≡⟨ ap-idOp ⟩
      apV σ x
    ∎
\end{code}
}

\begin{code}
  unitr : ∀ {U} {V} {σ : Op U V} → σ ∘ idOp U ∼op σ
\end{code}

\AgdaHide{
\begin{code}
  unitr {U} {V} {σ} {K} x = let open ≡-Reasoning {A = Expression V (varKind K)} in
    begin 
      apV (σ ∘ idOp U) x
    ≡⟨ apV-comp ⟩
      ap σ (apV (idOp U) x)
    ≡⟨ cong (ap σ) (apV-idOp x) ⟩
      apV σ x
    ∎
\end{code}
}