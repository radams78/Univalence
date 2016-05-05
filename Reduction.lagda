\AgdaHide{
\begin{code}
open import Grammar.Base
--TODO Make use of IsCongruence

module Reduction (G : Grammar) 
  (R : ∀ {V} {K} {C : Grammar.Kind G (Grammar.-Constructor {G} K)} → Grammar.Constructor G C → Grammar.Subexpression G V (Grammar.-Constructor {G} K) C → Grammar.Expression G V K → Set) where
open import Data.List
open import Prelims
open import Grammar.Taxonomy
open Grammar G 
open import Grammar.OpFamily G
open import Grammar.Replacement G
\end{code}
}
%TODO: Show the type of R?

\section{Reduction}

A \emph{reduction relation} is a relation $R$ between expressions such that, whenever $M R N$, then $M$ and $N$ have the same expression kind,
and $M$ is not a variable.

We define $\rightarrow_R$ to be the
congruence generated by $R$, and $\twoheadrightarrow_R$ to be its reflexive, transitive closure.

\begin{code}
Relation : Set₁
Relation = ∀ {V} {K} {C} → Subexpression V K C → Subexpression V K C → Set

data _⇒_ : Relation where
  redex : ∀ {V K} {C : Kind (-Constructor K)} {c : Constructor C} {EE : Subexpression V (-Constructor K) C} {F : Expression V K} → R c EE F → app c EE ⇒ F
  app : ∀ {V K} {C : Kind (-Constructor K)} {c : Constructor C} {MM NN : Subexpression V (-Constructor K) C} → MM ⇒ NN → app c MM ⇒ app c NN
  appl : ∀ {V K A L C M N PP} → M ⇒ N → _,,_ {V} {K} {A} {L} {C} M PP ⇒ _,,_ N PP
  appr : ∀ {V K A L C M NN PP} → NN ⇒ PP → _,,_ {V} {K} {A} {L} {C} M NN ⇒ _,,_ M PP

data _↠_ {V C K} : Subexpression V C K → Subexpression V C K → Set  where
  osr-red : ∀ {M N} → M ⇒ N → M ↠ N
  ref : ∀ {M} → M ↠ M
  trans-red : ∀ {M N P} → M ↠ N → N ↠ P → M ↠ P

redapp : ∀ {V K} {C : Kind (-Constructor K)} (c : Constructor C) {E F : Subexpression V (-Constructor K) C} →
  E ↠ F → app c E ↠ app c F
redapp _ (osr-red E→F) = osr-red (app E→F)
redapp _ ref = ref
redapp c (trans-red E↠F F↠G) = trans-red (redapp c E↠F) (redapp c F↠G)

--TODO Make lettering consistent for subexpressions
redappl : ∀ {V K A L C M N PP} → M ↠ N → _,,_ {V} {K} {A} {L} {C} M PP ↠ _,,_ N PP
redappl (osr-red A→B) = osr-red (appl A→B)
redappl ref = ref
redappl (trans-red A↠B B↠C) = trans-red (redappl A↠B) (redappl B↠C)

redappr : ∀ {V K A L C M NN PP} → NN ↠ PP → _,,_ {V} {K} {A} {L} {C} M NN ↠ _,,_ M PP
redappr (osr-red EE→FF) = osr-red (appr EE→FF)
redappr ref = ref
redappr (trans-red EE↠FF FF↠GG) = trans-red (redappr EE↠FF) (redappr FF↠GG)
\end{code}

We define $\simeq_R$ to be the reflexive, symmetric, transitive closure of $\rightarrow_R$.  We say $M$ and $N$ are \emph{$R$-convertible} iff $M \simeq_R N$.

\begin{code}
data _≃_ {V C K} : Subexpression V C K → Subexpression V C K → Set where
  osr-conv : ∀ {M N} → M ⇒ N → M ≃ N
  ref : ∀ {M} → M ≃ M
  sym-conv : ∀ {M N} → M ≃ N → N ≃ M
  trans-conv : ∀ {M N P} → M ≃ N → N ≃ P → M ≃ P
\end{code}

\begin{definition}
Let $\rhd$ be a relation between expressions such that, whenever $M \rhd N$, then $M$ and $N$ have the same kind.  Let $Op$ be a family of operators.
\begin{enumerate}
\item
We say $\rhd$  \emph{respects} $Op$ iff, for all $\sigma \in Op$, whenever $M \rhd N$, then $\sigma[M] \rhd \sigma[N]$.
\item
We say $\rhd$  \emph{creates} $Op$ iff, whenever $\rho[M] \rhd N$, then there exists $P$ such that $M \rhd P$ and $\sigma[P] \equiv N$.
\end{enumerate}
\end{definition}

\begin{code}
module Respects-Creates (Ops : OpFamily) where
  open OpFamily Ops

  respects : Relation → Set
  respects _▷_ = ∀ {U V C K} {M N : Subexpression U C K} {σ : Op U V} → M ▷ N → ap σ M ▷ ap σ N

  respects' : Set
  respects' = ∀ {U V C K c M N σ} → R {U} {C} {K} c M N → R {V} c (ap σ M) (ap σ N)

  record creation (_▷_ : Relation) {U V C K} (M : Subexpression U C K) {N} {σ : Op U V} (δ : ap σ M ▷ N) : Set where
    field
      created : Subexpression U C K
      red-created : M ▷ created
      ap-created : ap σ created ≡ N

  creates : Relation → Set
  creates ▷ = ∀ {U V C K} M {N σ} δ → creation ▷ {U} {V} {C} {K} M {N} {σ} δ

  record creation' {U V C K c} M {N} {σ : Op U V} (δ : R {V} {C} {K} c (ap σ M) N) : Set where
    field
      created : Expression U C
      red-created : R c M created
      ap-created : ap σ created ≡ N

  creates' : Set
  creates' = ∀ {U V C K c} M {N σ} δ → creation' {U} {V} {C} {K} {c} M {N} {σ} δ
\end{code}

\begin{lemma}
If $R$ respects $Op$, then so do $\rightarrow_R$, $\twoheadrightarrow_R$ and $\simeq_R$.
\end{lemma}

\begin{code}
  respects-osr : respects' → respects _⇒_
  respects-osr hyp (redex M▷N) = redex (hyp M▷N)
  respects-osr hyp (app MM→NN) = app (respects-osr hyp MM→NN)
  respects-osr hyp (appl M→N) = appl (respects-osr hyp M→N)
  respects-osr hyp (appr NN→PP) = appr (respects-osr hyp NN→PP)

  respects-red : respects' → respects _↠_
  respects-red hyp (osr-red M→N) = osr-red (respects-osr hyp M→N)
  respects-red _ ref = ref
  respects-red hyp (trans-red M↠N N↠P) = trans-red (respects-red hyp M↠N) (respects-red hyp N↠P)

  respects-conv : respects' → respects _≃_
  respects-conv hyp (osr-conv M→N) = osr-conv (respects-osr hyp M→N)
  respects-conv _ ref = ref
  respects-conv hyp (sym-conv M≃N) = sym-conv (respects-conv hyp M≃N)
  respects-conv hyp (trans-conv M≃N N≃P) = trans-conv (respects-conv hyp M≃N) (respects-conv hyp N≃P)
\end{code}

Let $\sigma, \tau : U \Rightarrow V$.  We say that $\sigma$ \emph{reduces} to $\tau$, $\sigma \twoheadrightarrow_R \tau$,
iff $\sigma(x) \twoheadrightarrow_R \tau(x)$ for all $x$.

\begin{code}
  _↠s_ : ∀ {U V} → Op U V → Op U V → Set
  _↠s_ {U} {V} σ τ = ∀ K (x : Var U K) → apV σ x ↠ apV τ x
\end{code}

\begin{lemma}
\begin{enumerate}
\item
If $R$ respects $Ops$ and $\sigma \twoheadrightarrow_R \tau$ then $(\sigma , K) \twoheadrightarrow_R (\tau , K)$.
\item
If $R$ respects $Ops$ and $\sigma \twoheadrightarrow_R \tau$ then $E[\sigma] \twoheadrightarrow_R E[\tau]$.
\end{enumerate}
\end{lemma}

\begin{code}
  liftOp-red : ∀ {U V K} {ρ σ : Op U V} → respects' → ρ ↠s σ → liftOp K ρ ↠s liftOp K σ
  liftOp-red _ _ _ x₀ = subst₂ _↠_ (sym liftOp-x₀) (sym liftOp-x₀) ref
  liftOp-red hyp ρ↠σ K (↑ x) = subst₂ _↠_ (sym (liftOp-↑ x)) (sym (liftOp-↑ x)) (respects-red hyp (ρ↠σ K x))

  liftOp'-red : ∀ {U V A} {ρ σ : Op U V} → respects' → ρ ↠s σ → liftOp' A ρ ↠s liftOp' A σ
  liftOp'-red {A = []} _ ρ↠σ = ρ↠σ
  liftOp'-red {A = (K ∷ A)} hyp ρ↠σ = liftOp'-red {A = A} hyp (liftOp-red hyp ρ↠σ)

  apredl : ∀ {U V C K} {ρ σ : Op U V} {E : Subexpression U C K} → respects' → ρ ↠s σ → ap ρ E ↠ ap σ E
  apredl {E = var x} hyp ρ↠σ = ρ↠σ _ x
  apredl {E = app c E} hyp ρ↠σ = redapp c (apredl {E = E} hyp ρ↠σ)
  apredl {E = out} _ _ = ref
  apredl {E = _,,_ {A = A} E F} hyp ρ↠σ = trans-red (redappl (apredl {E = E} hyp (liftOp'-red {A = A} hyp ρ↠σ))) (redappr (apredl {E = F} hyp ρ↠σ))
\end{code}

\begin{lemma}
If $R$ creates replacements, then so do $\rightarrow_R$, $\twoheadrightarrow_R$ and $\simeq_R$.
\end{lemma}

\begin{code}
create-osr : Respects-Creates.creates' replacement → Respects-Creates.creates replacement _⇒_
create-osr _ (var _) ()
create-osr hyp (app c E) (redex cσE⇒F) =
  let open Respects-Creates.creation' (hyp E cσE⇒F) in
  record { 
    created = created;
    red-created = redex red-created;
    ap-created = ap-created 
    }
create-osr hyp (app c E) (app σE⇒F) =     
  let open Respects-Creates.creation (create-osr hyp E σE⇒F) in 
  record { 
    created = app c created; 
    red-created = app red-created; 
    ap-created = cong (app c) ap-created 
    }
create-osr _ out ()
create-osr hyp (_,,_ E F) {σ = σ} (appl σE⇒E') =     
  let open Respects-Creates.creation (create-osr hyp E σE⇒E') in 
  record { 
    created = _,,_ created F; 
    red-created = appl red-created; 
    ap-created = cong (λ x → _,,_ x (F 〈 σ 〉)) ap-created
    }
create-osr hyp (_,,_ {A = A} E F) {σ = σ} (appr {PP = F'} σF⇒F') =     
  let open Respects-Creates.creation {Ops = replacement} (create-osr hyp F σF⇒F') in 
  record { 
    created = _,,_ E created; 
    red-created = appr red-created; 
    ap-created = cong (_,,_ (E 〈 OpFamily.liftOp' replacement A σ 〉)) ap-created
    }
\end{code}
