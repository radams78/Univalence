\AgdaHide{
\begin{code}
open import Grammar.Base
\end{code}
}

\section{Reduction}

A \emph{reduction relation} is a relation $R$ between expressions such that, whenever $M R N$, then $M$ and $N$ have the same expression kind,
and $M$ is not a variable.

\begin{code}
module Reduction.Base2 (G : Grammar) (R : Grammar.Reduction G) where
\end{code}

\AgdaHide{
\begin{code}
open import Data.List
open import Prelims
open import Grammar G
\end{code}
}

We define $\rightarrow_R$ to be the
congruence generated by $R$, $\twoheadrightarrow^+_R$ to be its transitive closure, $\twoheadrightarrow_R$ to be its reflexive, transitive closure, and $\simeq_R$ to be its reflexive, symmetric, transitive closure.
  We say $M$ and $N$ are \emph{$R$-convertible} iff $M \simeq_R N$.

\begin{code}
data Alphabet2 : Set where
  ∅ : Alphabet2
  _,_ : Alphabet2 → List VarKind → ExpressionKind → Alphabet2

data _⇒_ {V} : ∀ {K} {C} → 
  Subexpression V K C → Subexpression V K C → Set where
  redex : ∀ {K} {C : Kind (-Constructor K)} {c : Constructor C} 
    {E : Subexpression V (-Constructor K) C} {F : Expression V K} → 
    R c E F → app c E ⇒ F
  app : ∀ {K} {C : Kind (-Constructor K)} {c : Constructor C} 
    {E F : Subexpression V (-Constructor K) C} → 
    E ⇒ F → app c E ⇒ app c F
  appl : ∀ {K A L C E E' F} → 
    E ⇒ E' → _,,_ {V} {K} {A} {L} {C} E F ⇒ E' ,, F
  appr : ∀ {K A L C E F F'} → 
    F ⇒ F' → _,,_ {V} {K} {A} {L} {C} E F ⇒ E ,, F'

data _↠⁺_ {V C K} (E : Subexpression V C K) : Subexpression V C K → Set where
  osr-red+ : ∀ {F} → E ⇒ F → E ↠⁺ F
  trans-red+ : ∀ {F} {G} → E ↠⁺ F → F ↠⁺ G → E ↠⁺ G

data _↠_ {V C K} (E : Subexpression V C K) : 
  Subexpression V C K → Set where
  osr-red : ∀ {F} → E ⇒ F → E ↠ F
  ref : E ↠ E
  trans-red : ∀ {F G} → E ↠ F → F ↠ G → E ↠ G

data _≃_ {V C K} : Subexpression V C K → Subexpression V C K → Set 
  where
  osr-conv : ∀ {M N} → M ⇒ N → M ≃ N
  ref : ∀ {M} → M ≃ M
  sym-conv : ∀ {M N} → M ≃ N → N ≃ M
  trans-conv : ∀ {M N P} → M ≃ N → N ≃ P → M ≃ P
\end{code}

\AgdaHide{
\begin{code}
redex-conv : ∀ {V} {K} {C} {c} {E} {F} → R {V} {K} {C} c E F → app c E ≃ F
redex-conv rcEF = osr-conv (redex rcEF)

red-conv : ∀ {V} {C} {K} {M N : Subexpression V C K} → M ↠ N → M ≃ N
red-conv (osr-red M⇒N) = osr-conv M⇒N
red-conv ref = ref
red-conv (trans-red M↠N N↠P) = trans-conv (red-conv M↠N) (red-conv N↠P)
\end{code}
}

\begin{definition}
Let $\rhd$ be a relation between expressions such that, whenever $M \rhd N$, then $M$ and $N$ have the same kind.  Let $f$ be a function that maps expressions of kind $K$ over $U$ to expressions of kind $L$ over $V$.

We say $\rhd$ \emph{respects} $f$ iff, whenever $M \rhd N$, then $f(M) \rhd f(N)$.
\end{definition}

\begin{code}
Relation : Set₁
Relation = ∀ {V} {K} {C} → Subexpression V K C → Subexpression V K C → Set

respects : ∀ {U} {V} {K} {C} {L} {D} → Relation →
  (Subexpression U K C → Subexpression V L D) → Set
respects R f = ∀ {M N} → R M N → R (f M) (f N)
\end{code}

\begin{lemma}
If $\rightarrow_R$ respects $f$, then so do $\twoheadrightarrow^+_R$, $\twoheadrightarrow_R$ and $\simeq_R$.
\end{lemma}

\begin{code}
respects-red+ : ∀ {U} {V} {K} {C} {L} {D} {f} → 
  respects {U} {V} {K} {C} {L} {D} _⇒_ f → respects _↠⁺_ f
\end{code}

\AgdaHide{
\begin{code}
respects-red+ hyp (osr-red+ E→F) = osr-red+ (hyp E→F)
respects-red+ hyp (trans-red+ E↠F F↠G) = 
  trans-red+ (respects-red+ hyp E↠F) (respects-red+ hyp F↠G)
\end{code}
}

\begin{code}
respects-red : ∀ {U} {V} {K} {C} {L} {D} {f} → 
  respects {U} {V} {K} {C} {L} {D} _⇒_ f → respects _↠_ f
\end{code}

\AgdaHide{
\begin{code}
respects-red hyp (osr-red E→F) = osr-red (hyp E→F)
respects-red hyp ref = ref
respects-red hyp (trans-red E↠F F↠G) = 
  trans-red (respects-red hyp E↠F) (respects-red hyp F↠G)
\end{code}
}

\begin{code}
respects-conv : ∀ {U} {V} {K} {C} {L} {D} {f} → 
  respects {U} {V} {K} {C} {L} {D} _⇒_ f → respects _≃_ f
\end{code}

\AgdaHide{
\begin{code}
respects-conv hyp (osr-conv E→F) = osr-conv (hyp E→F)
respects-conv hyp ref = ref
respects-conv hyp (sym-conv E≃F) = sym-conv (respects-conv hyp E≃F)
respects-conv hyp (trans-conv E≃F F≃G) = trans-conv (respects-conv hyp E≃F) (respects-conv hyp F≃G)
\end{code}
}

\begin{lemma}
Let $Op$ be a family of operations.  If $R$ respects every operation in $Op$, then so does $\rightarrow_R$ (hence so do $\twoheadrightarrow_R$ and $\simeq_R$).
\end{lemma}

\begin{code}
module OpFamilies (Ops : OpFamily) where
  open OpFamily Ops

  respects' : Set
  respects' = ∀ {U V C K c M N σ} → 
    R {U} {C} {K} c M N → R {V} c (ap σ M) (ap σ N)

  respects-osr : ∀ {U} {V} {C} {K} {σ : Op U V} → 
    respects' → respects _⇒_ (ap {C = C} {K = K} σ)
\end{code}

\AgdaHide{
\begin{code}
  respects-osr hyp (redex M▷N) = redex (hyp M▷N)
  respects-osr hyp (app MM→NN) = app (respects-osr hyp MM→NN)
  respects-osr hyp (appl M→N) = appl (respects-osr hyp M→N)
  respects-osr hyp (appr NN→PP) = appr (respects-osr hyp NN→PP)

  apredr : ∀ {U} {V} {C} {K} {σ : Op U V} {E F : Subexpression U C K} → respects' →
         E ↠ F → ap σ E ↠ ap σ F
  apredr resp = respects-red (respects-osr resp)
\end{code}
}

Let $\sigma, \tau : U \Rightarrow V$.  We say that $\sigma$ \emph{reduces} to $\tau$, $\sigma \twoheadrightarrow_R \tau$,
iff $\sigma(x) \twoheadrightarrow_R \tau(x)$ for all $x$.

\begin{code}
  _↠s_ : ∀ {U V} → Op U V → Op U V → Set
  _↠s_ {U} {V} σ τ = ∀ K (x : Var U K) → apV σ x ↠ apV τ x
\end{code}

\begin{lemma}$ $
Suppose $R$ respects every operation $Op$ and $\rho \twoheadrightarrow_R \sigma$.  Then we have $(\rho , K) \twoheadrightarrow_R (\sigma , K)$, $\rho^A \twoheadrightarrow_R \sigma^A$, and
$E[\rho] \twoheadrightarrow_R E[\sigma]$ for all $K$, $A$, $E$.
\end{lemma}

\begin{code}
  liftOp-red : ∀ {U V K} {ρ σ : Op U V} → respects' →
    ρ ↠s σ → liftOp K ρ ↠s liftOp K σ
\end{code}

\AgdaHide{
\begin{code}
  liftOp-red _ _ _ x₀ = subst₂ _↠_ (sym liftOp-x₀) (sym liftOp-x₀) ref
  liftOp-red hyp ρ↠σ K (↑ x) = subst₂ _↠_ (sym (liftOp-↑ x)) (sym (liftOp-↑ x)) (apredr hyp (ρ↠σ K x))
\end{code}
}

\begin{code}
  liftOp'-red : ∀ {U V A} {ρ σ : Op U V} → respects' → 
    ρ ↠s σ → liftOp' A ρ ↠s liftOp' A σ
\end{code}

\AgdaHide{
\begin{code}
  liftOp'-red {A = []} _ ρ↠σ = ρ↠σ
  liftOp'-red {A = (K ∷ A)} hyp ρ↠σ = liftOp'-red {A = A} hyp (liftOp-red hyp ρ↠σ)
\end{code}
}

\begin{code}
  apredl : ∀ {U V C K} {ρ σ : Op U V} {E : Subexpression U C K} → 
    respects' → ρ ↠s σ → ap ρ E ↠ ap σ E
\end{code}

\AgdaHide{
\begin{code}
  apredl {E = var x} hyp ρ↠σ = ρ↠σ _ x
  apredl {E = app _ E} hyp ρ↠σ = respects-red app (apredl {E = E} hyp ρ↠σ)
  apredl {E = out} _ _ = ref
  apredl {E = _,,_ {A = A} E F} hyp ρ↠σ = trans-red (respects-red appl (apredl {E = E} hyp (liftOp'-red {A = A} hyp ρ↠σ))) (respects-red appr (apredl {E = F} hyp ρ↠σ))
\end{code}
}

\begin{definition}
Let $\rhd$ be a relation between expressions such that, whenever $M \rhd N$, then $M$ and $N$ have the same kind.  Let $Op$ be a family of operators.
\begin{enumerate}
\item
We say $\rhd$ \emph{creates} $Op$s iff, whenever $M [ \sigma ] \rhd N$, then there exists $P$ such that $M \rhd P$ and $P [ \sigma ] \equiv N$.
\end{enumerate}
\end{definition}

\begin{code}
  record creation (_▷_ : Relation) {U V C K} 
    (M : Subexpression U C K) {N} 
    {σ : Op U V} (δ : ap σ M ▷ N) : Set where
    field
      created : Subexpression U C K
      red-created : M ▷ created
      ap-created : ap σ created ≡ N

  creates : Relation → Set
  creates ▷ = ∀ {U V C K} M {N σ} δ → 
    creation ▷ {U} {V} {C} {K} M {N} {σ} δ

  record creation' {U V C K c} M {N} 
    {σ : Op U V} (δ : R {V} {C} {K} c (ap σ M) N) : Set where
    field
      created : Expression U C
      red-created : R c M created
      ap-created : ap σ created ≡ N

  creates' : Set
  creates' = ∀ {U V C K c} M {N σ} δ → 
    creation' {U} {V} {C} {K} {c} M {N} {σ} δ

open OpFamilies public
\end{code}

\begin{lemma}
If $E \rightarrow_R F$ then $[x := E] \twoheadrightarrow_R [x := F]$.
\end{lemma}

\begin{code}
botsub-red : ∀ {V} {K} {E F : Expression V (varKind K)} → 
  E ⇒ F → _↠s_ substitution (x₀:= E) (x₀:= F)
\end{code}

\AgdaHide{
\begin{code}
botsub-red E⇒F _ x₀ = osr-red E⇒F
botsub-red _ _ (↑ _) = ref
\end{code}
}

\begin{lemma}
If $R$ creates replacements, then so does $\rightarrow_R$.
\end{lemma}

\begin{code}
create-osr : creates' replacement → creates replacement _⇒_
\end{code}

\AgdaHide{
\begin{code}
create-osr _ (var _) ()
create-osr hyp (app c E) (redex cσE⇒F) =
  let open creation' (hyp E cσE⇒F) in
  record { 
    created = created;
    red-created = redex red-created;
    ap-created = ap-created 
    }
create-osr hyp (app c E) (app σE⇒F) =     
  let open creation (create-osr hyp E σE⇒F) in 
  record { 
    created = app c created; 
    red-created = app red-created; 
    ap-created = cong (app c) ap-created 
    }
create-osr _ out ()
create-osr hyp (_,,_ E F) {σ = σ} (appl σE⇒E') =     
  let open creation (create-osr hyp E σE⇒E') in 
  record { 
    created = _,,_ created F; 
    red-created = appl red-created; 
    ap-created = cong (λ x → _,,_ x (F 〈 σ 〉)) ap-created
    }
create-osr hyp (_,,_ {A = A} E F) {σ = σ} (appr {F' = F'} σF⇒F') =     
  let open creation {Ops = replacement} (create-osr hyp F σF⇒F') in 
  record { 
    created = _,,_ E created; 
    red-created = appr red-created; 
    ap-created = cong (_,,_ (E 〈 OpFamily.liftOp' replacement A σ 〉)) ap-created
    }
\end{code}
}
