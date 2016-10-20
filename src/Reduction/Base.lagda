\AgdaHide{
\begin{code}
import Relation.Binary.PropositionalEquality.Core
open import Prelims.Closure
open import Relation.Binary hiding (_⇒_)
open import Grammar.Base
\end{code}
}

\section{Reduction}

A \emph{reduction relation} is a relation $R$ between expressions such that, whenever $M R N$, then $M$ and $N$ have the same expression kind,
and $M$ is not a variable.

\begin{code}
module Reduction.Base (G : Grammar) (R : Grammar.Reduction G) where
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
infix 4 _⇒_
data _⇒_ {V} : ∀ {K} {C} → Subexp V K C → Subexp V K C → Set where
  redex : ∀ {K AA} {c : Con (SK AA K)} {E F} → 
    R c E F → app c E ⇒ F
  app : ∀ {K C} {c : Con (SK C K)} {E F} → 
    E ⇒ F → app c E ⇒ app c F
  appl : ∀ {A AA E E' F} → 
    E ⇒ E' → _∷_ {V} {A} {AA} E F ⇒ E' ∷ F
  appr : ∀ {A AA E F F'} → 
    F ⇒ F' → _∷_ {V} {A} {AA} E F ⇒ E ∷ F'

_↠⁺_ : ∀ {V C K} → Relation (Subexp V C K)
_↠⁺_ = TClose _⇒_

_↠_ : ∀ {V C K} → Relation (Subexp V C K)
_↠_ = RTClose _⇒_

RED : Alphabet → ∀ C → Kind C → Preorder _ _ _
RED V C K = record { 
  Carrier = Subexp V C K ; 
  _≈_ = _≡_ ; 
  _∼_ = _↠_ ; 
  isPreorder = record { 
    isEquivalence = Relation.Binary.PropositionalEquality.Core.isEquivalence ; 
    reflexive = λ { {M} .{M} refl → ref } ; 
    trans = λ x → Prelims.Closure.trans x } }

data _≃_ {V C K} : Subexp V C K → Subexp V C K → Set 
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

postulate red⁺-red : ∀ {V} {C} {K} {M N : Subexp V C K} → M ↠⁺ N → M ↠ N

red-conv : ∀ {V} {C} {K} {M N : Subexp V C K} → M ↠ N → M ≃ N
red-conv (inc M⇒N) = osr-conv M⇒N
red-conv ref = ref
red-conv (trans M↠N N↠P) = trans-conv (red-conv M↠N) (red-conv N↠P)

convl : ∀ {V} {A} {AA} {E E' : Abs V A} {FF : ListAbs V AA} → 
  E ≃ E' → (_∷_ {V} {A} {AA} E FF) ≃ (E' ∷ FF)
convl (osr-conv x) = osr-conv (appl x)
convl ref = ref
convl (sym-conv E≃E') = sym-conv (convl E≃E')
convl (trans-conv E≃E' E'≃E'') = trans-conv (convl E≃E') (convl E'≃E'')

convr : ∀ {V} {A} {AA} {E : Abs V A} {FF FF' : ListAbs V AA} → 
  FF ≃ FF' → (_∷_ {V} {A} {AA} E FF) ≃ (E ∷ FF')
convr (osr-conv x) = osr-conv (appr x)
convr ref = ref
convr (sym-conv E≃E') = sym-conv (convr E≃E')
convr (trans-conv E≃E' E'≃E'') = trans-conv (convr E≃E') (convr E'≃E'')

app-resp-conv : ∀ {V} {AA} {K} {c : Con (SK AA K)} {EE FF : ListAbs V AA} → EE ≃ FF → app c EE ≃ app c FF
app-resp-conv (osr-conv EE⇒FF) = osr-conv (app EE⇒FF)
app-resp-conv ref = ref
app-resp-conv (sym-conv EE≃FF) = sym-conv (app-resp-conv EE≃FF)
app-resp-conv (trans-conv EE≃FF FF≃GG) = trans-conv (app-resp-conv EE≃FF) (app-resp-conv FF≃GG)
\end{code}
}

\begin{definition}
Let $\rhd$ be a relation between expressions such that, whenever $M \rhd N$, then $M$ and $N$ have the same kind.  Let $f$ be a function that maps expressions of kind $K$ over $U$ to expressions of kind $L$ over $V$.

We say $\rhd$ \emph{respects} $f$ iff, whenever $M \rhd N$, then $f(M) \rhd f(N)$.  Similarly for binary functions.
\end{definition}

\begin{code}
Relation' : Set₁
Relation' = ∀ {V} {K} {C} → Subexp V K C → Subexp V K C → Set

respects : ∀ {U} {V} {K} {C} {L} {D} → Relation' → (Subexp U K C → Subexp V L D) → Set
respects R f = ∀ {M N} → R M N → R (f M) (f N)

respects₂ : ∀ {U} {V} {W} {K} {C} {L} {D} {M} {E} → Relation' → (Subexp U K C → Subexp V L D → Subexp W M E) → Set
respects₂ R f = ∀ {M M' N N'} → R M M' → R N N' → R (f M N) (f M' N')
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
respects-red+ hyp (inc E→F) = inc (hyp E→F)
respects-red+ hyp (trans E↠F F↠G) = 
  Prelims.Closure.trans (respects-red+ hyp E↠F) (respects-red+ hyp F↠G)
\end{code}
}

\begin{code}
respects-red : ∀ {U} {V} {K} {C} {L} {D} {f} → 
  respects {U} {V} {K} {C} {L} {D} _⇒_ f → respects _↠_ f
\end{code}

\AgdaHide{
\begin{code}
respects-red hyp (inc E→F) = inc (hyp E→F)
respects-red hyp ref = ref
respects-red hyp (trans E↠F F↠G) = 
  Prelims.Closure.trans (respects-red hyp E↠F) (respects-red hyp F↠G)
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

\begin{corollary}
The constructors in the grammar all respect $\twoheadrightarrow^+$, $\twoheadrightarrow$ and $\simeq$.
\end{corollary}

\begin{code}
app-red : ∀ {V} {AA} {K} {c : Con (SK AA K)} {EE FF : ListAbs V AA} → EE ↠ FF → app c EE ↠ app c FF
app-red = respects-red app

∷-redl : ∀ {V} {AA} {A} {E E' : Abs V A} {FF : ListAbs V AA} → E ↠ E' → (_∷_ {V} {A} {AA} E FF) ↠ (E' ∷ FF)
∷-redl = respects-red appl

∷-redr : ∀ {V} {AA} {A} {E : Abs V A} {FF FF' : ListAbs V AA} → FF ↠ FF' → (_∷_ {V} {A} {AA} E FF) ↠ (E ∷ FF')
∷-redr = respects-red appr

∷-red : ∀ {V} {AA} {A} {E E' : Abs V A} {FF FF' : ListAbs V AA} → E ↠ E' → FF ↠ FF' → (_∷_ {V} {A} {AA} E FF) ↠ (E' ∷ FF')
∷-red E↠E' FF↠FF' = Prelims.RTClosure.trans (∷-redl E↠E') (∷-redr FF↠FF')
\end{code}

\begin{lemma}
Let $Op$ be a family of operations.  If $R$ respects every operation in $Op$, then so does $\rightarrow_R$ (hence so do $\twoheadrightarrow_R$ and $\simeq_R$).
\end{lemma}

\begin{code}
module OpFamilies (Ops : OpFamily) where
  open OpFamily Ops

  respects' : Set
  respects' = ∀ {U V C K c M N σ} → 
    R {U} {C} {K} c M N → R {V} c (ap σ M) (ap σ N)

  aposrr : ∀ {U} {V} {C} {K} {σ : Op U V} → 
    respects' → respects _⇒_ (ap {C = C} {K = K} σ)
\end{code}

\AgdaHide{
\begin{code}
  aposrr hyp (redex M▷N) = redex (hyp M▷N)
  aposrr hyp (app MM→NN) = app (aposrr hyp MM→NN)
  aposrr hyp (appl M→N) = appl (aposrr hyp M→N)
  aposrr hyp (appr NN→PP) = appr (aposrr hyp NN→PP)

  apredr : ∀ {U} {V} {C} {K} {σ : Op U V} {E F : Subexp U C K} → 
    respects' → E ↠ F → ap σ E ↠ ap σ F
  apredr resp = respects-red (aposrr resp)
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
  liftOp-red hyp ρ↠σ K (↑ x) = subst₂ _↠_ (sym (liftOp-↑ x)) (sym (liftOp-↑ x)) 
    (apredr hyp (ρ↠σ K x))
\end{code}
}

\begin{code}
  liftsOp-red : ∀ {U V A} {ρ σ : Op U V} → respects' → 
    ρ ↠s σ → liftsOp A ρ ↠s liftsOp A σ
\end{code}

\AgdaHide{
\begin{code}
  liftsOp-red {A = []} _ ρ↠σ = ρ↠σ
  liftsOp-red {A = K ∷ A} hyp ρ↠σ = liftsOp-red {A = A} hyp (liftOp-red hyp ρ↠σ)
\end{code}
}

\begin{code}
  apredl : ∀ {U V C K} {ρ σ : Op U V} {E : Subexp U C K} → 
    respects' → ρ ↠s σ → ap ρ E ↠ ap σ E
\end{code}

\AgdaHide{
\begin{code}
  apredl {E = var x} hyp ρ↠σ = ρ↠σ _ x
  apredl {E = app _ E} hyp ρ↠σ = respects-red app (apredl {E = E} hyp ρ↠σ)
  apredl {E = []} _ _ = ref
  apredl {E = _∷_ {A = SK A _} E F} hyp ρ↠σ = Prelims.RTClosure.trans (respects-red appl (apredl {E = E} hyp (liftsOp-red {A = A} hyp ρ↠σ))) (respects-red appr (apredl {E = F} hyp ρ↠σ))
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
  record creation (_▷_ : Relation') {U V C K} 
    (M : Subexp U C K) {N} 
    {σ : Op U V} (δ : ap σ M ▷ N) : Set where
    field
      created : Subexp U C K
      red-created : M ▷ created
      ap-created : ap σ created ≡ N

  creates : Relation' → Set
  creates ▷ = ∀ {U V C K} M {N σ} δ → 
    creation ▷ {U} {V} {C} {K} M {N} {σ} δ

  record creation' {U V C K c} M {N} 
    {σ : Op U V} (δ : R {V} {C} {K} c (ap σ M) N) : Set where
    field
      created : Expression U K
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
  E ⇒ F → _↠s_ SUB (x₀:= E) (x₀:= F)
\end{code}

\AgdaHide{
\begin{code}
botsub-red E⇒F _ x₀ = inc E⇒F
botsub-red _ _ (↑ _) = ref
\end{code}
}

\begin{lemma}
If $R$ creates replacements, then so does $\rightarrow_R$.
\end{lemma}

\begin{code}
create-osr : creates' REP → creates REP _⇒_
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
create-osr _ [] ()
create-osr hyp (_∷_ E F) {σ = σ} (appl σE⇒E') =     
  let open creation (create-osr hyp E σE⇒E') in 
  record { 
    created = _∷_ created F; 
    red-created = appl red-created; 
    ap-created = cong (λ x → _∷_ x (F 〈 σ 〉)) ap-created
    }
create-osr hyp (_∷_ {A = SK A _} E F) {σ = σ} (appr {F' = F'} σF⇒F') =     
  let open creation {Ops = REP} (create-osr hyp F σF⇒F') in 
  record { 
    created = _∷_ E created; 
    red-created = appr red-created; 
    ap-created = cong (_∷_ (E 〈 OpFamily.liftsOp REP A σ 〉)) ap-created
    }
\end{code}
}
