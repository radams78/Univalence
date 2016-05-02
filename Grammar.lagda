\newcommand{\id}[1]{\mathsf{id}_{#1}}

\section{Grammars}

\begin{code}
module Grammar where

open import Function
open import Data.Empty
open import Data.Product
open import Data.Nat public
open import Data.Fin public using (Fin;zero;suc)
open import Prelims
\end{code}

Before we begin investigating the several theories we wish to consider, we present a general theory of syntax and
capture-avoiding substitution.

A \emph{taxononmy} consists of:
\begin{itemize}
\item a set of \emph{expression kinds};
\item a subset of expression kinds, called the \emph{variable kinds}.  We refer to the other expession kinds as \emph{non-variable kinds}.
\end{itemize}

A \emph{grammar} over a taxonomy consists of:
\begin{itemize}
\item a set of \emph{constructors}, each with an associated \emph{constructor kind} of the form
\begin{equation}
\label{eq:conkind}
 ((A_{11}, \ldots, A_{1r_1}) B_1, \ldots, (A_{m1}, \ldots, A_{mr_m}) B_m) C
\end{equation}
where each $A_{ij}$ is a variable kind, and each $B_i$ and $C$ is an expression kind.
\item a function assigning, to each variable kind $K$, an expression kind, the \emph{parent} of $K$.
\end{itemize}

A constructor $c$ of kind (\ref{eq:conkind}) is a constructor that takes $m$ arguments of kind $B_1$, \ldots, $B_m$, and binds $r_i$ variables in its $i$th argument of kind $A_{ij}$,
producing an expression of kind $C$.  We write this expression as

\begin{equation}
\label{eq:expression}
c([x_{11}, \ldots, x_{1r_1}]E_1, \ldots, [x_{m1}, \ldots, x_{mr_m}]E_m) \enspace .
\end{equation}

The subexpressions of the form $[x_{i1}, \ldots, x_{ir_i}]E_i$ shall be called \emph{abstractions}, and the pieces of syntax of the form $(A_{i1}, \ldots, A_{ij})B_i$ that occur in constructor kinds shall be called \emph{abstraction kinds}.

We formalise this as follows.  First, we construct the sets of expression kinds, constructor kinds and abstraction kinds over a taxonomy:

\begin{code}
record Taxonomy : Set₁ where
  field
    VarKind : Set
    NonVarKind : Set

  data ExpressionKind : Set where
    varKind : VarKind → ExpressionKind
    nonVarKind : NonVarKind → ExpressionKind

  data KindClass : Set where
    -Expression  : KindClass
    -Abstraction : KindClass
    -Constructor : ExpressionKind → KindClass

  data Kind : KindClass → Set where
    base : ExpressionKind → Kind -Expression
    out  : ExpressionKind → Kind -Abstraction
    Π    : VarKind → Kind -Abstraction → Kind -Abstraction
    out₂ : ∀ {K} → Kind (-Constructor K)
    Π₂   : ∀ {K} → Kind -Abstraction → Kind (-Constructor K) → Kind (-Constructor K)
\end{code}

An \emph{alphabet} $A$ consists of a finite set of \emph{variables}, to each of which is assigned a variable kind $K$.
Let $\emptyset$ be the empty alphabet, and $(A , K)$ be the result of extending the alphabet $A$ with one
fresh variable $x₀$ of kind $K$.  We write $\mathsf{Var}\ A\ K$ for the set of all variables in $A$ of kind $K$.

\begin{code}
  data Alphabet : Set where
    ∅ : Alphabet
    _,_ : Alphabet → VarKind → Alphabet

  data Var : Alphabet → VarKind → Set where
    x₀ : ∀ {V} {K} → Var (V , K) K
    ↑ : ∀ {V} {K} {L} → Var V L → Var (V , K) L
\end{code}

We can now define a grammar over a taxonomy:

\begin{code}
  record ToGrammar : Set₁ where
    field
      Constructor    : ∀ {K} → Kind (-Constructor K) → Set
      parent         : VarKind → ExpressionKind
\end{code}

The \emph{expressions} of kind $E$ over the alphabet $V$ are defined inductively by:
\begin{itemize}
\item
Every variable of kind $E$ is an expression of kind $E$.
\item
If $c$ is a constructor of kind (\ref{eq:conkind}), each $E_i$ is an expression of kind $B_i$, and each $x_{ij}$
is a variable of kind $A_{ij}$, then (\ref{eq:expression}) is an expression of kind $C$.
\end{itemize}
Each $x_{ij}$ is bound within $E_i$ in the expression (\ref{eq:expression}).  We identify expressions up
to $\alpha$-conversion.

\begin{code}
    data Subexpression : Alphabet → ∀ C → Kind C → Set
    Expression : Alphabet → ExpressionKind → Set
    Body : Alphabet → ∀ {K} → Kind (-Constructor K) → Set
    Abstraction : Alphabet → Kind -Abstraction → Set

    Expression V K = Subexpression V -Expression (base K)
    Body V {K} C = Subexpression V (-Constructor K) C

    alpha : Alphabet → Kind -Abstraction → Alphabet
    alpha V (out _) = V
    alpha V (Π K A) = alpha (V , K) A

    beta : Kind -Abstraction → ExpressionKind
    beta (out K) = K
    beta (Π _ A) = beta A
    
    Abstraction V A = Expression (alpha V A) (beta A)

    data Subexpression where
      var : ∀ {V} {K} → Var V K → Expression V (varKind K)
      app : ∀ {V} {K} {C} → Constructor C → Body V {K} C → Expression V K
      out₂ : ∀ {V} {K} → Body V {K} out₂
      app₂ : ∀ {V} {K} {A} {C} → Abstraction V A → Body V {K} C → Body V (Π₂ A C)

    var-inj : ∀ {V} {K} {x y : Var V K} → var x ≡ var y → x ≡ y
    var-inj refl = refl
\end{code}

\subsection{Families of Operations}

We now wish to define the operations of \emph{replacement} (replacing one variable with another) and \emph{substitution}
of expressions for variables.  To this end, we define the following.

A \emph{family of operations} consists of the following data:
\begin{itemize}
\item
Given alphabets $U$ and $V$, a set of \emph{operations} $\sigma : U \rightarrow V$.
\item
Given an operation $\sigma : U \rightarrow V$ and a variable $x$ in $U$ of kind $K$, an expression $\sigma(x)$ over $V$ of kind $K$, the result of \emph{applying} $\sigma$ to $x$.
\item
For every alphabet $V$, an operation $\id{V} : V \rightarrow V$, the \emph{identity} operation.
\item
For any operations $\rho : U \rightarrow V$ and $\sigma : V \rightarrow W$, an operation $\sigma \circ \rho : U \rightarrow W$, the \emph{composite} of
$\sigma$ and $\rho$
\item
For every alphabet $V$ and variable kind $K$, an operation $\uparrow : V \rightarrow (V , K)$, the \emph{successor} operation.
\item
For every operation $\sigma : U \rightarrow V$, an operation $(\sigma , K) : (U , K) \rightarrow (V , K)$, the result of \emph{lifting} $\sigma$.
We write $(\sigma , K_1 , K_2, \ldots , K_n)$ for $((\cdots( \sigma , K_1) , K_2) , \cdots) , K_n)$.
\end{itemize}
such that
\begin{enumerate}
\item
$\uparrow(x) \equiv x$
\item
$\id{V}(x) \equiv x$
\item
$(\sigma \circ \rho)(x) \equiv \sigma [ \rho(x) ]$
\item
Given $\sigma : U \rightarrow V$ and $x \in U$, we have $(\sigma , K)(x) \equiv \sigma(x)$
\item
$(\sigma , K)(x_0) \equiv x_0$
\end{enumerate}
where, given an operation $\sigma : U \rightarrow V$ and expression $E$ over $U$, the expression $\sigma[E]$ over $V$ is defined by
\begin{align*}
\sigma[x] & \eqdef \sigma(x)
\sigma[c([x_{11}, \ldots, x_{1r_1}] E_1, \ldots, [x_{n1}, \ldots, x_{nr_n}] E_n)] & \eqdef
c([x_{11}, \ldots, x_{1r_1}] (\sigma, K_{11}, \ldots, K_{1r_1}) [E_1], \ldots, [x_{n1}, \ldots, x_{nr_n}] (\sigma , K_{n1}, \ldots, K_{nr_n})[E_n])
\end{align*}
where $K_{ij}$ is the kind of $x_{ij}$.

We say two operations $\rho, \sigma : U \rightarrow V$ are \emph{equivalent}, $\rho \sim \sigma$, iff $\rho(x) \equiv \sigma(x)$
for all $x$.  Note that this is equivalent to $\rho[E] \equiv \sigma[E]$ for all $E$. 

\begin{code}
    record PreOpFamily : Set₂ where
      field
        Op : Alphabet → Alphabet → Set
        apV : ∀ {U} {V} {K} → Op U V → Var U K → Expression V (varKind K)
        up : ∀ {V} {K} → Op V (V , K)
        apV-up : ∀ {V} {K} {L} {x : Var V K} → apV (up {K = L}) x ≡ var (↑ x)
        idOp : ∀ V → Op V V
        apV-idOp : ∀ {V} {K} (x : Var V K) → apV (idOp V) x ≡ var x

      _∼op_ : ∀ {U} {V} → Op U V → Op U V → Set
      _∼op_ {U} {V} ρ σ = ∀ {K} (x : Var U K) → apV ρ x ≡ apV σ x
    
      ∼-refl : ∀ {U} {V} {σ : Op U V} → σ ∼op σ
      ∼-refl _ = refl
    
      ∼-sym : ∀ {U} {V} {σ τ : Op U V} → σ ∼op τ → τ ∼op σ
      ∼-sym σ-is-τ x = sym (σ-is-τ x)

      ∼-trans : ∀ {U} {V} {ρ σ τ : Op U V} → ρ ∼op σ → σ ∼op τ → ρ ∼op τ
      ∼-trans ρ-is-σ σ-is-τ x = trans (ρ-is-σ x) (σ-is-τ x)

      OP : Alphabet → Alphabet →  Setoid _ _
      OP U V = record { 
        Carrier = Op U V ; 
        _≈_ = _∼op_ ; 
        isEquivalence = record { 
          refl = ∼-refl ; 
          sym = ∼-sym ; 
          trans = ∼-trans } }

      record IsLiftFamily : Set₁ where
        field
          liftOp : ∀ {U} {V} K → Op U V → Op (U , K) (V , K)
          liftOp-cong : ∀ {V} {W} {K} {ρ σ : Op V W} → ρ ∼op σ → liftOp K ρ ∼op liftOp K σ
\end{code}

Given an operation $\sigma : U \rightarrow V$ and an abstraction kind $(x_1 : A_1 , \ldots , x_n : A_n) B$, define
the \emph{repeated lifting} $\sigma^A$ to be $((\cdots(\sigma , A_1) , A_2) , \cdots ) , A_n)$.

\begin{code}
        liftOp' : ∀ {U} {V} A → Op U V → Op (alpha U A) (alpha V A)
        liftOp' (out _) σ = σ
        liftOp' (Π K A) σ = liftOp' A (liftOp K σ)
--TODO Refactor to deal with sequences of kinds instead of abstraction kinds?

        liftOp'-cong : ∀ {U} {V} A {ρ σ : Op U V} → ρ ∼op σ → liftOp' A ρ ∼op liftOp' A σ
        liftOp'-cong (out _) ρ-is-σ = ρ-is-σ
        liftOp'-cong (Π _ A) ρ-is-σ = liftOp'-cong A (liftOp-cong ρ-is-σ)

        ap : ∀ {U} {V} {C} {K} → Op U V → Subexpression U C K → Subexpression V C K
        ap ρ (var x) = apV ρ x
        ap ρ (app c EE) = app c (ap ρ EE)
        ap _ out₂ = out₂
        ap ρ (app₂ {A = A} E EE) = app₂ (ap (liftOp' A ρ) E) (ap ρ EE)

        ap-congl : ∀ {U} {V} {C} {K} {ρ σ : Op U V} (E : Subexpression U C K) →
          ρ ∼op σ → ap ρ E ≡ ap σ E
        ap-congl (var x) ρ-is-σ = ρ-is-σ x
        ap-congl (app c E) ρ-is-σ = cong (app c) (ap-congl E ρ-is-σ)
        ap-congl out₂ _ = refl
        ap-congl (app₂ {A = A} E F) ρ-is-σ = cong₂ app₂ (ap-congl E (liftOp'-cong A ρ-is-σ)) (ap-congl F ρ-is-σ)

        ap-cong : ∀ {U} {V} {C} {K} {ρ σ : Op U V} {M N : Subexpression U C K} →
          ρ ∼op σ → M ≡ N → ap ρ M ≡ ap σ N
        ap-cong {ρ = ρ} {σ} {M} {N} ρ∼σ M≡N = let open ≡-Reasoning in 
          begin
            ap ρ M
          ≡⟨ ap-congl M ρ∼σ ⟩
            ap σ M
          ≡⟨ cong (ap σ) M≡N ⟩
            ap σ N
          ∎

    record LiftFamily : Set₂ where
      field
        preOpFamily : PreOpFamily
        isLiftFamily : PreOpFamily.IsLiftFamily preOpFamily
      open PreOpFamily preOpFamily public
      open IsLiftFamily isLiftFamily public
\end{code}

Let $F$, $G$ and $H$ be three families of operations.  For all $U$, $V$, $W$, let $\circ$ be a function
\[ \circ : F V W \times G U V \rightarrow H U W \]

\begin{lemma}
If $\circ$ respects lifting, then it respects repeated lifting.
\end{lemma}

\begin{code}
    liftOp-liftOp' : ∀ F G H
      (circ : ∀ {U} {V} {W} → LiftFamily.Op F V W → LiftFamily.Op G U V → LiftFamily.Op H U W) →
      (∀ {U V W K σ ρ} → LiftFamily._∼op_ H (LiftFamily.liftOp H K (circ {U} {V} {W} σ ρ)) (circ (LiftFamily.liftOp F K σ) (LiftFamily.liftOp G K ρ))) →
      ∀ {U V W} A {σ ρ} → LiftFamily._∼op_ H (LiftFamily.liftOp' H A (circ {U} {V} {W} σ ρ)) (circ (LiftFamily.liftOp' F A σ) (LiftFamily.liftOp' G A ρ))
    liftOp-liftOp' _ _ H circ hyp (out _) = LiftFamily.∼-refl H
    liftOp-liftOp' F G H circ hyp {U} {V} {W} (Π K A) {σ} {ρ} = let open EqReasoning (LiftFamily.OP H _ _) in 
      begin
        LiftFamily.liftOp' H A (LiftFamily.liftOp H K (circ σ ρ))
      ≈⟨ LiftFamily.liftOp'-cong H A hyp ⟩
        LiftFamily.liftOp' H A (circ (LiftFamily.liftOp F K σ) (LiftFamily.liftOp G K ρ))
      ≈⟨ liftOp-liftOp' F G H circ hyp A ⟩
        circ (LiftFamily.liftOp' F A (LiftFamily.liftOp F K σ)) (LiftFamily.liftOp' G A (LiftFamily.liftOp G K ρ))
      ∎

    record IsOpFamily (F : LiftFamily) : Set₂ where
      open LiftFamily F public
      field
          liftOp-x₀ : ∀ {U} {V} {K} {σ : Op U V} → apV (liftOp K σ) x₀ ≡ var x₀
          liftOp-↑ : ∀ {U} {V} {K} {L} {σ : Op U V} (x : Var U L) →
            apV (liftOp K σ) (↑ x) ≡ ap up (apV σ x)
          comp : ∀ {U} {V} {W} → Op V W → Op U V → Op U W
          apV-comp : ∀ {U} {V} {W} {K} {σ : Op V W} {ρ : Op U V} {x : Var U K} →
            apV (comp σ ρ) x ≡ ap σ (apV ρ x)
          liftOp-comp : ∀ {U} {V} {W} {K} {σ : Op V W} {ρ : Op U V} →
            liftOp K (comp σ ρ) ∼op comp (liftOp K σ) (liftOp K ρ)
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

      liftOp-idOp : ∀ {V} {K} → liftOp K (idOp V) ∼op idOp (V , K)
      liftOp-idOp {V} {K} x₀ = let open ≡-Reasoning in
          begin
            apV (liftOp K (idOp V)) x₀
          ≡⟨ liftOp-x₀ ⟩
            var x₀
          ≡⟨⟨ apV-idOp x₀ ⟩⟩
            apV (idOp (V , K)) x₀
          ∎
      liftOp-idOp {V} {K} {L} (↑ x) = let open ≡-Reasoning in 
          begin 
            apV (liftOp K (idOp V)) (↑ x)
          ≡⟨ liftOp-↑ x ⟩
            ap up (apV (idOp V) x)
          ≡⟨ cong (ap up) (apV-idOp x) ⟩
            ap up (var x)              
          ≡⟨ apV-up ⟩
            var (↑ x)
          ≡⟨⟨ apV-idOp (↑ x) ⟩⟩
            (apV (idOp (V , K)) (↑ x)
          ∎)

      liftOp'-idOp : ∀ {V} A → liftOp' A (idOp V) ∼op idOp (alpha V A)
      liftOp'-idOp (out _) = ∼-refl
      liftOp'-idOp {V} (Π K A) = let open EqReasoning (OP (alpha (V , K) A) (alpha (V , K) A)) in 
          begin
            liftOp' A (liftOp K (idOp V))
          ≈⟨ liftOp'-cong A liftOp-idOp ⟩
            liftOp' A (idOp (V , K))
          ≈⟨ liftOp'-idOp A ⟩
            idOp (alpha (V , K) A)
          ∎

      ap-idOp : ∀ {V} {C} {K} {E : Subexpression V C K} → ap (idOp V) E ≡ E
      ap-idOp {E = var x} = apV-idOp x
      ap-idOp {E = app c EE} = cong (app c) ap-idOp
      ap-idOp {E = out₂} = refl
      ap-idOp {E = app₂ {A = A} E F} = cong₂ app₂ (trans (ap-congl E (liftOp'-idOp A)) ap-idOp) ap-idOp

      liftOp'-comp : ∀ {U} {V} {W} A {σ : Op U V} {τ : Op V W} → liftOp' A (comp τ σ) ∼op comp (liftOp' A τ) (liftOp' A σ)
      liftOp'-comp A = liftOp-liftOp' F F F comp liftOp-comp A

      ap-comp : ∀ {U} {V} {W} {C} {K} (E : Subexpression U C K) {σ : Op V W} {ρ : Op U V} → ap (comp σ ρ) E ≡ ap σ (ap ρ E)
      ap-comp (var x) = apV-comp
      ap-comp (app c E) = cong (app c) (ap-comp E)
      ap-comp out₂ = refl
      ap-comp (app₂ {A = A} E F) = cong₂ app₂ (trans (ap-congl E (liftOp'-comp A)) (ap-comp E)) (ap-comp F)

      comp-cong : ∀ {U} {V} {W} {σ σ' : Op V W} {ρ ρ' : Op U V} → σ ∼op σ' → ρ ∼op ρ' → comp σ ρ ∼op comp σ' ρ'
      comp-cong {σ = σ} {σ'} {ρ} {ρ'} σ∼σ' ρ∼ρ' x = let open ≡-Reasoning in 
          begin
            apV (comp σ ρ) x
          ≡⟨ apV-comp ⟩
            ap σ (apV ρ x)
          ≡⟨ ap-cong σ∼σ' (ρ∼ρ' x) ⟩
            ap σ' (apV ρ' x)
          ≡⟨⟨ apV-comp ⟩⟩
            apV (comp σ' ρ') x
          ∎
\end{code}

\newcommand{\Op}{\ensuremath{\mathbf{Op}}}

The alphabets and operations up to equivalence form
a category, which we denote $\Op$.
The action of application associates, with every operator family, a functor $\Op \rightarrow \Set$,
which maps an alphabet $U$ to the set of expressions over $U$, and every operation $\sigma$ to the function $\sigma[-]$.
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

\subsection{Replacement}

The operation family of \emph{replacement} is defined as follows.  A replacement $\rho : U \rightarrow V$ is a function
that maps every variable in $U$ to a variable in $V$ of the same kind.  Application, idOpentity and composition are simply
function application, the idOpentity function and function composition.  The successor is the canonical injection $V \rightarrow (V, K)$,
and $(\sigma , K)$ is the extension of $\sigma$ that maps $x_0$ to $x_0$.

\begin{code}
    Rep : Alphabet → Alphabet → Set
    Rep U V = ∀ K → Var U K → Var V K

    Rep↑ : ∀ {U} {V} {K} → Rep U V → Rep (U , K) (V , K)
    Rep↑ _ _ x₀ = x₀
    Rep↑ ρ K (↑ x) = ↑ (ρ K x)

    upRep : ∀ {V} {K} → Rep V (V , K)
    upRep _ = ↑

    idOpRep : ∀ V → Rep V V
    idOpRep _ _ x = x

    pre-replacement : PreOpFamily
    pre-replacement = record { 
      Op = Rep; 
      apV = λ ρ x → var (ρ _ x); 
      up = upRep; 
      apV-up = refl; 
      idOp = idOpRep; 
      apV-idOp = λ _ → refl }

    _∼R_ : ∀ {U} {V} → Rep U V → Rep U V → Set
    _∼R_ = PreOpFamily._∼op_ pre-replacement

    Rep↑-cong : ∀ {U} {V} {K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → Rep↑ {K = K} ρ ∼R Rep↑ ρ'
    Rep↑-cong ρ-is-ρ' x₀ = refl
    Rep↑-cong ρ-is-ρ' (↑ x) = cong (var ∘ ↑) (var-inj (ρ-is-ρ' x))

    proto-replacement : LiftFamily
    proto-replacement = record { 
      preOpFamily = pre-replacement; 
      isLiftFamily = record { 
        liftOp = λ _ → Rep↑; 
        liftOp-cong = Rep↑-cong }}

    infix 60 _〈_〉
    _〈_〉 : ∀ {U} {V} {C} {K} → Subexpression U C K → Rep U V → Subexpression V C K
    E 〈 ρ 〉 = LiftFamily.ap proto-replacement ρ E

    infixl 75 _•R_
    _•R_ : ∀ {U} {V} {W} → Rep V W → Rep U V → Rep U W
    (ρ' •R ρ) K x = ρ' K (ρ K x)

    Rep↑-comp : ∀ {U} {V} {W} {K} {ρ' : Rep V W} {ρ : Rep U V} → Rep↑ {K = K} (ρ' •R ρ) ∼R Rep↑ ρ' •R Rep↑ ρ
    Rep↑-comp x₀ = refl
    Rep↑-comp (↑ _) = refl

    replacement : OpFamily
    replacement = record { 
      liftFamily = proto-replacement; 
      isOpFamily = record { 
        liftOp-x₀ = refl; 
        comp = _•R_; 
        apV-comp = refl; 
        liftOp-comp = Rep↑-comp; 
        liftOp-↑ = λ _ → refl }
      }

    rep-cong : ∀ {U} {V} {C} {K} {E : Subexpression U C K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → E 〈 ρ 〉 ≡ E 〈 ρ' 〉
    rep-cong {U} {V} {C} {K} {E} {ρ} {ρ'} ρ-is-ρ' = OpFamily.ap-congl replacement E ρ-is-ρ'

    rep-idOp : ∀ {V} {C} {K} {E : Subexpression V C K} → E 〈 idOpRep V 〉 ≡ E
    rep-idOp = OpFamily.ap-idOp replacement

    rep-comp : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {ρ : Rep U V} {σ : Rep V W} →
      E 〈 σ •R ρ 〉 ≡ E 〈 ρ 〉 〈 σ 〉
    rep-comp {U} {V} {W} {C} {K} {E} {ρ} {σ} = OpFamily.ap-comp replacement E

    Rep↑-idOp : ∀ {V} {K} → Rep↑ (idOpRep V) ∼R idOpRep (V , K)
    Rep↑-idOp = OpFamily.liftOp-idOp replacement
--TODO Inline many of these
\end{code}

This providOpes us with the canonical mapping from an expression over $V$ to an expression over $(V , K)$:
\begin{code}
    liftE : ∀ {V} {K} {L} → Expression V L → Expression (V , K) L
    liftE E = E 〈 upRep 〉
--TOOD Inline this
\end{code}

\subsection{Substitution}

A \emph{substitution} $\sigma$ from alphabet $U$ to alphabet $V$, $\sigma : U \Rightarrow V$, is a function $\sigma$ that maps every variable $x$ of kind $K$ in $U$ to an
\emph{expression} $\sigma(x)$ of kind $K$ over $V$.  We now aim to prov that the substitutions form a family of operations, with application and idOpentity being simply function application and idOpentity.

\begin{code}
    Sub : Alphabet → Alphabet → Set
    Sub U V = ∀ K → Var U K → Expression V (varKind K)

    idOpSub : ∀ V → Sub V V
    idOpSub _ _ = var
\end{code}

The \emph{successor} substitution $V \rightarrow (V , K)$ maps a variable $x$ to itself.

\begin{code}
    Sub↑ : ∀ {U} {V} {K} → Sub U V → Sub (U , K) (V , K)
    Sub↑ _ _ x₀ = var x₀
    Sub↑ σ K (↑ x) = (σ K x) 〈 upRep 〉

    pre-substitution : PreOpFamily
    pre-substitution = record { 
      Op = Sub; 
      apV = λ σ x → σ _ x; 
      up = λ _ x → var (↑ x); 
      apV-up = refl; 
      idOp = λ _ _ → var; 
      apV-idOp = λ _ → refl }

    _∼_ : ∀ {U} {V} → Sub U V → Sub U V → Set
    _∼_ = PreOpFamily._∼op_ pre-substitution

    Sub↑-cong : ∀ {U} {V} {K} {σ σ' : Sub U V} → σ ∼ σ' → Sub↑ {K = K} σ ∼ Sub↑ σ'
    Sub↑-cong {K = K} σ-is-σ' x₀ = refl
    Sub↑-cong σ-is-σ' (↑ x) = cong (λ E → E 〈 upRep 〉) (σ-is-σ' x)

    proto-substitution : LiftFamily
    proto-substitution = record { 
      preOpFamily = pre-substitution; 
      isLiftFamily = record { 
        liftOp = λ _ → Sub↑; 
        liftOp-cong = Sub↑-cong }
      }
\end{code}

Then, given an expression $E$ of kind $K$ over $U$, we write $E[\sigma]$ for the application of $\sigma$ to $E$, which is the result of substituting $\sigma(x)$ for $x$ for each variable in $E$, avoidOping capture.

\begin{code}
    infix 60 _⟦_⟧
    _⟦_⟧ : ∀ {U} {V} {C} {K} → Subexpression U C K → Sub U V → Subexpression V C K
    E ⟦ σ ⟧ = LiftFamily.ap proto-substitution σ E
\end{code}

Composition is defined by $(\sigma \circ \rho)(x) \equiv \rho(x) [ \sigma ]$.

\begin{code}
    infix 75 _•_
    _•_ : ∀ {U} {V} {W} → Sub V W → Sub U V → Sub U W
    (σ • ρ) K x = ρ K x ⟦ σ ⟧

    sub-cong : ∀ {U} {V} {C} {K} {E : Subexpression U C K} {σ σ' : Sub U V} → σ ∼ σ' → E ⟦ σ ⟧ ≡ E ⟦ σ' ⟧
    sub-cong {E = E} = LiftFamily.ap-congl proto-substitution E
\end{code}

Most of the axioms of a family of operations are easy to verify.  

\begin{code}
    infix 75 _•₁_
    _•₁_ : ∀ {U} {V} {W} → Rep V W → Sub U V → Sub U W
    (ρ •₁ σ) K x = (σ K x) 〈 ρ 〉

    Sub↑-comp₁ : ∀ {U} {V} {W} {K} {ρ : Rep V W} {σ : Sub U V} → Sub↑ (ρ •₁ σ) ∼ Rep↑ ρ •₁ Sub↑ σ
    Sub↑-comp₁ {K = K} x₀ = refl
    Sub↑-comp₁ {U} {V} {W} {K} {ρ} {σ} {L} (↑ x) = let open ≡-Reasoning {A = Expression (W , K) (varKind L)} in 
      begin 
        (σ L x) 〈 ρ 〉 〈 upRep 〉
      ≡⟨⟨ rep-comp {E = σ L x} ⟩⟩
        (σ L x) 〈 upRep •R ρ 〉
      ≡⟨⟩
        (σ L x) 〈 Rep↑ ρ •R upRep 〉
      ≡⟨ rep-comp {E = σ L x} ⟩
        (σ L x) 〈 upRep 〉 〈 Rep↑ ρ 〉
      ∎

    liftOp'-comp₁ : ∀ {U} {V} {W} A {ρ : Rep V W} {σ : Sub U V} →
      LiftFamily.liftOp' proto-substitution A (ρ •₁ σ) ∼ OpFamily.liftOp' replacement A ρ •₁ LiftFamily.liftOp' proto-substitution A σ
    liftOp'-comp₁ = liftOp-liftOp' proto-replacement proto-substitution proto-substitution _•₁_ Sub↑-comp₁

    sub-comp₁ : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {ρ : Rep V W} {σ : Sub U V} →
      E ⟦ ρ •₁ σ ⟧ ≡ E ⟦ σ ⟧ 〈 ρ 〉
    sub-comp₁ {E = var _} = refl
    sub-comp₁ {E = app c EE} = cong (app c) (sub-comp₁ {E = EE})
    sub-comp₁ {E = out₂} = refl
    sub-comp₁ {E = app₂ {A = A} E F} {ρ} {σ} = cong₂ app₂ 
      (let open ≡-Reasoning {A = Expression (alpha _ A) (beta A)} in
      begin 
        E ⟦ LiftFamily.liftOp' proto-substitution A (ρ •₁ σ) ⟧
      ≡⟨ LiftFamily.ap-congl proto-substitution E (liftOp'-comp₁ A) ⟩
        E ⟦ OpFamily.liftOp' replacement A ρ •₁ LiftFamily.liftOp' proto-substitution A σ ⟧ 
      ≡⟨ sub-comp₁ {E = E} ⟩
        E ⟦ LiftFamily.liftOp' proto-substitution A σ ⟧ 〈 OpFamily.liftOp' replacement A ρ 〉
      ∎)
      (sub-comp₁ {E = F})

    infix 75 _•₂_
    _•₂_ : ∀ {U} {V} {W} → Sub V W → Rep U V → Sub U W
    (σ •₂ ρ) K x = σ K (ρ K x)

    Sub↑-comp₂ : ∀ {U} {V} {W} {K} {σ : Sub V W} {ρ : Rep U V} → Sub↑ {K = K} (σ •₂ ρ) ∼ Sub↑ σ •₂ Rep↑ ρ
    Sub↑-comp₂ {K = K} x₀ = refl
    Sub↑-comp₂ (↑ x) = refl

    liftOp'-comp₂ : ∀ {U} {V} {W} A {σ : Sub V W} {ρ : Rep U V} → LiftFamily.liftOp' proto-substitution A (σ •₂ ρ) ∼ LiftFamily.liftOp' proto-substitution A σ •₂ OpFamily.liftOp' replacement A ρ
    liftOp'-comp₂ = liftOp-liftOp' proto-substitution proto-replacement proto-substitution _•₂_ Sub↑-comp₂

    sub-comp₂ : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {σ : Sub V W} {ρ : Rep U V} → E ⟦ σ •₂ ρ ⟧ ≡ E 〈 ρ 〉 ⟦ σ ⟧
    sub-comp₂ {E = var _} = refl
    sub-comp₂ {E = app c EE} = cong (app c) (sub-comp₂ {E = EE})
    sub-comp₂ {E = out₂} = refl
    sub-comp₂ {E = app₂ {A = A} E F} {σ} {ρ} = cong₂ app₂ 
      (let open ≡-Reasoning {A = Expression (alpha _ A) (beta A)} in
      begin
        E ⟦ LiftFamily.liftOp' proto-substitution A (σ •₂ ρ) ⟧
      ≡⟨ LiftFamily.ap-congl proto-substitution E (liftOp'-comp₂ A) ⟩
        E ⟦ LiftFamily.liftOp' proto-substitution A σ •₂ OpFamily.liftOp' replacement A ρ ⟧
      ≡⟨ sub-comp₂ {E = E} ⟩
        E 〈 OpFamily.liftOp' replacement A ρ 〉 ⟦ LiftFamily.liftOp' proto-substitution A σ ⟧
      ∎)
      (sub-comp₂ {E = F})
--TODO Common pattern with sub-comp₁

    Sub↑-comp : ∀ {U} {V} {W} {ρ : Sub U V} {σ : Sub V W} {K} →
      Sub↑ {K = K} (σ • ρ) ∼ Sub↑ σ • Sub↑ ρ
    Sub↑-comp x₀ = refl
    Sub↑-comp {W = W} {ρ = ρ} {σ = σ} {K = K} {L} (↑ x) =
      let open ≡-Reasoning {A = Expression (W , K) (varKind L)} in 
      begin 
        (ρ L x) ⟦ σ ⟧ 〈 upRep 〉
      ≡⟨⟨ sub-comp₁ {E = ρ L x} ⟩⟩
        ρ L x ⟦ upRep •₁ σ ⟧  
      ≡⟨ sub-comp₂ {E = ρ L x} ⟩
        (ρ L x) 〈 upRep 〉 ⟦ Sub↑ σ ⟧ 
      ∎
\end{code}

Replacement is a special case of substitution:
\begin{lemma}
Let $\rho$ be a replacement $U \rightarrow V$.
\begin{enumerate}
\item
The replacement $(\rho , K)$ and the substitution $(\rho , K)$ are equal.
\item
$$ E \langle \rho \rangle \equiv E [ \rho ] $$
\end{enumerate}
\end{lemma}

\begin{code}
    Rep↑-is-Sub↑ : ∀ {U} {V} {ρ : Rep U V} {K} → (λ L x → var (Rep↑ {K = K} ρ L x)) ∼ Sub↑ {K = K} (λ L x → var (ρ L x))
    Rep↑-is-Sub↑ x₀ = refl
    Rep↑-is-Sub↑ (↑ _) = refl

    liftOp'-is-liftOp' : ∀ {U} {V} {ρ : Rep U V} {A} → (λ K x → var (OpFamily.liftOp' replacement A ρ K x)) ∼ LiftFamily.liftOp' proto-substitution A (λ K x → var (ρ K x))
    liftOp'-is-liftOp' {ρ = ρ} {A = out _} = LiftFamily.∼-refl proto-substitution {σ = λ K x → var (ρ K x)}
    liftOp'-is-liftOp' {U} {V} {ρ} {Π K A} = LiftFamily.∼-trans proto-substitution 
      (liftOp'-is-liftOp' {ρ = Rep↑ ρ} {A = A})
      (LiftFamily.liftOp'-cong proto-substitution A (Rep↑-is-Sub↑ {ρ = ρ} {K = K}) )

    rep-is-sub : ∀ {U} {V} {K} {C} {E : Subexpression U K C} {ρ : Rep U V} → E 〈 ρ 〉 ≡ E ⟦ (λ K x → var (ρ K x)) ⟧
    rep-is-sub {E = var _} = refl
    rep-is-sub {E = app c E} = cong (app c) (rep-is-sub {E = E})
    rep-is-sub {E = out₂} = refl
    rep-is-sub {E = app₂ {A = A} E F} {ρ} = cong₂ app₂ 
      (let open ≡-Reasoning {A = Expression (alpha _ A) (beta A)} in
      begin 
        E 〈 OpFamily.liftOp' replacement A ρ 〉
      ≡⟨ rep-is-sub {E = E} ⟩
        E ⟦ (λ K x → var (OpFamily.liftOp' replacement A ρ K x)) ⟧ 
      ≡⟨ LiftFamily.ap-congl proto-substitution E (liftOp'-is-liftOp' {A = A}) ⟩
        E ⟦ LiftFamily.liftOp' proto-substitution A (λ K x → var (ρ K x)) ⟧
      ∎)
      (rep-is-sub {E = F})
    
    substitution : OpFamily
    substitution = record { 
      liftFamily = proto-substitution; 
      isOpFamily = record { 
        liftOp-x₀ = refl; 
        comp = _•_; 
        apV-comp = refl; 
        liftOp-comp = Sub↑-comp; 
        liftOp-↑ = λ {_} {_} {_} {_} {σ} x → rep-is-sub {E = σ _ x}
        }
      }

    Sub↑-idOp : ∀ {V} {K} → Sub↑ {V} {V} {K} (idOpSub V) ∼ idOpSub (V , K)
    Sub↑-idOp = OpFamily.liftOp-idOp substitution

    sub-idOp : ∀ {V} {C} {K} {E : Subexpression V C K} → E ⟦ idOpSub V ⟧ ≡ E
    sub-idOp = OpFamily.ap-idOp substitution

    sub-comp : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {σ : Sub V W} {ρ : Sub U V} →
      E ⟦ σ • ρ ⟧ ≡ E ⟦ ρ ⟧ ⟦ σ ⟧
    sub-comp {E = E} = OpFamily.ap-comp substitution E
  
    assoc : ∀ {U V W X} {ρ : Sub W X} {σ : Sub V W} {τ : Sub U V} → ρ • (σ • τ) ∼ (ρ • σ) • τ
    assoc {τ = τ} = OpFamily.assoc substitution {ρ = τ}

    sub-unitl : ∀ {U} {V} {σ : Sub U V} → idOpSub V • σ ∼ σ
    sub-unitl {σ = σ} = OpFamily.unitl substitution {σ = σ}

    sub-unitr : ∀ {U} {V} {σ : Sub U V} → σ • idOpSub U ∼ σ
    sub-unitr {σ = σ} = OpFamily.unitr substitution {σ = σ}
\end{code}

Let $E$ be an expression of kind $K$ over $V$.  Then we write $[x_0 := E]$ for the following substitution
$(V , K) \Rightarrow V$:

\begin{code}
    x₀:= : ∀ {V} {K} → Expression V (varKind K) → Sub (V , K) V
    x₀:= E _ x₀ = E
    x₀:= E K₁ (↑ x) = var x
\end{code}

\begin{lemma}
\begin{enumerate}
\item
$$ \rho \bullet_1 [x_0 := E] \sim [x_0 := E \langle \rho \rangle] \bullet_2 (\rho , K) $$
\item
$$ \sigma \bullet [x_0 := E] \sim [x_0 := E[\sigma]] \bullet (\sigma , K) $$
\end{enumerate}
\end{lemma}

\begin{code}
    comp₁-botsub : ∀ {U} {V} {K} {E : Expression U (varKind K)} {ρ : Rep U V} →
      ρ •₁ (x₀:= E) ∼ (x₀:= (E 〈 ρ 〉)) •₂ Rep↑ ρ
    comp₁-botsub x₀ = refl
    comp₁-botsub (↑ _) = refl

    comp-botsub : ∀ {U} {V} {K} {E : Expression U (varKind K)} {σ : Sub U V} →
      σ • (x₀:= E) ∼ (x₀:= (E ⟦ σ ⟧)) • Sub↑ σ
    comp-botsub x₀ = refl
    comp-botsub {σ = σ} {L} (↑ x) = trans (sym sub-idOp) (sub-comp₂ {E = σ L x})
\end{code}

\subsection{Congruences}

A \emph{congruence} is a relation $R$ on expressions such that:
\begin{enumerate}
\item
if $M R N$, then $M$ and $N$ have the same kind;
\item
if $M_i R N_i$ for all $i$, then $c[[\vec{x_1}]M_1, \ldots, [\vec{x_n}]M_n] R c[[\vec{x_1}]N_1, \ldots, [\vec{x_n}]N_n]$.
\end{enumerate}

\begin{code}
    Relation : Set₁
    Relation = ∀ {V} {C} {K} → Subexpression V C K → Subexpression V C K → Set

--TODO Abbreviations for Subexpression V (-Constructor... and Subexpression V -Abstraction
    record IsCongruence (R : Relation) : Set where
      field
        ICapp : ∀ {V} {K} {C} {c} {MM NN : Subexpression V (-Constructor K) C} → R MM NN → R (app c MM) (app c NN)
        ICout₂ : ∀ {V} {K} → R {V} { -Constructor K} {out₂} out₂ out₂
        ICappl : ∀ {V} {K} {A} {C} {M N : Abstraction V A} {PP : Body V {K} C} → R M N → R (app₂ {A = A} M PP) (app₂ N PP)
        ICappr : ∀ {V} {K} {A} {C} {M : Abstraction V A} {NN PP : Body V {K} C} → R NN PP → R (app₂ {A = A} M NN) (app₂ M PP)
\end{code}

\subsection{Contexts}

A \emph{context} has the form $x_1 : A_1, \ldots, x_n : A_n$ where, for each $i$:
\begin{itemize}
\item $x_i$ is a variable of kind $K_i$ distinct from $x_1$, \ldots, $x_{i-1}$;
\item $A_i$ is an expression of some kind $L_i$;
\item $L_i$ is a parent of $K_i$.
\end{itemize}
The \emph{domain} of this context is the alphabet $\{ x_1, \ldots, x_n \}$.

We give ourselves the following operations.  Given an alphabet $A$ and finite set $F$, let $\mathsf{extend}\ A\ K\ F$ be the
alphabet $A \uplus F$, where each element of $F$ has kind $K$.  Let $\mathsf{embedr}$ be the canonical injection
$F \rightarrow \mathsf{extend}\ A\ K\ F$; thus, for all $x \in F$, we have $\mathsf{embedr}\ x$ is a variable
of $\mathsf{extend}\ A\ K\ F$ of kind $K$.

\begin{code}
    extend : Alphabet → VarKind → ℕ → Alphabet
    extend A K zero = A
    extend A K (suc F) = extend A K F , K

    embedr : ∀ {A} {K} {F} → Fin F → Var (extend A K F) K
    embedr zero = x₀
    embedr (suc x) = ↑ (embedr x)
\end{code}

Let $\mathsf{embedl}$ be the canonical injection $A \rightarrow \mathsf{extend}\ A\ K\ F$, which
is a replacement.

\begin{code}
    embedl : ∀ {A} {K} {F} → Rep A (extend A K F)
    embedl {F = zero} _ x = x
    embedl {F = suc F} K x = ↑ (embedl {F = F} K x)
\end{code}

\begin{code}
    data Context (K : VarKind) : Alphabet → Set where
      〈〉 : Context K ∅
      _,_ : ∀ {V} → Context K V → Expression V (parent K) → Context K (V , K)

    typeof : ∀ {V} {K} (x : Var V K) (Γ : Context K V) → Expression V (parent K)
    typeof x₀ (_ , A) = A 〈 upRep 〉
    typeof (↑ x) (Γ , _) = typeof x Γ 〈 upRep 〉

    data Context' (A : Alphabet) (K : VarKind) : ℕ → Set where
      〈〉 : Context' A K zero
      _,_ : ∀ {F} → Context' A K F → Expression (extend A K F) (parent K) → Context' A K (suc F)
    
    typeof' : ∀ {A} {K} {F} → Fin F → Context' A K F → Expression (extend A K F) (parent K)
    typeof' zero (_ , A) = A 〈 upRep 〉
    typeof' (suc x) (Γ , _) = typeof' x Γ 〈 upRep 〉

record Grammar : Set₁ where
  field
    taxonomy : Taxonomy
    toGrammar : Taxonomy.ToGrammar taxonomy
  open Taxonomy taxonomy public
  open ToGrammar toGrammar public
\end{code}
