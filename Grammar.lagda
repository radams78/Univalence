\newcommand{\id}[1]{\mathsf{id}_{#1}}

\section{Grammars}

\begin{code}
module Grammar where

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
fresh variable $x₀$ of kind $K$.  We write $\mathsc{Var}\ A\ K$ for the set of all variables in $A$ of kind $K$.

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
record ToGrammar (T : Taxonomy) : Set₁ where
  open Taxonomy T
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
--Make Abstraction recursively defined?

  data Subexpression where
    var : ∀ {V} {K} → Var V K → Expression V (varKind K)
    app : ∀ {V} {K} {C} → Constructor C → Body V {K} C → Expression V K
    out₂ : ∀ {V} {K} → Body V {K} out₂
    app₂ : ∀ {V} {K} {A} {C} → Abstraction V A → Body V {K} C → Body V (Π₂ A C)

  var-inj : ∀ {V} {K} {x y : Var V K} → var x ≡ var y → x ≡ y
  var-inj ref = ref
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
--TODO Make this more computational?
  record PreOpFamily : Set₂ where
    field
      Op : Alphabet → Alphabet → Set
      apV : ∀ {U} {V} {K} → Op U V → Var U K → Expression V (varKind K)
      up : ∀ {V} {K} → Op V (V , K)
      apV-up : ∀ {V} {K} {L} {x : Var V K} → apV (up {K = L}) x ≡ var (↑ x)
      id : ∀ V → Op V V
      apV-id : ∀ {V} {K} (x : Var V K) → apV (id V) x ≡ var x

    _∼op_ : ∀ {U} {V} → Op U V → Op U V → Set
    _∼op_ {U} {V} ρ σ = ∀ {K} (x : Var U K) → apV ρ x ≡ apV σ x

    ∼-ref : ∀ {U} {V} {σ : Op U V} → σ ∼op σ
    ∼-ref _ = ref

    ∼-sym : ∀ {U} {V} {σ τ : Op U V} → σ ∼op τ → τ ∼op σ
    ∼-sym σ-is-τ x = sym (σ-is-τ x)

    ∼-trans : ∀ {U} {V} {ρ σ τ : Op U V} → ρ ∼op σ → σ ∼op τ → ρ ∼op τ
    ∼-trans ρ-is-σ σ-is-τ x = trans (ρ-is-σ x) (σ-is-τ x)

  record IsLiftFamily (opfamily : PreOpFamily) : Set₁ where
    open PreOpFamily opfamily
    field
      liftOp : ∀ {U} {V} K → Op U V → Op (U , K) (V , K)
      liftOp-x₀ : ∀ {U} {V} {K} {σ : Op U V} → apV (liftOp K σ) x₀ ≡ var x₀
      liftOp-wd : ∀ {V} {W} {K} {ρ σ : Op V W} → ρ ∼op σ → liftOp K ρ ∼op liftOp K σ

    liftOp' : ∀ {U} {V} A → Op U V → Op (alpha U A) (alpha V A)
    liftOp' (out _) σ = σ
    liftOp' (Π K A) σ = liftOp' A (liftOp K σ)

    liftOp'-wd : ∀ {U} {V} A {ρ σ : Op U V} → ρ ∼op σ → liftOp' A ρ ∼op liftOp' A σ
    liftOp'-wd (out _) ρ-is-σ = ρ-is-σ
    liftOp'-wd (Π _ A) ρ-is-σ = liftOp'-wd A (liftOp-wd ρ-is-σ)

    ap : ∀ {U} {V} {C} {K} → Op U V → Subexpression U C K → Subexpression V C K
    ap ρ (var x) = apV ρ x
    ap ρ (app c EE) = app c (ap ρ EE)
    ap _ out₂ = out₂
    ap ρ (app₂ {A = A} E EE) = app₂ (ap (liftOp' A ρ) E) (ap ρ EE)

    ap-wd : ∀ {U} {V} {C} {K} {ρ σ : Op U V} (E : Subexpression U C K) →
      ρ ∼op σ → ap ρ E ≡ ap σ E
    ap-wd (var x) ρ-is-σ = ρ-is-σ x
    ap-wd (app c E) ρ-is-σ = wd (app c) (ap-wd E ρ-is-σ)
    ap-wd out₂ _ = ref
    ap-wd (app₂ {A = A} E F) ρ-is-σ = wd2 app₂ (ap-wd E (liftOp'-wd A ρ-is-σ)) (ap-wd F ρ-is-σ)

  record LiftFamily : Set₂ where
    field
      preOpFamily : PreOpFamily
      isLiftFamily : IsLiftFamily preOpFamily
    open PreOpFamily preOpFamily public
    open IsLiftFamily isLiftFamily public

  record IsOpFamily (liftfamily : LiftFamily) : Set₂ where
    open LiftFamily liftfamily
    field
      comp : ∀ {U} {V} {W} → Op V W → Op U V → Op U W
      apV-comp : ∀ {U} {V} {W} {K} {σ : Op V W} {ρ : Op U V} {x : Var U K} →
        apV (comp σ ρ) x ≡ ap σ (apV ρ x)
      liftOp-comp : ∀ {U} {V} {W} {K} {σ : Op V W} {ρ : Op U V} →
        liftOp K (comp σ ρ) ∼op comp (liftOp K σ) (liftOp K ρ)
      liftOp-↑ : ∀ {U} {V} {K} {L} {σ : Op U V} (x : Var U L) →
        apV (liftOp K σ) (↑ x) ≡ ap up (apV σ x)
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
    liftOp-up {U} {V} {K} {σ} {L} x = let open Equational-Reasoning (Expression (V , K) (varKind L)) in 
      ∵ apV (comp (liftOp K σ) up) x
      ≡ ap (liftOp K σ) (apV up x)     [ apV-comp ]
      ≡ apV (liftOp K σ) (↑ x)         [ wd (ap (liftOp K σ)) apV-up ]
      ≡ ap up (apV σ x)                [ liftOp-↑ x ]
      ≡ apV (comp up σ) x              [[ apV-comp ]]

    liftOp-id : ∀ {V} {K} → liftOp K (id V) ∼op id (V , K)
    liftOp-id x₀ = trans liftOp-x₀ (sym (apV-id x₀))
    liftOp-id {V} {K} {L} (↑ x) = let open Equational-Reasoning _ in 
      ∵ apV (liftOp K (id V)) (↑ x)
      ≡ ap up (apV (id V) x)       [ liftOp-↑ x ]
      ≡ ap up (var x)              [ wd (ap up) (apV-id x) ]
      ≡ var (↑ x)                  [ apV-up ]
      ≡ apV (id (V , K)) (↑ x)     [[ apV-id (↑ x) ]]
--TODO Replace with apV (liftOp (id V)) x ≡ x or ap (liftOp (id V)) E ≡ E?
--trans (liftOp-↑ x) (trans (wd (ap up) (apV-id x)) (trans apV-up (sym (apV-id (↑ x)))))

    liftOp'-id : ∀ {V} A → liftOp' A (id V) ∼op id (alpha V A)
    liftOp'-id (out _) = ∼-ref
    liftOp'-id {V} (Π K A) = ∼-trans (liftOp'-wd A liftOp-id) (liftOp'-id A)

    ap-id : ∀ {V} {C} {K} {E : Subexpression V C K} → ap (id V) E ≡ E
    ap-id {E = var x} = apV-id x
    ap-id {E = app c EE} = wd (app c) ap-id
    ap-id {E = out₂} = ref
    ap-id {E = app₂ {A = A} E F} = wd2 app₂ (trans (ap-wd E (liftOp'-id A)) ap-id) ap-id
      
    liftOp'-comp : ∀ {U} {V} {W} A {σ : Op U V} {τ : Op V W} → liftOp' A (comp τ σ) ∼op comp (liftOp' A τ) (liftOp' A σ)
    liftOp'-comp (Taxonomy.out x) = ∼-ref
    liftOp'-comp (Taxonomy.Π x A) = ∼-trans (liftOp'-wd A liftOp-comp) (liftOp'-comp A)
--TODO Extract common pattern

    ap-comp : ∀ {U} {V} {W} {C} {K} (E : Subexpression U C K) {σ : Op V W} {ρ : Op U V} → ap (comp σ ρ) E ≡ ap σ (ap ρ E)
    ap-comp (var x) = apV-comp
    ap-comp (app c E) = wd (app c) (ap-comp E)
    ap-comp out₂ = ref
    ap-comp (app₂ {A = A} E F) = wd2 app₂ (trans (ap-wd E (liftOp'-comp A)) (ap-comp E)) (ap-comp F)
\end{code}

The alphabets and operations up to equivalence form
a category, which we denote $\Op$.
The action of application associates, with every operator family, a functor $\Op \rightarrow \Set$,
which maps an alphabet $U$ to the set of expressions over $U$, and every operation $\sigma$ to the function $\sigma[-]$.
This functor is faithful and injective on objects, and so $\Op$ can be seen as a subcategory of $\Set$.

\begin{code}
    assoc : ∀ {U} {V} {W} {X} {τ : Op W X} {σ : Op V W} {ρ : Op U V} → comp τ (comp σ ρ) ∼op comp (comp τ σ) ρ
    assoc {U} {V} {W} {X} {τ} {σ} {ρ} {K} x = let open Equational-Reasoning (Expression X (varKind K)) in 
      ∵ apV (comp τ (comp σ ρ)) x
      ≡ ap τ (apV (comp σ ρ) x)    [ apV-comp ]
      ≡ ap τ (ap σ (apV ρ x))      [ wd (ap τ) apV-comp ]
      ≡ ap (comp τ σ) (apV ρ x)    [[ ap-comp (apV ρ x) ]]
      ≡ apV (comp (comp τ σ) ρ) x  [[ apV-comp ]]

    unitl : ∀ {U} {V} {σ : Op U V} → comp (id V) σ ∼op σ
    unitl {U} {V} {σ} {K} x = let open Equational-Reasoning (Expression V (varKind K)) in 
      ∵ apV (comp (id V) σ) x
      ≡ ap (id V) (apV σ x)       [ apV-comp ]
      ≡ apV σ x                   [ ap-id ]

    unitr : ∀ {U} {V} {σ : Op U V} → comp σ (id U) ∼op σ
    unitr {U} {V} {σ} {K} x = let open Equational-Reasoning (Expression V (varKind K)) in
      ∵ apV (comp σ (id U)) x
      ≡ ap σ (apV (id U) x)      [ apV-comp ]
      ≡ apV σ x                  [ wd (ap σ) (apV-id x) ]

  record OpFamily : Set₂ where
    field
      liftFamily : LiftFamily
      isOpFamily  : IsOpFamily liftFamily
    open LiftFamily liftFamily public
    open IsOpFamily isOpFamily public
\end{code}

\subsection{Replacement}

The operation family of \emph{replacement} is defined as follows.  A replacement $\rho : U \rightarrow V$ is a function
that maps every variable in $U$ to a variable in $V$ of the same kind.  Application, identity and composition are simply
function application, the identity function and function composition.  The successor is the canonical injection $V \rightarrow (V, K)$,
and $(\sigma , K)$ is the extension of $\sigma$ that maps $x_0$ to $x_0$.

\begin{code}
  Rep : Alphabet → Alphabet → Set
  Rep U V = ∀ K → Var U K → Var V K

  Rep↑ : ∀ {U} {V} {K} → Rep U V → Rep (U , K) (V , K)
  Rep↑ _ _ x₀ = x₀
  Rep↑ ρ K (↑ x) = ↑ (ρ K x)

  upRep : ∀ {V} {K} → Rep V (V , K)
  upRep _ = ↑

  idRep : ∀ V → Rep V V
  idRep _ _ x = x

  pre-replacement : PreOpFamily
  pre-replacement = record { 
    Op = Rep; 
    apV = λ ρ x → var (ρ _ x); 
    up = upRep; 
    apV-up = ref; 
    id = idRep; 
    apV-id = λ _ → ref }

  _∼R_ : ∀ {U} {V} → Rep U V → Rep U V → Set
  _∼R_ = PreOpFamily._∼op_ pre-replacement

  Rep↑-wd : ∀ {U} {V} {K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → Rep↑ {K = K} ρ ∼R Rep↑ ρ'
  Rep↑-wd ρ-is-ρ' x₀ = ref
  Rep↑-wd ρ-is-ρ' (↑ x) = wd (var ∘ ↑) (var-inj (ρ-is-ρ' x))

  proto-replacement : LiftFamily
  proto-replacement = record { 
    preOpFamily = pre-replacement; 
    isLiftFamily = record { 
      liftOp = λ _ → Rep↑; 
      liftOp-x₀ = ref; 
      liftOp-wd = Rep↑-wd }}

--TODO Change notation?
  infix 60 _〈_〉
  _〈_〉 : ∀ {U} {V} {C} {K} → Subexpression U C K → Rep U V → Subexpression V C K
  E 〈 ρ 〉 = LiftFamily.ap proto-replacement ρ E

  infixl 75 _•R_
  _•R_ : ∀ {U} {V} {W} → Rep V W → Rep U V → Rep U W
  (ρ' •R ρ) K x = ρ' K (ρ K x)

  Rep↑-comp : ∀ {U} {V} {W} {K} {ρ' : Rep V W} {ρ : Rep U V} → Rep↑ {K = K} (ρ' •R ρ) ∼R Rep↑ ρ' •R Rep↑ ρ
  Rep↑-comp x₀ = ref
  Rep↑-comp (↑ _) = ref

  replacement : OpFamily
  replacement = record { 
    liftFamily = proto-replacement; 
    isOpFamily = record { 
      comp = _•R_; 
      apV-comp = ref; 
      liftOp-comp = Rep↑-comp; 
      liftOp-↑ = λ _ → ref }
    }

  rep-wd : ∀ {U} {V} {C} {K} {E : Subexpression U C K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → E 〈 ρ 〉 ≡ E 〈 ρ' 〉
  rep-wd {U} {V} {C} {K} {E} {ρ} {ρ'} ρ-is-ρ' = OpFamily.ap-wd replacement E ρ-is-ρ'

  rep-id : ∀ {V} {C} {K} {E : Subexpression V C K} → E 〈 idRep V 〉 ≡ E
  rep-id = OpFamily.ap-id replacement

  rep-comp : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {ρ : Rep U V} {σ : Rep V W} →
    E 〈 σ •R ρ 〉 ≡ E 〈 ρ 〉 〈 σ 〉
  rep-comp {U} {V} {W} {C} {K} {E} {ρ} {σ} = OpFamily.ap-comp replacement E

  Rep↑-id : ∀ {V} {K} → Rep↑ (idRep V) ∼R idRep (V , K)
  Rep↑-id = OpFamily.liftOp-id replacement
--TODO Inline many of these
\end{code}

This provides us with the canonical mapping from an expression over $V$ to an expression over $(V , K)$:
\begin{code}
  liftE : ∀ {V} {K} {L} → Expression V L → Expression (V , K) L
  liftE E = E 〈 upRep 〉
--TOOD Inline this
\end{code}

\subsection{Substitution}

A \emph{substitution} $\sigma$ from alphabet $U$ to alphabet $V$, $\sigma : U \Rightarrow V$, is a function $\sigma$ that maps every variable $x$ of kind $K$ in $U$ to an
\emph{expression} $\sigma(x)$ of kind $K$ over $V$.  We now aim to prov that the substitutions form a family of operations, with application and identity being simply function application and identity.

\begin{code}
  Sub : Alphabet → Alphabet → Set
  Sub U V = ∀ K → Var U K → Expression V (varKind K)

  idSub : ∀ V → Sub V V
  idSub _ _ = var
\end{code}

The \emph{successor} substitution $V \rightarrow (V , K)$ maps a variable $x$ to itself.

\begin{code}
  Sub↑ : ∀ {U} {V} {K} → Sub U V → Sub (U , K) (V , K)
  Sub↑ _ _ x₀ = var x₀
  Sub↑ σ K (↑ x) = liftE (σ K x)

  pre-substitution : PreOpFamily
  pre-substitution = record { 
    Op = Sub; 
    apV = λ σ x → σ _ x; 
    up = λ _ x → var (↑ x); 
    apV-up = ref; 
    id = λ _ _ → var; 
    apV-id = λ _ → ref }

  _∼_ : ∀ {U} {V} → Sub U V → Sub U V → Set
  _∼_ = PreOpFamily._∼op_ pre-substitution

  Sub↑-wd : ∀ {U} {V} {K} {σ σ' : Sub U V} → σ ∼ σ' → Sub↑ {K = K} σ ∼ Sub↑ σ'
  Sub↑-wd {K = K} σ-is-σ' x₀ = ref
  Sub↑-wd σ-is-σ' (↑ x) = wd liftE (σ-is-σ' x)

  proto-substitution : LiftFamily
  proto-substitution = record { 
    preOpFamily = pre-substitution; 
    isLiftFamily = record { 
      liftOp = λ _ → Sub↑; 
      liftOp-x₀ = ref; 
      liftOp-wd = Sub↑-wd }
    }
\end{code}

Then, given an expression $E$ of kind $K$ over $U$, we write $E[\sigma]$ for the application of $\sigma$ to $E$, which is the result of substituting $\sigma(x)$ for $x$ for each variable in $E$, avoiding capture.

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

  sub-wd : ∀ {U} {V} {C} {K} {E : Subexpression U C K} {σ σ' : Sub U V} → σ ∼ σ' → E ⟦ σ ⟧ ≡ E ⟦ σ' ⟧
  sub-wd {E = E} = LiftFamily.ap-wd proto-substitution E
\end{code}

Most of the axioms of a family of operations are easy to verify.  

\begin{code}
  infix 75 _•₁_
  _•₁_ : ∀ {U} {V} {W} → Rep V W → Sub U V → Sub U W
  (ρ •₁ σ) K x = (σ K x) 〈 ρ 〉

  Sub↑-comp₁ : ∀ {U} {V} {W} {K} {ρ : Rep V W} {σ : Sub U V} → Sub↑ (ρ •₁ σ) ∼ Rep↑ ρ •₁ Sub↑ σ
  Sub↑-comp₁ {K = K} x₀ = ref
  Sub↑-comp₁ {U} {V} {W} {K} {ρ} {σ} {L} (↑ x) = let open Equational-Reasoning (Expression (W , K) (varKind L)) in 
    ∵ liftE ((σ L x) 〈 ρ 〉)
    ≡ (σ L x) 〈 (λ _ x → ↑ (ρ _ x)) 〉 [[ rep-comp {E = σ L x} ]]
    ≡ (liftE (σ L x)) 〈 Rep↑ ρ 〉      [ rep-comp {E = σ L x} ]

  liftOp'-comp₁ : ∀ {U} {V} {W} {A} {ρ : Rep V W} {σ : Sub U V} →
    LiftFamily.liftOp' proto-substitution A (ρ •₁ σ) ∼ OpFamily.liftOp' replacement A ρ •₁ LiftFamily.liftOp' proto-substitution A σ
  liftOp'-comp₁ {A = out _} {ρ} {σ} = LiftFamily.∼-ref proto-substitution {σ = ρ •₁ σ}
  liftOp'-comp₁ {U} {V} {W} {Π K A} {ρ} {σ} = 
    LiftFamily.∼-trans proto-substitution 
      (LiftFamily.liftOp'-wd proto-substitution A 
        (Sub↑-comp₁ {ρ = ρ} {σ = σ})) 
        (liftOp'-comp₁ {A = A})

  sub-comp₁ : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {ρ : Rep V W} {σ : Sub U V} →
      E ⟦ ρ •₁ σ ⟧ ≡ E ⟦ σ ⟧ 〈 ρ 〉
  sub-comp₁ {E = var _} = ref
  sub-comp₁ {E = app c EE} = wd (app c) (sub-comp₁ {E = EE})
  sub-comp₁ {E = out₂} = ref
  sub-comp₁ {E = app₂ {A = A} E F} {ρ} {σ} = wd2 app₂ 
    (let open Equational-Reasoning (Expression (alpha _ A) (beta A)) in
    ∵ E ⟦ LiftFamily.liftOp' proto-substitution A (ρ •₁ σ) ⟧
    ≡ E ⟦ OpFamily.liftOp' replacement A ρ •₁ LiftFamily.liftOp' proto-substitution A σ ⟧ [ LiftFamily.ap-wd proto-substitution E (liftOp'-comp₁ {A = A}) ]
    ≡ E ⟦ LiftFamily.liftOp' proto-substitution A σ ⟧ 〈 OpFamily.liftOp' replacement A ρ 〉 [ sub-comp₁ {E = E} ])
    (sub-comp₁ {E = F})
--TODO Equational Reasoning for setoids

  infix 75 _•₂_
  _•₂_ : ∀ {U} {V} {W} → Sub V W → Rep U V → Sub U W
  (σ •₂ ρ) K x = σ K (ρ K x)

  Sub↑-comp₂ : ∀ {U} {V} {W} {K} {σ : Sub V W} {ρ : Rep U V} → Sub↑ {K = K} (σ •₂ ρ) ∼ Sub↑ σ •₂ Rep↑ ρ
  Sub↑-comp₂ {K = K} x₀ = ref
  Sub↑-comp₂ (↑ x) = ref

  liftOp'-comp₂ : ∀ {U} {V} {W} {A} {σ : Sub V W} {ρ : Rep U V} → LiftFamily.liftOp' proto-substitution A (σ •₂ ρ) ∼ LiftFamily.liftOp' proto-substitution A σ •₂ OpFamily.liftOp' replacement A ρ
  liftOp'-comp₂ {A = out _} {σ} {ρ} = LiftFamily.∼-ref proto-substitution {σ = σ •₂ ρ}
  liftOp'-comp₂ {A = Π _ A} = LiftFamily.∼-trans proto-substitution (LiftFamily.liftOp'-wd proto-substitution A Sub↑-comp₂) (liftOp'-comp₂ {A = A})

  sub-comp₂ : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {σ : Sub V W} {ρ : Rep U V} → E ⟦ σ •₂ ρ ⟧ ≡ E 〈 ρ 〉 ⟦ σ ⟧
  sub-comp₂ {E = var _} = ref
  sub-comp₂ {E = app c EE} = wd (app c) (sub-comp₂ {E = EE})
  sub-comp₂ {E = out₂} = ref
  sub-comp₂ {E = app₂ {A = A} E F} {σ} {ρ} = wd2 app₂ 
    (let open Equational-Reasoning (Expression (alpha _ A) (beta A)) in
    ∵ E ⟦ LiftFamily.liftOp' proto-substitution A (σ •₂ ρ) ⟧
    ≡ E ⟦ LiftFamily.liftOp' proto-substitution A σ •₂ OpFamily.liftOp' replacement A ρ ⟧ [ LiftFamily.ap-wd proto-substitution E (liftOp'-comp₂ {A = A}) ]
    ≡ E 〈 OpFamily.liftOp' replacement A ρ 〉 ⟦ LiftFamily.liftOp' proto-substitution A σ ⟧ [ sub-comp₂ {E = E} ])
    (sub-comp₂ {E = F})

  Sub↑-comp : ∀ {U} {V} {W} {ρ : Sub U V} {σ : Sub V W} {K} →
    Sub↑ {K = K} (σ • ρ) ∼ Sub↑ σ • Sub↑ ρ
  Sub↑-comp x₀ = ref
  Sub↑-comp {W = W} {ρ = ρ} {σ = σ} {K = K} {L} (↑ x) =
    let open Equational-Reasoning (Expression (W , K) (varKind L)) in 
      ∵ liftE ((ρ L x) ⟦ σ ⟧)
      ≡ ρ L x ⟦ (λ _ → ↑) •₁ σ ⟧  [[ sub-comp₁ {E = ρ L x} ]]
      ≡ (liftE (ρ L x)) ⟦ Sub↑ σ ⟧ [ sub-comp₂ {E = ρ L x} ]
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
  Rep↑-is-Sub↑ x₀ = ref
  Rep↑-is-Sub↑ (↑ _) = ref

  liftOp'-is-liftOp' : ∀ {U} {V} {ρ : Rep U V} {A} → (λ K x → var (OpFamily.liftOp' replacement A ρ K x)) ∼ LiftFamily.liftOp' proto-substitution A (λ K x → var (ρ K x))
  liftOp'-is-liftOp' {ρ = ρ} {A = out _} = LiftFamily.∼-ref proto-substitution {σ = λ K x → var (ρ K x)}
  liftOp'-is-liftOp' {U} {V} {ρ} {Taxonomy.Π K A} = LiftFamily.∼-trans proto-substitution 
    (liftOp'-is-liftOp' {ρ = Rep↑ ρ} {A = A})
    (LiftFamily.liftOp'-wd proto-substitution A (Rep↑-is-Sub↑ {ρ = ρ} {K = K}) )

  rep-is-sub : ∀ {U} {V} {K} {C} {E : Subexpression U K C} {ρ : Rep U V} → E 〈 ρ 〉 ≡ E ⟦ (λ K x → var (ρ K x)) ⟧
  rep-is-sub {E = var _} = ref
  rep-is-sub {E = app c E} = wd (app c) (rep-is-sub {E = E})
  rep-is-sub {E = out₂} = ref
  rep-is-sub {E = app₂ {A = A} E F} {ρ} = wd2 app₂ 
    (let open Equational-Reasoning (Expression (alpha _ A) (beta A)) in
    ∵ E 〈 OpFamily.liftOp' replacement A ρ 〉
    ≡ E ⟦ (λ K x → var (OpFamily.liftOp' replacement A ρ K x)) ⟧ [ rep-is-sub {E = E} ]
    ≡ E ⟦ LiftFamily.liftOp' proto-substitution A (λ K x → var (ρ K x)) ⟧ [ LiftFamily.ap-wd proto-substitution E (liftOp'-is-liftOp' {A = A}) ]) 
    (rep-is-sub {E = F})

  substitution : OpFamily
  substitution = record { 
    liftFamily = proto-substitution; 
    isOpFamily = record { 
      comp = _•_; 
      apV-comp = ref; 
      liftOp-comp = Sub↑-comp; 
      liftOp-↑ = λ {_} {_} {_} {_} {σ} x → rep-is-sub {E = σ _ x}
      }
    }

  Sub↑-id : ∀ {V} {K} → Sub↑ {V} {V} {K} (idSub V) ∼ idSub (V , K)
  Sub↑-id = OpFamily.liftOp-id substitution

  sub-id : ∀ {V} {C} {K} {E : Subexpression V C K} → E ⟦ idSub V ⟧ ≡ E
  sub-id = OpFamily.ap-id substitution

  sub-comp : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {σ : Sub V W} {ρ : Sub U V} →
    E ⟦ σ • ρ ⟧ ≡ E ⟦ ρ ⟧ ⟦ σ ⟧
  sub-comp {E = E} = OpFamily.ap-comp substitution E

  assoc : ∀ {U V W X} {ρ : Sub W X} {σ : Sub V W} {τ : Sub U V} → ρ • (σ • τ) ∼ (ρ • σ) • τ
  assoc {τ = τ} = OpFamily.assoc substitution {ρ = τ}

  sub-unitl : ∀ {U} {V} {σ : Sub U V} → idSub V • σ ∼ σ
  sub-unitl {σ = σ} = OpFamily.unitl substitution {σ = σ}

  sub-unitr : ∀ {U} {V} {σ : Sub U V} → σ • idSub U ∼ σ
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
    ρ •₁ (x₀:= E) ∼ (x₀:= (E ‌〈 ρ 〉)) •₂ Rep↑ ρ
  comp₁-botsub x₀ = ref
  comp₁-botsub (↑ _) = ref

  comp-botsub : ∀ {U} {V} {K} {E : Expression U (varKind K)} {σ : Sub U V} →
    σ • (x₀:= E) ∼ (x₀:= (E ⟦ σ ⟧)) • Sub↑ σ
  comp-botsub x₀ = ref
  comp-botsub {σ = σ} {L} (↑ x) = trans (sym sub-id) (sub-comp₂ {E = σ L x})
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

We give ourselves the following operations.  Given an alphabet $A$ and finite set $F$, let $\mathsc{extend}\ A\ K\ F$ be the
alphabet $A \uplus F$, where each element of $F$ has kind $K$.  Let $\mathsc{embedr}$ be the canonical injection
$F \rightarrow \mathsc{extend}\ A\ K\ F$; thus, for all $x \in F$, we have $\mathsc{embedr}\ x$ is a variable
of $\mathsc{extend}\ A\ K\ F$ of kind $K$.

\begin{code}
  extend : Alphabet → VarKind → FinSet → Alphabet
  extend A K ∅ = A
  extend A K (Lift F) = extend A K F , K

  embedr : ∀ {A} {K} {F} → El F → Var (extend A K F) K
  embedr ⊥ = x₀
  embedr (↑ x) = ↑ (embedr x)
\end{code}

Let $\mathsc{embedl}$ be the canonical injection $A \rightarrow \mathsc{extend}\ A\ K\ F$, which
is a replacement.

\begin{code}
  embedl : ∀ {A} {K} {F} → Rep A (extend A K F)
  embedl {F = ∅} _ x = x
  embedl {F = Lift F} K x = ↑ (embedl {F = F} K x)
\end{code}

\begin{code}
  data Context (K : VarKind) : Alphabet → Set where
    〈〉 : Context K ∅
    _,_ : ∀ {V} → Context K V → Expression V (parent K) → Context K (V , K)

  typeof : ∀ {V} {K} (x : Var V K) (Γ : Context K V) → Expression V (parent K)
  typeof x₀ (_ , A) = liftE A
  typeof (↑ x) (Γ , _) = liftE (typeof x Γ)

  data Context' (A : Alphabet) (K : VarKind) : FinSet → Set where
    〈〉 : Context' A K ∅
    _,_ : ∀ {F} → Context' A K F → Expression (extend A K F) (parent K) → Context' A K (Lift F)

  typeof' : ∀ {A} {K} {F} → El F → Context' A K F → Expression (extend A K F) (parent K)
  typeof' ⊥ (_ , A) = liftE A
  typeof' (↑ x) (Γ , _) = liftE (typeof' x Γ)

record Grammar : Set₁ where
  field
    taxonomy : Taxonomy
    toGrammar : ToGrammar taxonomy
  open Taxonomy taxonomy public
  open ToGrammar toGrammar public
\end{code}
