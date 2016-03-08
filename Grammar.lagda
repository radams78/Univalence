\section{Grammars}

\begin{code}
module Grammar where

open import Prelims hiding (_∼_)
\end{code}

Before we begin investigating the several theories we wish to consider, we present a general theory of syntax and
capture-avoiding substitution.

A \emph{grammar} consists of:
\begin{itemize}
\item a set of \emph{expression kinds};
\item a set of \emph{constructors}, each with an associated \emph{constructor kind} of the form
\begin{equation}
\label{eq:conkind}
 ((A_{11}, \ldots, A_{1r_1}) B_1, \ldots, (A_{m1}, \ldots, A_{mr_m}) B_m) C
\end{equation}
where each $A_{ij}$, $B_i$ and $C$ is an expression kind.
\item a binary relation of \emph{parenthood} on the set of expression kinds.
\end{itemize}

A constructor $c$ of kind (\ref{eq:conkind}) is a constructor that takes $m$ arguments of kind $B_1$, \ldots, $B_m$, and binds $r_i$ variables in its $i$th argument of kind $A_{ij}$,
producing an expression of kind $C$.  We write this expression as

\begin{equation}
\label{eq:expression}
c([x_{11}, \ldots, x_{1r_1}]E_1, \ldots, [x_{m1}, \ldots, x_{mr_m}]E_m) \enspace .
\end{equation}

The subexpressions of the form $[x_{i1}, \ldots, x_{ir_i}]E_i$ shall be called \emph{abstractions}, and the pieces of syntax of the form $(A_{i1}, \ldots, A_{ij})B_i$ that occur in constructor kinds shall be called \emph{abstraction kinds}.

\begin{code}
mutual
  data KindClass (ExpressionKind : Set) : Set where
    -Expression  : KindClass ExpressionKind
    -Abstraction : KindClass ExpressionKind
    -Constructor : ExpressionKind → KindClass ExpressionKind

  data Kind (ExpressionKind : Set) : KindClass ExpressionKind → Set where
    base : ExpressionKind → Kind ExpressionKind -Expression
    out  : ExpressionKind → Kind ExpressionKind -Abstraction
    Π    : ExpressionKind → Kind ExpressionKind -Abstraction → Kind ExpressionKind -Abstraction
    out₂ : ∀ {K} → Kind ExpressionKind (-Constructor K)
    Π₂   : ∀ {K} → Kind ExpressionKind -Abstraction → Kind ExpressionKind (-Constructor K) → Kind ExpressionKind (-Constructor K)

AbstractionKind : Set → Set
AbstractionKind ExpressionKind = Kind ExpressionKind -Abstraction

ConstructorKind : ∀ {ExpressionKind} → ExpressionKind → Set
ConstructorKind {ExpressionKind} K = Kind ExpressionKind (-Constructor K)

record Taxonomy : Set₁ where
  field
    VarKind : Set
    NonVarKind : Set

  data ExpressionKind : Set where
    varKind : VarKind → ExpressionKind
    nonVarKind : NonVarKind → ExpressionKind

record ToGrammar (T : Taxonomy) : Set₁ where
  open Taxonomy T
  field
    Constructor    : ∀ {K : ExpressionKind} → ConstructorKind K → Set
    parent         : VarKind → ExpressionKind
\end{code}

An \emph{alphabet} $V = \{ V_E \}_E$ consists of a set $V_E$ of \emph{variables} of kind $E$ for each expression kind $E$..  The \emph{expressions}
of kind $E$ over the alphabet $V$ are defined inductively by:
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
  data Alphabet : Set where
    ∅ : Alphabet
    _,_ : Alphabet → VarKind → Alphabet

  data Var : Alphabet → VarKind → Set where
    x₀ : ∀ {V} {K} → Var (V , K) K
    ↑ : ∀ {V} {K} {L} → Var V L → Var (V , K) L

  Extend : Alphabet → VarKind → FinSet → Alphabet
  Extend A K ∅ = A
  Extend A K (Lift F) = Extend A K F , K

  data Expression' (V : Alphabet) : ∀ C → Kind ExpressionKind C → Set where
    var : ∀ {K} → Var V K → Expression' V -Expression (base (varKind K))
    app : ∀ {K} {C : ConstructorKind K} → Constructor C → Expression' V (-Constructor K) C → Expression' V -Expression (base K)
    out : ∀ {K} → Expression' V -Expression (base K) → Expression' V -Abstraction (out K)
    Λ   : ∀ {K} {A} → Expression' (V , K) -Abstraction A → Expression' V -Abstraction (Π (varKind K) A)
    out₂ : ∀ {K} → Expression' V (-Constructor K) out₂
    app₂ : ∀ {K} {A} {C} → Expression' V -Abstraction A → Expression' V (-Constructor K) C → Expression' V (-Constructor K) (Π₂ A C)

  Expression'' : Alphabet → ExpressionKind → Set
  Expression'' V K = Expression' V -Expression (base K)

  Body' : Alphabet → ∀ K → ConstructorKind K → Set
  Body' V K C = Expression' V (-Constructor K) C

  Abstraction' : Alphabet → AbstractionKind ExpressionKind → Set
  Abstraction' V K = Expression' V -Abstraction K
\end{code}

Given alphabets $U$, $V$, and a function $\rho$ that maps every variable in $U$ of kind $K$ to a variable in $V$ of kind $K$,
we denote by $E \{ \rho \}$ the result of \emph{replacing} every variable $x$ in $E$ with $\rho(x)$.

\begin{code}
  Rep : Alphabet → Alphabet → Set
  Rep U V = ∀ K → Var U K → Var V K

  _∼R_ : ∀ {U} {V} → Rep U V → Rep U V → Set
  ρ ∼R ρ' = ∀ {K} x → ρ K x ≡ ρ' K x
\end{code}

The alphabets and replacements form a category.

\begin{code}
  idRep : ∀ V → Rep V V
  idRep _ _ x = x

  infixl 75 _•R_
  _•R_ : ∀ {U} {V} {W} → Rep V W → Rep U V → Rep U W
  (ρ' •R ρ) K x = ρ' K (ρ K x)

  --We choose not to prove the category axioms, as they hold up to judgemental equality.
\end{code}

Given a replacement $\rho : U \rightarrow V$, we can `lift´ this to a replacement $(\rho , K) : (U , K) \rightarrow (V , K)$.
Under this operation, the mapping $(- , K)$ becomes an endofunctor on the category of alphabets and replacements.

\begin{code}
  Rep↑ : ∀ {U} {V} {K} → Rep U V → Rep (U , K) (V , K)
  Rep↑ _ _ x₀ = x₀
  Rep↑ ρ K (↑ x) = ↑ (ρ K x)

  Rep↑-wd : ∀ {U} {V} {K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → Rep↑ {K = K} ρ ∼R Rep↑ ρ'
  Rep↑-wd ρ-is-ρ' x₀ = ref
  Rep↑-wd ρ-is-ρ' (↑ x) = wd ↑ (ρ-is-ρ' x)

  Rep↑-id : ∀ {V} {K} → Rep↑ (idRep V) ∼R idRep (V , K)
  Rep↑-id x₀ = ref
  Rep↑-id (↑ _) = ref

  Rep↑-comp : ∀ {U} {V} {W} {K} {ρ' : Rep V W} {ρ : Rep U V} → Rep↑ {K = K} (ρ' •R ρ) ∼R Rep↑ ρ' •R Rep↑ ρ
  Rep↑-comp x₀ = ref
  Rep↑-comp (↑ _) = ref
\end{code}

Finally, we can define $E \langle \rho \rangle$, the result of replacing each variable $x$ in $E$ with $\rho(x)$.
Under this operation, the mapping $\mathsf{Expression}\ -\ K$ becomes a functor from the category of
alphabets and replacements to the category of sets.

\begin{code}
  rep : ∀ {U} {V} {C} {K} → Expression' U C K → Rep U V → Expression' V C K
  rep (var x) ρ = var (ρ _ x)
  rep (app c EE) ρ = app c (rep EE ρ)
  rep (out E) ρ = out (rep E ρ)
  rep (Λ E) ρ = Λ (rep E (Rep↑ ρ))
  rep out₂ _ = out₂
  rep (app₂ E F) ρ = app₂ (rep E ρ) (rep F ρ)

  mutual
    infix 60 _〈_〉
    _〈_〉 : ∀ {U} {V} {K} → Expression'' U K → Rep U V → Expression'' V K
    var x 〈 ρ 〉 = var (ρ _ x)
    (app c EE) 〈 ρ 〉 = app c (EE 〈 ρ 〉B)
  
    infix 60 _〈_〉B
    _〈_〉B : ∀ {U} {V} {K} {C : ConstructorKind K} → Expression' U (-Constructor K) C → Rep U V → Expression' V (-Constructor K) C
    out₂ 〈 ρ 〉B = out₂
    (app₂ A EE) 〈 ρ 〉B = app₂ (A 〈 ρ 〉A) (EE 〈 ρ 〉B)

    infix 60 _〈_〉A
    _〈_〉A : ∀ {U} {V} {A} → Expression' U -Abstraction A → Rep U V → Expression' V -Abstraction A
    out E 〈 ρ 〉A = out (E 〈 ρ 〉)
    Λ A 〈 ρ 〉A = Λ (A 〈 Rep↑ ρ 〉A)

  mutual
    rep-wd : ∀ {U} {V} {K} {E : Expression'' U K} {ρ : Rep U V} {ρ'} → ρ ∼R ρ' → rep E ρ ≡ rep E ρ'
    rep-wd {E = var x} ρ-is-ρ' = wd var (ρ-is-ρ' x)
    rep-wd {E = app c EE} ρ-is-ρ' = wd (app c) (rep-wdB ρ-is-ρ')

    rep-wdB : ∀ {U} {V} {K} {C : ConstructorKind K} {EE : Expression' U (-Constructor K) C} {ρ ρ' : Rep U V} → ρ ∼R ρ' → rep EE ρ ≡ rep EE ρ'
    rep-wdB {U} {V} .{K} {out₂ {K}} {out₂} ρ-is-ρ' = ref
    rep-wdB {U} {V} {K} {Π₂ A C} {app₂ A' EE} ρ-is-ρ' = wd2 app₂ (rep-wdA ρ-is-ρ') (rep-wdB ρ-is-ρ')

    rep-wdA : ∀ {U} {V} {A} {E : Expression' U -Abstraction A} {ρ ρ' : Rep U V} → ρ ∼R ρ' → rep E ρ ≡ rep E ρ'
    rep-wdA {U} {V} {out K} {out E} ρ-is-ρ' = wd out (rep-wd ρ-is-ρ')
    rep-wdA {U} {V} .{Π (varKind _) _} {Λ E} ρ-is-ρ' = wd Λ (rep-wdA (Rep↑-wd ρ-is-ρ'))

  mutual
    rep-id : ∀ {V} {K} {E : Expression'' V K} → rep E (idRep V) ≡ E
    rep-id {E = var _} = ref
    rep-id {E = app c _} = wd (app c) rep-idB

    rep-idB : ∀ {V} {K} {C : ConstructorKind K} {EE : Expression' V (-Constructor K) C} → rep EE (idRep V) ≡ EE
    rep-idB {EE = out₂} = ref
    rep-idB {EE = app₂ _ _} = wd2 app₂ rep-idA rep-idB

    rep-idA : ∀ {V} {K} {A : Expression' V -Abstraction K} → rep A (idRep V) ≡ A
    rep-idA {A = out _} = wd out rep-id
    rep-idA {A = Λ _} = wd Λ (trans (rep-wdA Rep↑-id) rep-idA)

  mutual
    rep-comp : ∀ {U} {V} {W} {K} {ρ : Rep U V} {ρ' : Rep V W} {E : Expression'' U K} → rep E (ρ' •R ρ) ≡ rep (rep E ρ) ρ'
    rep-comp {E = var _} = ref
    rep-comp {E = app c _} = wd (app c) rep-compB

    rep-compB : ∀ {U} {V} {W} {K} {C : ConstructorKind K} {ρ : Rep U V} {ρ' : Rep V W} {EE : Expression' U (-Constructor K) C} → rep EE (ρ' •R ρ) ≡ rep (rep EE ρ) ρ'
    rep-compB {EE = out₂} = ref
    rep-compB {U} {V} {W} {K} {Π₂ L C} {ρ} {ρ'} {app₂ A EE} = wd2 app₂ rep-compA rep-compB

    rep-compA : ∀ {U} {V} {W} {K} {ρ : Rep U V} {ρ' : Rep V W} {A : Expression' U -Abstraction K} → rep A (ρ' •R ρ) ≡ rep (rep A ρ) ρ'
    rep-compA {A = out _} = wd out rep-comp
    rep-compA {U} {V} {W} .{Π (varKind K) L} {ρ} {ρ'} {Λ {K} {L} A} = wd Λ (trans (rep-wdA Rep↑-comp) rep-compA)
\end{code}

This provides us with the canonical mapping from an expression over $V$ to an expression over $(V , K)$:
\begin{code}
  lift : ∀ {V} {K} {L} → Expression'' V L → Expression'' (V , K) L
  lift E = rep E (λ _ → ↑)
\end{code}

A \emph{substitution} $\sigma$ from alphabet $U$ to alphabet $V$, $\sigma : U \Rightarrow V$, is a function $\sigma$ that maps every variable $x$ of kind $K$ in $U$ to an
\emph{expression} $\sigma(x)$ of kind $K$ over $V$.  Then, given an expression $E$ of kind $K$ over $U$, we write $E[\sigma]$ for
the result of substituting $\sigma(x)$ for $x$ for each variable in $E$, avoiding capture.

\begin{code}
  Sub : Alphabet → Alphabet → Set
  Sub U V = ∀ K → Var U K → Expression'' V (varKind K)

  _∼_ : ∀ {U} {V} → Sub U V → Sub U V → Set
  σ ∼ τ = ∀ K x → σ K x ≡ τ K x
\end{code}

The \emph{identity} substitution $\id{V} : V \rightarrow V$ is defined as follows.

\begin{code}
  idSub : ∀ {V} → Sub V V
  idSub _ x = var x
\end{code}

Given $\sigma : U \rightarrow V$ and an expression $E$ over $U$, we want to define the expression $E[\sigma]$ over $V$,
the result of applying the substitution $\sigma$ to $M$.
Only after this will we be able to define the composition of two substitutions.  However, there is some work we need to do before we are able to do this.

We can define the composition of a substitution and a replacement as follows
\begin{code}
  infix 75 _•₁_
  _•₁_ : ∀ {U} {V} {W} → Rep V W → Sub U V → Sub U W
  (ρ •₁ σ) K x = rep (σ K x) ρ

  infix 75 _•₂_
  _•₂_ : ∀ {U} {V} {W} → Sub V W → Rep U V → Sub U W
  (σ •₂ ρ) K x = σ K (ρ K x)
\end{code}

Given a substitution $\sigma : U \Rightarrow V$,  define a substitution $
(\sigma , K) : (U , K) \Rightarrow (V , K)$ as follows.

\begin{code}
  Sub↑ : ∀ {U} {V} {K} → Sub U V → Sub (U , K) (V , K)
  Sub↑ _ _ x₀ = var x₀
  Sub↑ σ K (↑ x) = lift (σ K x)

  Sub↑-wd : ∀ {U} {V} {K} {σ σ' : Sub U V} → σ ∼ σ' → Sub↑ {K = K} σ ∼ Sub↑ σ'
  Sub↑-wd {K = K} σ-is-σ' ._ x₀ = ref
  Sub↑-wd σ-is-σ' L (↑ x) = wd lift (σ-is-σ' L x)
\end{code}

\begin{lemma}
The operations we have defined satisfy the following properties.
\begin{enumerate}
\item
$(\id{V},K) = \id{(V,K)}$
\item
$(\rho \bullet_1 \sigma, K) = (\rho , K) \bullet_1 (\sigma , K)$
\item
$(\sigma \bullet_2 \rho, K) = (\sigma , K) \bullet_2 (\rho , K)$
\end{enumerate}
\end{lemma}

\begin{code}
  Sub↑-id : ∀ {V} {K} → Sub↑ {V} {V} {K} idSub ∼ idSub
  Sub↑-id {K = K} ._ x₀ = ref
  Sub↑-id _ (↑ _) = ref

  Sub↑-comp₁ : ∀ {U} {V} {W} {K} {ρ : Rep V W} {σ : Sub U V} → Sub↑ (ρ •₁ σ) ∼ Rep↑ ρ •₁ Sub↑ σ
  Sub↑-comp₁ {K = K} ._ x₀ = ref
  Sub↑-comp₁ {U} {V} {W} {K} {ρ} {σ} L (↑ x) = let open Equational-Reasoning (Expression'' (W , K) (varKind L)) in 
    ∵ lift (rep (σ L x) ρ)
    ≡ rep (σ L x) (λ _ x → ↑ (ρ _ x)) [[ rep-comp {E = σ L x} ]]
    ≡ rep (lift (σ L x)) (Rep↑ ρ)     [ rep-comp ]

  Sub↑-comp₂ : ∀ {U} {V} {W} {K} {σ : Sub V W} {ρ : Rep U V} → Sub↑ {K = K} (σ •₂ ρ) ∼ Sub↑ σ •₂ Rep↑ ρ
  Sub↑-comp₂ {K = K} ._ x₀ = ref
  Sub↑-comp₂ L (↑ x) = ref
\end{code}

We can now define the result of applying a substitution $\sigma$ to an expression $E$,
which we denote $E [ \sigma ]$.

\begin{code}
  mutual
    infix 60 _⟦_⟧
    _⟦_⟧ : ∀ {U} {V} {K} → Expression'' U K → Sub U V → Expression'' V K
    (var x) ⟦ σ ⟧ = σ _ x
    (app c EE) ⟦ σ ⟧ = app c (EE ⟦ σ ⟧B)

    infix 60 _⟦_⟧B
    _⟦_⟧B : ∀ {U} {V} {K} {C : ConstructorKind K} → Expression' U (-Constructor K) C → Sub U V → Expression' V (-Constructor K) C
    out₂ ⟦ σ ⟧B = out₂
    (app₂ A EE) ⟦ σ ⟧B = app₂ (A ⟦ σ ⟧A) (EE ⟦ σ ⟧B)

    infix 60 _⟦_⟧A
    _⟦_⟧A : ∀ {U} {V} {A} → Expression' U -Abstraction A → Sub U V → Expression' V -Abstraction A
    (out E) ⟦ σ ⟧A = out (E ⟦ σ ⟧)
    (Λ A) ⟦ σ ⟧A = Λ (A ⟦ Sub↑ σ ⟧A)

  mutual
    sub-wd : ∀ {U} {V} {K} {E : Expression'' U K} {σ σ' : Sub U V} → σ ∼ σ' → E ⟦ σ ⟧ ≡ E ⟦ σ' ⟧
    sub-wd {E = var x} σ-is-σ' = σ-is-σ' _ x
    sub-wd {U} {V} {K} {app c EE} σ-is-σ' = wd (app c) (sub-wdB σ-is-σ')

    sub-wdB : ∀ {U} {V} {K} {C : ConstructorKind K} {EE : Expression' U (-Constructor K) C} {σ σ' : Sub U V} → σ ∼ σ' → EE ⟦ σ ⟧B ≡ EE ⟦ σ' ⟧B
    sub-wdB {EE = out₂} σ-is-σ' = ref
    sub-wdB {EE = app₂ A EE} σ-is-σ' = wd2 app₂ (sub-wdA σ-is-σ') (sub-wdB σ-is-σ')

    sub-wdA : ∀ {U} {V} {K} {A : Expression' U -Abstraction K} {σ σ' : Sub U V} → σ ∼ σ' → A ⟦ σ ⟧A ≡ A ⟦ σ' ⟧A
    sub-wdA {A = out E} σ-is-σ' = wd out (sub-wd {E = E} σ-is-σ')
    sub-wdA {U} {V} .{Π (varKind K) L} {Λ {K} {L} A} σ-is-σ' = wd Λ (sub-wdA (Sub↑-wd σ-is-σ'))
\end{code}

\begin{lemma}
$ $
\begin{enumerate}
\item
$M[\id{V}] \equiv M$
\item
$M[\rho \bullet_1 \sigma] \equiv M [ \sigma ] \langle \rho \rangle$
\item
$M[\sigma \bullet_2 \rho] \equiv M \langle \rho \rangle [ \sigma ]$
\end{enumerate}
\end{lemma}

\begin{code}
  mutual
    subid : ∀ {V} {K} {E : Expression'' V K} → E ⟦ idSub ⟧ ≡ E
    subid {E = var _} = ref
    subid {V} {K} {app c _} = wd (app c) subidB

    subidB : ∀ {V} {K} {C : ConstructorKind K} {EE : Expression' V (-Constructor K) C} → EE ⟦ idSub ⟧B ≡ EE
    subidB {EE = out₂} = ref
    subidB {EE = app₂ _ _} = wd2 app₂ subidA subidB

    subidA : ∀ {V} {K} {A : Expression' V -Abstraction K} → A ⟦ idSub ⟧A ≡ A
    subidA {A = out _} = wd out subid
    subidA {A = Λ _} = wd Λ (trans (sub-wdA Sub↑-id) subidA)

  mutual
    sub-comp₁ : ∀ {U} {V} {W} {K} {E : Expression'' U K} {ρ : Rep V W} {σ : Sub U V} →
      E ⟦ ρ •₁ σ ⟧ ≡ rep (E ⟦ σ ⟧) ρ
    sub-comp₁ {E = var _} = ref
    sub-comp₁ {E = app c _} = wd (app c) sub-comp₁B

    sub-comp₁B : ∀ {U} {V} {W} {K} {C : ConstructorKind K} {EE : Expression' U (-Constructor K) C} {ρ : Rep V W} {σ : Sub U V} →
      EE ⟦ ρ •₁ σ ⟧B ≡ rep (EE ⟦ σ ⟧B) ρ
    sub-comp₁B {EE = out₂} = ref
    sub-comp₁B {U} {V} {W} {K} {(Π₂ L C)} {app₂ A EE} = wd2 app₂ sub-comp₁A sub-comp₁B

    sub-comp₁A : ∀ {U} {V} {W} {K} {A : Expression' U -Abstraction K} {ρ : Rep V W} {σ : Sub U V} →
      A ⟦ ρ •₁ σ ⟧A ≡ rep (A ⟦ σ ⟧A) ρ
    sub-comp₁A {A = out E} = wd out (sub-comp₁ {E = E})
    sub-comp₁A {U} {V} {W} .{(Π (varKind K) L)} {Λ {K} {L} A} = wd Λ (trans (sub-wdA Sub↑-comp₁) sub-comp₁A)

  mutual
    sub-comp₂ : ∀ {U} {V} {W} {K} {E : Expression'' U K} {σ : Sub V W} {ρ : Rep U V} → E ⟦ σ •₂ ρ ⟧ ≡ (rep E ρ) ⟦ σ ⟧
    sub-comp₂ {E = var _} = ref
    sub-comp₂ {U} {V} {W} {K} {app c EE} = wd (app c) sub-comp₂B

    sub-comp₂B : ∀ {U} {V} {W} {K} {C : ConstructorKind K} {EE : Expression' U (-Constructor K) C}
      {σ : Sub V W} {ρ : Rep U V} → EE ⟦ σ •₂ ρ ⟧B ≡ (rep EE ρ) ⟦ σ ⟧B
    sub-comp₂B {EE = out₂} = ref
    sub-comp₂B {U} {V} {W} {K} {Π₂ L C} {app₂ A EE} = wd2 app₂ sub-comp₂A sub-comp₂B

    sub-comp₂A : ∀ {U} {V} {W} {K} {A : Expression' U -Abstraction K} {σ : Sub V W} {ρ : Rep U V} → A ⟦ σ •₂ ρ ⟧A ≡ (rep A ρ) ⟦ σ ⟧A
    sub-comp₂A {A = out E} = wd out (sub-comp₂ {E = E})
    sub-comp₂A {U} {V} {W} .{Π (varKind K) L} {Λ {K} {L} A} = wd Λ (trans (sub-wdA Sub↑-comp₂) sub-comp₂A)
\end{code}

We define the composition of two substitutions, as follows.

\begin{code}
  infix 75 _•_
  _•_ : ∀ {U} {V} {W} → Sub V W → Sub U V → Sub U W
  (σ • ρ) K x = ρ K x ⟦ σ ⟧
\end{code}

\begin{lemma}
  Let $\sigma : V \Rightarrow W$ and $\rho : U \Rightarrow V$.
  \begin{enumerate}
  \item $(\sigma \bullet \rho, K) \sim (\sigma , K) \bullet (\rho , K)$
  \item $E [ \sigma \bullet \rho ] \equiv E [ \rho ] [ \sigma ]$
  \end{enumerate}
\end{lemma}

\begin{code}
  Sub↑-comp : ∀ {U} {V} {W} {ρ : Sub U V} {σ : Sub V W} {K} →
    Sub↑ {K = K} (σ • ρ) ∼ Sub↑ σ • Sub↑ ρ
  Sub↑-comp _ x₀ = ref
  Sub↑-comp {W = W} {ρ = ρ} {σ = σ} {K = K} L (↑ x) =
    let open Equational-Reasoning (Expression'' (W , K) (varKind L)) in 
      ∵ lift ((ρ L x) ⟦ σ ⟧)
      ≡ ρ L x ⟦ (λ _ → ↑) •₁ σ ⟧  [[ sub-comp₁ {E = ρ L x} ]]
      ≡ (lift (ρ L x)) ⟦ Sub↑ σ ⟧ [ sub-comp₂ {E = ρ L x} ]

  mutual
    sub-compA : ∀ {U} {V} {W} {K} {A : Expression' U -Abstraction K} {σ : Sub V W} {ρ : Sub U V} →
      A ⟦ σ • ρ ⟧A ≡ A ⟦ ρ ⟧A ⟦ σ ⟧A
    sub-compA {A = out E} = wd out (sub-comp {E = E})
    sub-compA {U} {V} {W} .{Π (varKind K) L} {Λ {K} {L} A} {σ} {ρ} = wd Λ (let open Equational-Reasoning (Expression' (W , K) -Abstraction L) in 
      ∵ A ⟦ Sub↑ (σ • ρ) ⟧A
      ≡ A ⟦ Sub↑ σ • Sub↑ ρ ⟧A    [ sub-wdA Sub↑-comp ]
      ≡ A ⟦ Sub↑ ρ ⟧A ⟦ Sub↑ σ ⟧A [ sub-compA ])

    sub-compB : ∀ {U} {V} {W} {K} {C : ConstructorKind K} {EE : Expression' U (-Constructor K) C} {σ : Sub V W} {ρ : Sub U V} →
      EE ⟦ σ • ρ ⟧B ≡ EE ⟦ ρ ⟧B ⟦ σ ⟧B
    sub-compB {EE = out₂} = ref
    sub-compB {U} {V} {W} {K} {(Π₂ L C)} {app₂ A EE} = wd2 app₂ sub-compA sub-compB

    sub-comp : ∀ {U} {V} {W} {K} {E : Expression'' U K} {σ : Sub V W} {ρ : Sub U V} →
      E ⟦ σ • ρ ⟧ ≡ E ⟦ ρ ⟧ ⟦ σ ⟧
    sub-comp {E = var _} = ref
    sub-comp {U} {V} {W} {K} {app c EE} = wd (app c) sub-compB
\end{code}

\begin{lemma}
The alphabets and substitutions form a category under this composition.
\end{lemma}

\begin{code}
  assoc : ∀ {U V W X} {ρ : Sub W X} {σ : Sub V W} {τ : Sub U V} → ρ • (σ • τ) ∼ (ρ • σ) • τ
  assoc {τ = τ} K x = sym (sub-comp {E = τ K x})

  sub-unitl : ∀ {U} {V} {σ : Sub U V} → idSub • σ ∼ σ
  sub-unitl _ _ = subid

  sub-unitr : ∀ {U} {V} {σ : Sub U V} → σ • idSub ∼ σ
  sub-unitr _ _ = ref
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
  Rep↑-is-Sub↑ K x₀ = ref
  Rep↑-is-Sub↑ K₁ (↑ x) = ref

  mutual
    rep-is-sub : ∀ {U} {V} {K} {E : Expression'' U K} {ρ : Rep U V} →
             E 〈 ρ 〉 ≡ E ⟦ (λ K x → var (ρ K x)) ⟧
    rep-is-sub {E = var _} = ref
    rep-is-sub {U} {V} {K} {app c EE} = wd (app c) rep-is-subB

    rep-is-subB : ∀ {U} {V} {K} {C : ConstructorKind K} {EE : Expression' U (-Constructor K) C} {ρ : Rep U V} →
      EE 〈 ρ 〉B ≡ EE ⟦ (λ K x → var (ρ K x)) ⟧B
    rep-is-subB {EE = out₂} = ref
    rep-is-subB {EE = app₂ _ _} = wd2 app₂ rep-is-subA rep-is-subB

    rep-is-subA : ∀ {U} {V} {K} {A : Expression' U -Abstraction K} {ρ : Rep U V} →
      A 〈 ρ 〉A ≡ A ⟦ (λ K x → var (ρ K x)) ⟧A
    rep-is-subA {A = out E} = wd out rep-is-sub
    rep-is-subA {U} {V} .{Π (varKind K) L} {Λ {K} {L} A} {ρ} = wd Λ (let open Equational-Reasoning (Expression' (V , K) -Abstraction L) in 
      ∵ A 〈 Rep↑ ρ 〉A
      ≡ A ⟦ (λ M x → var (Rep↑ ρ M x)) ⟧A [ rep-is-subA ]
      ≡ A ⟦ Sub↑ (λ M x → var (ρ M x)) ⟧A [ sub-wdA Rep↑-is-Sub↑ ])
\end{code}

Let $E$ be an expression of kind $K$ over $V$.  Then we write $[x_0 := E]$ for the following substitution
$(V , K) \Rightarrow V$:

\begin{code}
  x₀:= : ∀ {V} {K} → Expression'' V (varKind K) → Sub (V , K) V
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
  comp₁-botsub : ∀ {U} {V} {K} {E : Expression'' U (varKind K)} {ρ : Rep U V} →
    ρ •₁ (x₀:= E) ∼ (x₀:= (rep E ρ)) •₂ Rep↑ ρ
  comp₁-botsub _ x₀ = ref
  comp₁-botsub _ (↑ _) = ref

  comp-botsub : ∀ {U} {V} {K} {E : Expression'' U (varKind K)} {σ : Sub U V} →
    σ • (x₀:= E) ∼ (x₀:= (E ⟦ σ ⟧)) • Sub↑ σ
  comp-botsub _ x₀ = ref
  comp-botsub {σ = σ} L (↑ x) = trans (sym subid) (sub-comp₂ {E = σ L x})
\end{code}

\section{Contexts}

A \emph{context} has the form $x_1 : A_1, \ldots, x_n : A_n$ where, for each $i$:
\begin{itemize}
\item $x_i$ is a variable of kind $K_i$ distinct from $x_1$, \ldots, $x_{i-1}$;
\item $A_i$ is an expression of some kind $L_i$;
\item $L_i$ is a parent of $K_i$.
\end{itemize}
The \emph{domain} of this context is the alphabet $\{ x_1, \ldots, x_n \}$.

\begin{code}
  data Context (K : VarKind) : Alphabet → Set where
    〈〉 : Context K ∅
    _,_ : ∀ {V} → Context K V → Expression'' V (parent K) → Context K (V , K)

  typeof : ∀ {V} {K} (x : Var V K) (Γ : Context K V) → Expression'' V (parent K)
  typeof x₀ (_ , A) = lift A
  typeof (↑ x) (Γ , _) = lift (typeof x Γ)

  data Context' (A : Alphabet) (K : VarKind) : FinSet → Set where
    〈〉 : Context' A K ∅
    _,_ : ∀ {F} → Context' A K F → Expression'' (Extend A K F) (parent K) → Context' A K (Lift F)

  typeof' : ∀ {A} {K} {F} → El F → Context' A K F → Expression'' (Extend A K F) (parent K)
  typeof' ⊥ (_ , A) = lift A
  typeof' (↑ x) (Γ , _) = lift (typeof' x Γ)

record Grammar : Set₁ where
  field
    taxonomy : Taxonomy
    toGrammar : ToGrammar taxonomy
  open Taxonomy taxonomy public
  open ToGrammar toGrammar public
\end{code}
