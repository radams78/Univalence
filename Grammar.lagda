\section{Grammars}

\begin{code}
module Grammar where

open import Prelims hiding (Rep;_∼_;lift)
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
data AbstractionKind (ExpressionKind : Set) : Set where
  out : ExpressionKind → AbstractionKind ExpressionKind
  Π   : ExpressionKind → AbstractionKind ExpressionKind → AbstractionKind ExpressionKind

data ConstructorKind {ExpressionKind : Set} (K : ExpressionKind) : Set where
  out : ConstructorKind K
  Π   : AbstractionKind ExpressionKind → ConstructorKind K → ConstructorKind K

record Grammar : Set₁ where
  field
    ExpressionKind : Set
    Constructor    : ∀ {K : ExpressionKind} → ConstructorKind K → Set
    parent         : ExpressionKind → ExpressionKind → Set
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
    _,_ : Alphabet → ExpressionKind → Alphabet

  data Var : Alphabet → ExpressionKind → Set where
    x₀ : ∀ {V} {K} → Var (V , K) K
    ↑ : ∀ {V} {K} {L} → Var V L → Var (V , K) L

  mutual
    data Expression (V : Alphabet) (K : ExpressionKind) : Set where
      var : Var V K → Expression V K
      app : ∀ {C : ConstructorKind K} → Constructor C → Body V C → Expression V K

    data Body (V : Alphabet) {K : ExpressionKind} : ConstructorKind K → Set where
      out : Body V out
      app : ∀ {A} {C} → Abstraction V A → Body V C → Body V (Π A C)

    data Abstraction (V : Alphabet) : AbstractionKind ExpressionKind → Set where
      out : ∀ {K} → Expression V K → Abstraction V (out K)
      Λ   : ∀ {K} {A} → Abstraction (V , K) A → Abstraction V (Π K A)
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
  mutual
    infix 60 _〈_〉
    _〈_〉 : ∀ {U} {V} {K} → Expression U K → Rep U V → Expression V K
    var x 〈 ρ 〉 = var (ρ _ x)
    (app c EE) 〈 ρ 〉 = app c (EE 〈 ρ 〉B)
  
    infix 60 _〈_〉B
    _〈_〉B : ∀ {U} {V} {K} {C : ConstructorKind K} → Body U C → Rep U V → Body V C
    out 〈 ρ 〉B = out
    (app A EE) 〈 ρ 〉B = app (A 〈 ρ 〉A) (EE 〈 ρ 〉B)

    infix 60 _〈_〉A
    _〈_〉A : ∀ {U} {V} {A} → Abstraction U A → Rep U V → Abstraction V A
    out E 〈 ρ 〉A = out (E 〈 ρ 〉)
    Λ A 〈 ρ 〉A = Λ (A 〈 Rep↑ ρ 〉A)

  mutual
    rep-wd : ∀ {U} {V} {K} {E : Expression U K} {ρ : Rep U V} {ρ'} → ρ ∼R ρ' → E 〈 ρ 〉 ≡ E 〈 ρ' 〉
    rep-wd {U} {V} {K} {var x} ρ-is-ρ' = wd var (ρ-is-ρ' x)
    rep-wd {U} {V} {K} {app c EE} ρ-is-ρ' = wd (app c) (rep-wdB ρ-is-ρ')

    rep-wdB : ∀ {U} {V} {K} {C : ConstructorKind K} {EE : Body U C} {ρ ρ' : Rep U V} → ρ ∼R ρ' → EE 〈 ρ 〉B ≡ EE 〈 ρ' 〉B
    rep-wdB {U} {V} {K} {out} {out} ρ-is-ρ' = ref
    rep-wdB {U} {V} {K} {Π A C} {app A' EE} ρ-is-ρ' = wd2 app (rep-wdA ρ-is-ρ') (rep-wdB ρ-is-ρ')

    rep-wdA : ∀ {U} {V} {A} {E : Abstraction U A} {ρ ρ' : Rep U V} → ρ ∼R ρ' → E 〈 ρ 〉A ≡ E 〈 ρ' 〉A
    rep-wdA {U} {V} {out K} {out E} ρ-is-ρ' = wd out (rep-wd ρ-is-ρ')
    rep-wdA {U} {V} {Π K A} {Λ E} ρ-is-ρ' = wd Λ (rep-wdA (Rep↑-wd ρ-is-ρ'))

  mutual
    rep-id : ∀ {V} {K} {E : Expression V K} → E 〈 idRep V 〉 ≡ E
    rep-id {E = var _} = ref
    rep-id {E = app c _} = wd (app c) rep-idB

    rep-idB : ∀ {V} {K} {C : ConstructorKind K} {EE : Body V C} → EE 〈 idRep V 〉B ≡ EE
    rep-idB {EE = out} = ref
    rep-idB {EE = app _ _} = wd2 app rep-idA rep-idB

    rep-idA : ∀ {V} {K} {A : Abstraction V K} → A 〈 idRep V 〉A ≡ A
    rep-idA {A = out _} = wd out rep-id
    rep-idA {A = Λ _} = wd Λ (trans (rep-wdA Rep↑-id) rep-idA)

  mutual
    rep-comp : ∀ {U} {V} {W} {K} {ρ : Rep U V} {ρ' : Rep V W} {E : Expression U K} → E 〈 ρ' •R ρ 〉 ≡ E 〈 ρ 〉 〈 ρ' 〉
    rep-comp {E = var _} = ref
    rep-comp {E = app c _} = wd (app c) rep-compB

    rep-compB : ∀ {U} {V} {W} {K} {C : ConstructorKind K} {ρ : Rep U V} {ρ' : Rep V W} {EE : Body U C} → EE 〈 ρ' •R ρ 〉B ≡ EE 〈 ρ 〉B 〈 ρ' 〉B
    rep-compB {EE = out} = ref
    rep-compB {U} {V} {W} {K} {Π L C} {ρ} {ρ'} {app A EE} = wd2 app rep-compA rep-compB

    rep-compA : ∀ {U} {V} {W} {K} {ρ : Rep U V} {ρ' : Rep V W} {A : Abstraction U K} → A 〈 ρ' •R ρ 〉A ≡ A 〈 ρ 〉A 〈 ρ' 〉A
    rep-compA {A = out _} = wd out rep-comp
    rep-compA {U} {V} {W} {Π K L} {ρ} {ρ'} {Λ A} = wd Λ (trans (rep-wdA Rep↑-comp) rep-compA)
\end{code}

This provides us with the canonical mapping from an expression over $V$ to an expression over $(V , K)$:
\begin{code}
  lift : ∀ {V} {K} {L} → Expression V L → Expression (V , K) L
  lift E = E 〈 (λ _ → ↑) 〉
\end{code}

A \emph{substitution} $\sigma$ from alphabet $U$ to alphabet $V$, $\sigma : U \Rightarrow V$, is a function $\sigma$ that maps every variable $x$ of kind $K$ in $U$ to an
\emph{expression} $\sigma(x)$ of kind $K$ over $V$.  Then, given an expression $E$ of kind $K$ over $U$, we write $E[\sigma]$ for
the result of substituting $\sigma(x)$ for $x$ for each variable in $E$, avoiding capture.

\begin{code}
  Sub : Alphabet → Alphabet → Set
  Sub U V = ∀ K → Var U K → Expression V K

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
  (ρ •₁ σ) K x = σ K x 〈 ρ 〉

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
  Sub↑-wd {K = K} σ-is-σ' .K x₀ = ref
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
  Sub↑-id : ∀ {V} {K} → Sub↑ {V} idSub ∼ idSub
  Sub↑-id {K = K} .K x₀ = ref
  Sub↑-id _ (↑ _) = ref

  Sub↑-comp₁ : ∀ {U} {V} {W} {K} {ρ : Rep V W} {σ : Sub U V} → Sub↑ (ρ •₁ σ) ∼ Rep↑ ρ •₁ Sub↑ σ
  Sub↑-comp₁ {K = K} .K x₀ = ref
  Sub↑-comp₁ {U} {V} {W} {K} {ρ} {σ} L (↑ x) = let open Equational-Reasoning (Expression (W , K) L) in 
    ∵ lift (σ L x 〈 ρ 〉)
    ≡ σ L x 〈 (λ _ x → ↑ (ρ _ x)) 〉 [[ rep-comp ]]
    ≡ (lift (σ L x)) 〈 Rep↑ ρ 〉     [ rep-comp ]

  Sub↑-comp₂ : ∀ {U} {V} {W} {K} {σ : Sub V W} {ρ : Rep U V} → Sub↑ (σ •₂ ρ) ∼ Sub↑ σ •₂ Rep↑ ρ
  Sub↑-comp₂ {K = K} .K x₀ = ref
  Sub↑-comp₂ L (↑ x) = ref
\end{code}

We can now define the result of applying a substitution $\sigma$ to an expression $E$,
which we denote $E [ \sigma ]$.

\begin{code}
  mutual
    infix 60 _⟦_⟧
    _⟦_⟧ : ∀ {U} {V} {K} → Expression U K → Sub U V → Expression V K
    (var x) ⟦ σ ⟧ = σ _ x
    (app c EE) ⟦ σ ⟧ = app c (EE ⟦ σ ⟧B)

    infix 60 _⟦_⟧B
    _⟦_⟧B : ∀ {U} {V} {K} {C : ConstructorKind K} → Body U C → Sub U V → Body V C
    out ⟦ σ ⟧B = out
    (app A EE) ⟦ σ ⟧B = app (A ⟦ σ ⟧A) (EE ⟦ σ ⟧B)

    infix 60 _⟦_⟧A
    _⟦_⟧A : ∀ {U} {V} {A} → Abstraction U A → Sub U V → Abstraction V A
    (out E) ⟦ σ ⟧A = out (E ⟦ σ ⟧)
    (Λ A) ⟦ σ ⟧A = Λ (A ⟦ Sub↑ σ ⟧A)

  mutual
    sub-wd : ∀ {U} {V} {K} {E : Expression U K} {σ σ' : Sub U V} → σ ∼ σ' → E ⟦ σ ⟧ ≡ E ⟦ σ' ⟧
    sub-wd {E = var x} σ-is-σ' = σ-is-σ' _ x
    sub-wd {U} {V} {K} {app c EE} σ-is-σ' = wd (app c) (sub-wdB σ-is-σ')

    sub-wdB : ∀ {U} {V} {K} {C : ConstructorKind K} {EE : Body U C} {σ σ' : Sub U V} → σ ∼ σ' → EE ⟦ σ ⟧B ≡ EE ⟦ σ' ⟧B
    sub-wdB {EE = out} σ-is-σ' = ref
    sub-wdB {EE = app A EE} σ-is-σ' = wd2 app (sub-wdA σ-is-σ') (sub-wdB σ-is-σ')

    sub-wdA : ∀ {U} {V} {K} {A : Abstraction U K} {σ σ' : Sub U V} → σ ∼ σ' → A ⟦ σ ⟧A ≡ A ⟦ σ' ⟧A
    sub-wdA {A = out E} σ-is-σ' = wd out (sub-wd {E = E} σ-is-σ')
    sub-wdA {U} {V} {Π K L} {Λ A} σ-is-σ' = wd Λ (sub-wdA (Sub↑-wd σ-is-σ'))
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
    subid : ∀ {V} {K} {E : Expression V K} → E ⟦ idSub ⟧ ≡ E
    subid {E = var _} = ref
    subid {V} {K} {app c _} = wd (app c) subidB

    subidB : ∀ {V} {K} {C : ConstructorKind K} {EE : Body V C} → EE ⟦ idSub ⟧B ≡ EE
    subidB {EE = out} = ref
    subidB {EE = app _ _} = wd2 app subidA subidB

    subidA : ∀ {V} {K} {A : Abstraction V K} → A ⟦ idSub ⟧A ≡ A
    subidA {A = out _} = wd out subid
    subidA {A = Λ _} = wd Λ (trans (sub-wdA Sub↑-id) subidA)

  mutual
    sub-comp₁ : ∀ {U} {V} {W} {K} {E : Expression U K} {ρ : Rep V W} {σ : Sub U V} →
      E ⟦ ρ •₁ σ ⟧ ≡ E ⟦ σ ⟧ 〈 ρ 〉
    sub-comp₁ {E = var _} = ref
    sub-comp₁ {E = app c _} = wd (app c) sub-comp₁B

    sub-comp₁B : ∀ {U} {V} {W} {K} {C : ConstructorKind K} {EE : Body U C} {ρ : Rep V W} {σ : Sub U V} →
      EE ⟦ ρ •₁ σ ⟧B ≡ EE ⟦ σ ⟧B 〈 ρ 〉B
    sub-comp₁B {EE = out} = ref
    sub-comp₁B {U} {V} {W} {K} {(Π L C)} {app A EE} = wd2 app sub-comp₁A sub-comp₁B

    sub-comp₁A : ∀ {U} {V} {W} {K} {A : Abstraction U K} {ρ : Rep V W} {σ : Sub U V} →
      A ⟦ ρ •₁ σ ⟧A ≡ A ⟦ σ ⟧A 〈 ρ 〉A
    sub-comp₁A {A = out E} = wd out (sub-comp₁ {E = E})
    sub-comp₁A {U} {V} {W} {(Π K L)} {Λ A} = wd Λ (trans (sub-wdA Sub↑-comp₁) sub-comp₁A)

  mutual
    sub-comp₂ : ∀ {U} {V} {W} {K} {E : Expression U K} {σ : Sub V W} {ρ : Rep U V} → E ⟦ σ •₂ ρ ⟧ ≡ E 〈 ρ 〉 ⟦ σ ⟧
    sub-comp₂ {E = var _} = ref
    sub-comp₂ {U} {V} {W} {K} {app c EE} = wd (app c) sub-comp₂B

    sub-comp₂B : ∀ {U} {V} {W} {K} {C : ConstructorKind K} {EE : Body U C}
      {σ : Sub V W} {ρ : Rep U V} → EE ⟦ σ •₂ ρ ⟧B ≡ EE 〈 ρ 〉B ⟦ σ ⟧B
    sub-comp₂B {EE = out} = ref
    sub-comp₂B {U} {V} {W} {K} {Π L C} {app A EE} = wd2 app sub-comp₂A sub-comp₂B

    sub-comp₂A : ∀ {U} {V} {W} {K} {A : Abstraction U K} {σ : Sub V W} {ρ : Rep U V} → A ⟦ σ •₂ ρ ⟧A ≡ A 〈 ρ 〉A ⟦ σ ⟧A
    sub-comp₂A {A = out E} = wd out (sub-comp₂ {E = E})
    sub-comp₂A {U} {V} {W} {Π K L} {Λ A} = wd Λ (trans (sub-wdA Sub↑-comp₂) sub-comp₂A)
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
    let open Equational-Reasoning (Expression (W , K) L) in 
    ∵ lift ((ρ L x) ⟦ σ ⟧)
    ≡ ρ L x ⟦ (λ _ → ↑) •₁ σ ⟧  [[ sub-comp₁ {E = ρ L x} ]]
    ≡ (lift (ρ L x)) ⟦ Sub↑ σ ⟧ [ sub-comp₂ {E = ρ L x} ]

  mutual
    sub-compA : ∀ {U} {V} {W} {K} {A : Abstraction U K} {σ : Sub V W} {ρ : Sub U V} →
      A ⟦ σ • ρ ⟧A ≡ A ⟦ ρ ⟧A ⟦ σ ⟧A
    sub-compA {A = out E} = wd out (sub-comp {E = E})
    sub-compA {U} {V} {W} {Π K L} {Λ A} {σ} {ρ} = wd Λ (let open Equational-Reasoning (Abstraction (W , K) L) in 
      ∵ A ⟦ Sub↑ (σ • ρ) ⟧A
      ≡ A ⟦ Sub↑ σ • Sub↑ ρ ⟧A    [ sub-wdA Sub↑-comp ]
      ≡ A ⟦ Sub↑ ρ ⟧A ⟦ Sub↑ σ ⟧A [ sub-compA ])

    sub-compB : ∀ {U} {V} {W} {K} {C : ConstructorKind K} {EE : Body U C} {σ : Sub V W} {ρ : Sub U V} →
      EE ⟦ σ • ρ ⟧B ≡ EE ⟦ ρ ⟧B ⟦ σ ⟧B
    sub-compB {EE = out} = ref
    sub-compB {U} {V} {W} {K} {(Π L C)} {app A EE} = wd2 app sub-compA sub-compB

    sub-comp : ∀ {U} {V} {W} {K} {E : Expression U K} {σ : Sub V W} {ρ : Sub U V} →
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
  Rep↑-is-Sub↑ _ x₀ = ref
  Rep↑-is-Sub↑ _ (↑ _) = ref

  mutual
    rep-is-sub : ∀ {U} {V} {K} {E : Expression U K} {ρ : Rep U V} →
             E 〈 ρ 〉 ≡ E ⟦ (λ K x → var (ρ K x)) ⟧
    rep-is-sub {E = var _} = ref
    rep-is-sub {U} {V} {K} {app c EE} = wd (app c) rep-is-subB

    rep-is-subB : ∀ {U} {V} {K} {C : ConstructorKind K} {EE : Body U C} {ρ : Rep U V} →
      EE 〈 ρ 〉B ≡ EE ⟦ (λ K x → var (ρ K x)) ⟧B
    rep-is-subB {EE = out} = ref
    rep-is-subB {EE = app _ _} = wd2 app rep-is-subA rep-is-subB

    rep-is-subA : ∀ {U} {V} {K} {A : Abstraction U K} {ρ : Rep U V} →
      A 〈 ρ 〉A ≡ A ⟦ (λ K x → var (ρ K x)) ⟧A
    rep-is-subA {A = out E} = wd out rep-is-sub
    rep-is-subA {U} {V} {Π K L} {Λ A} {ρ} = wd Λ (let open Equational-Reasoning (Abstraction (V , K) L) in 
      ∵ A 〈 Rep↑ ρ 〉A
      ≡ A ⟦ (λ M x → var (Rep↑ ρ M x)) ⟧A [ rep-is-subA ]
      ≡ A ⟦ Sub↑ (λ M x → var (ρ M x)) ⟧A [ sub-wdA Rep↑-is-Sub↑ ])
\end{code}

Let $E$ be an expression of kind $K$ over $V$.  Then we write $[x_0 := E]$ for the following substitution
$(V , K) \Rightarrow V$:

\begin{code}
  x₀:= : ∀ {V} {K} → Expression V K → Sub (V , K) V
  (x₀:= E) _ x₀ = E
  (x₀:= _) _ (↑ x) = var x
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
  comp₁-botsub : ∀ {U} {V} {K} {E : Expression U K} {ρ : Rep U V} →
    ρ •₁ (x₀:= E) ∼ (x₀:= (E 〈 ρ 〉)) •₂ Rep↑ ρ
  comp₁-botsub _ x₀ = ref
  comp₁-botsub _ (↑ _) = ref

  comp-botsub : ∀ {U} {V} {K} {E : Expression U K} {σ : Sub U V} →
    σ • (x₀:= E) ∼ (x₀:= (E ⟦ σ ⟧)) • Sub↑ σ
  comp-botsub _ x₀ = ref
  comp-botsub {σ = σ} L (↑ x) = trans (sym subid) (sub-comp₂ {E = σ L x})
\end{code}

\section{Reduction}

Let $R$ be a relation on expressions of the same kind.  We define $\rightarrow_R$ to be the
congruence generated by $R$, $\twoheadrightarrow_R$ to be its reflexive, transitive closure.

\begin{code}
  Reduction : Set₁
  Reduction = ∀ {V} {K} → Expression V K → Expression V K → Set

  mutual
    data osr (R : ∀ {V} {K} → Expression V K → Expression V K → Set) : ∀ {V} {K} → Expression V K → Expression V K → Set where
      redex : ∀ {V} {K} {M N : Expression V K} → R M N → osr R M N
      app : ∀ {V} {K} {C : ConstructorKind K} {c : Constructor C} {MM NN : Body V C} → osrB R MM NN → osr R (app c MM) (app c NN)

    data osrB (R : ∀ {V} {K} → Expression V K → Expression V K → Set) : ∀ {V} {K} {C : ConstructorKind K} → Body V C → Body V C → Set where
      appl : ∀ {V} {K} {L} {C : ConstructorKind L} {M N : Abstraction V K} {PP : Body V C} → osrA R M N → osrB R (app M PP) (app N PP)
      appr : ∀ {V} {K} {L} {C : ConstructorKind L} {M : Abstraction V K} {NN PP : Body V C} → osrB R NN PP → osrB R (app M NN) (app M PP)

    data osrA (R : ∀ {V} {K} → Expression V K → Expression V K → Set) : ∀ {V} {K} → Abstraction V K → Abstraction V K → Set where
      out : ∀ {V} {K} {M N : Expression V K} → osr R M N → osrA R (out M) (out N)
      Λ : ∀ {V} {K} {L} {M N : Abstraction (V , K) L} → osrA R M N → osrA R (Λ M) (Λ N)

  _→〈_〉_ : ∀ {V} {K} → Expression V K → (∀ {V} {K} → Expression V K → Expression V K → Set) → Expression V K → Set
  M →〈 R 〉 N = osr R M N

  data red (R : ∀ {V} {K} → Expression V K → Expression V K → Set) {V} {K} : Expression V K → Expression V K → Set where
    osr-red : ∀ {M} {N} → M →〈 R 〉 N → red R M N
    ref : ∀ {M} → red R M M
    trans-red : ∀ {M N P : Expression V K} → red R M N → red R N P → red R M P

  _↠〈_〉_ : ∀ {V} {K} → Expression V K → (∀ {V} {K} → Expression V K → Expression V K → Set) → Expression V K → Set
  M ↠〈 R 〉 N = red R M N

  data redB (R : ∀ {V} {K} → Expression V K → Expression V K → Set) {V} {K} {C : ConstructorKind K} : Body V C → Body V C → Set where
    osr-red : ∀ {M} {N} → osrB R M N → redB R M N
    ref : ∀ {M} → redB R M M
    trans-red : ∀ {M N P : Body V C} → redB R M N → redB R N P → redB R M P

  redapp : ∀ {R : ∀ {V} {K} → Expression V K → Expression V K → Set} {V} {K} {C : ConstructorKind K} (c : Constructor C) {MM NN : Body V C} →
    redB R MM NN → app c MM ↠〈 R 〉 app c NN
  redapp S (osr-red MM→NN) = osr-red (app MM→NN)
  redapp _ ref = ref
  redapp c (trans-red MM↠NN NN↠PP) = trans-red (redapp c MM↠NN) (redapp c NN↠PP)

  redappr : ∀ {R : Reduction} {V} {K} {L} {C : ConstructorKind L} {A : Abstraction V K} {EE FF : Body V C} →
    redB R EE FF → redB R (app A EE) (app A FF)
  redappr (osr-red EE→FF) = osr-red (appr EE→FF)
  redappr ref = ref
  redappr (trans-red EE↠FF FF↠GG) = trans-red (redappr EE↠FF) (redappr FF↠GG)

  data redA (R : Reduction) {V} {K}: Abstraction V K → Abstraction V K → Set where
    osr-red : ∀ {A} {B} → osrA R A B → redA R A B
    ref : ∀ {A} → redA R A A
    trans-red : ∀ {A B C : Abstraction V K} → redA R A B → redA R B C → redA R A C

  redappl : ∀ {R : Reduction} {V} {K} {L} {C : ConstructorKind L} {A B : Abstraction V K} {EE : Body V C} →
    redA R A B → redB R (app A EE) (app B EE)
  redappl (osr-red A→B) = osr-red (appl A→B)
  redappl ref = ref
  redappl (trans-red A↠B B↠C) = trans-red (redappl A↠B) (redappl B↠C)

  redout : ∀ {R : Reduction} {V} {K} {E F : Expression V K} → red R E F → redA R (out E) (out F)
  redout (osr-red E→F) = osr-red (out E→F)
  redout ref = ref
  redout (trans-red E↠F F↠G) = trans-red (redout E↠F) (redout F↠G)

  redΛ : ∀ {R : Reduction} {V} {K} {L} {A B : Abstraction (V , K) L} → redA R A B → redA R (Λ A) (Λ B)
  redΛ (osr-red A→B) = osr-red (Λ A→B)
  redΛ ref = ref
  redΛ (trans-red A↠B B↠C) = trans-red (redΛ A↠B) (redΛ B↠C)

  data conv (R : ∀ {V} {K} → Expression V K → Expression V K → Set) {V} {K} : Expression V K → Expression V K → Set where
    osr-conv : ∀ {M} {N} → M →〈 R 〉 N → conv R M N
    ref : ∀ {M} → conv R M M
    sym-conv : ∀ {M} {N} → conv R M N → conv R N M
    trans-conv : ∀ {M} {N} {P} → conv R M N → conv R N P → conv R M P

  _≃〈_〉_ : ∀ {V} {K} → Expression V K → (∀ {V} {K} → Expression V K → Expression V K → Set) → Expression V K → Set
  M ≃〈 R 〉 N = conv R M N
\end{code}

If $R$ respects replacement (substitution), then so does each of these relations.

\begin{code}
  mutual
    reposr : ∀ {R : Reduction} →
      (∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → R M N → R (M 〈 ρ 〉) (N 〈 ρ 〉)) →
      ∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → M →〈 R 〉 N → M 〈 ρ 〉 →〈 R 〉 N 〈 ρ 〉
    reposr hyp (redex M▷N) = redex (hyp M▷N)
    reposr hyp (app MM→NN) = app (reposrB hyp MM→NN)

    reposrB : ∀ {R : Reduction} →
      (∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → R M N → R (M 〈 ρ 〉) (N 〈 ρ 〉)) →
      ∀ {U} {V} {K} {C : ConstructorKind K} {M N : Body U C} {ρ : Rep U V} → osrB R M N → osrB R (M 〈 ρ 〉B) (N 〈 ρ 〉B)
    reposrB hyp (appl M→N) = appl (reposrA hyp M→N)
    reposrB hyp (appr NN→PP) = appr (reposrB hyp NN→PP)

    reposrA : ∀ {R : Reduction} →
      (∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → R M N → R (M 〈 ρ 〉) (N 〈 ρ 〉)) →
      ∀ {U} {V} {K} {A B : Abstraction U K} {ρ : Rep U V} → osrA R A B → osrA R (A 〈 ρ 〉A) (B 〈 ρ 〉A)
    reposrA hyp (out M→N) = out (reposr hyp M→N)
    reposrA hyp (Λ M→N) = Λ (reposrA hyp M→N)

  repred : ∀ {R : Reduction} →
    (∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → R M N → R (M 〈 ρ 〉) (N 〈 ρ 〉)) →
    ∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → M ↠〈 R 〉 N → M 〈 ρ 〉 ↠〈 R 〉 N 〈 ρ 〉
  repred hyp (osr-red M→N) = osr-red (reposr hyp M→N)
  repred _ ref = ref
  repred hyp (trans-red M↠N N↠P) = trans-red (repred hyp M↠N) (repred hyp N↠P)

  repconv : ∀ {R : Reduction} →
    (∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → R M N → R (M 〈 ρ 〉) (N 〈 ρ 〉)) →
    ∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → M ≃〈 R 〉 N → M 〈 ρ 〉 ≃〈 R 〉 N 〈 ρ 〉
  repconv hyp (osr-conv M→N) = osr-conv (reposr hyp M→N)
  repconv hyp ref = ref
  repconv hyp (sym-conv δ) = sym-conv (repconv hyp δ)
  repconv hyp (trans-conv δ δ₁) = trans-conv (repconv hyp δ) (repconv hyp δ₁)

  mutual
    subosr : ∀ {R : Reduction} →
      (∀ {U} {V} {K} {M N : Expression U K} {ρ : Sub U V} → R M N → R (M ⟦ ρ ⟧) (N ⟦ ρ ⟧)) →
      ∀ {U} {V} {K} {M N : Expression U K} {ρ : Sub U V} → M →〈 R 〉 N → M ⟦ ρ ⟧ →〈 R 〉 N ⟦ ρ ⟧
    subosr hyp (redex M▷N) = redex (hyp M▷N)
    subosr hyp (app MM→NN) = app (subosrB hyp MM→NN)

    subosrB : ∀ {R : Reduction} →
      (∀ {U} {V} {K} {M N : Expression U K} {ρ : Sub U V} → R M N → R (M ⟦ ρ ⟧) (N ⟦ ρ ⟧)) →
      ∀ {U} {V} {K} {C : ConstructorKind K} {M N : Body U C} {ρ : Sub U V} → osrB R M N → osrB R (M ⟦ ρ ⟧B) (N ⟦ ρ ⟧B)
    subosrB hyp (appl M→N) = appl (subosrA hyp M→N)
    subosrB hyp (appr NN→PP) = appr (subosrB hyp NN→PP)

    subosrA : ∀ {R : Reduction} →
      (∀ {U} {V} {K} {M N : Expression U K} {ρ : Sub U V} → R M N → R (M ⟦ ρ ⟧) (N ⟦ ρ ⟧)) →
      ∀ {U} {V} {K} {A B : Abstraction U K} {ρ : Sub U V} → osrA R A B → osrA R (A ⟦ ρ ⟧A) (B ⟦ ρ ⟧A)
    subosrA hyp (out M→N) = out (subosr hyp M→N)
    subosrA hyp (Λ M→N) = Λ (subosrA hyp M→N)

  subred : ∀ {R : Reduction} →
    (∀ {U} {V} {K} {M N : Expression U K} {ρ : Sub U V} → R M N → R (M ⟦ ρ ⟧) (N ⟦ ρ ⟧)) →
    ∀ {U} {V} {K} {M N : Expression U K} {ρ : Sub U V} → M ↠〈 R 〉 N → M ⟦ ρ ⟧ ↠〈 R 〉 N ⟦ ρ ⟧
  subred hyp (osr-red M→N) = osr-red (subosr hyp M→N)
  subred _ ref = ref
  subred hyp (trans-red M↠N N↠P) = trans-red (subred hyp M↠N) (subred hyp N↠P)

  subconv : ∀ {R : Reduction} →
    (∀ {U} {V} {K} {M N : Expression U K} {ρ : Sub U V} → R M N → R (M ⟦ ρ ⟧) (N ⟦ ρ ⟧)) →
    ∀ {U} {V} {K} {M N : Expression U K} {ρ : Sub U V} → M ≃〈 R 〉 N → M ⟦ ρ ⟧ ≃〈 R 〉 N ⟦ ρ ⟧
  subconv hyp (osr-conv M→N) = osr-conv (subosr hyp M→N)
  subconv hyp ref = ref
  subconv hyp (sym-conv δ) = sym-conv (subconv hyp δ)
  subconv hyp (trans-conv δ δ₁) = trans-conv (subconv hyp δ) (subconv hyp δ₁)
\end{code}

Let $\sigma, \tau : U \Rightarrow V$.  We say that $\sigma$ \emph{reduces} to $\tau$, $\sigma \twoheadrightarrow_R \tau$,
iff $\sigma(x) \twoheadrightarrow_R \tau(x)$ for all $x$.

\begin{code}
  _↠〈_〉s_ : ∀ {U} {V} → Sub U V → Reduction → Sub U V → Set
  σ ↠〈 R 〉s τ = ∀ K x → σ K x ↠〈 R 〉 τ K x
\end{code}

\begin{lemma}
\begin{enumerate}
\item
If $R$ respects replacement and $\sigma \twoheadrightarrow_R \tau$ then $(\sigma , K) \twoheadrightarrow_R (\tau , K)$.
\item
If $R$ respects replacement and $\sigma \twoheadrightarrow_R \tau$ then $E[\sigma] \twoheadrightarrow_R E[\tau]$.
\end{enumerate}
\end{lemma}

\begin{code}
  liftSub-red : ∀ {U} {V} {K} {ρ σ : Sub U V} {R : Reduction} → 
    (∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → R M N → R (M 〈 ρ 〉) (N 〈 ρ 〉)) →
    ρ ↠〈 R 〉s σ → Sub↑ {K = K} ρ ↠〈 R 〉s Sub↑ σ
  liftSub-red _ _ _ x₀ = ref
  liftSub-red hyp ρ↠σ L (↑ x) = repred hyp (ρ↠σ L x)

  mutual
    subredr : ∀ {U} {V} {K} {ρ σ : Sub U V} {R : Reduction} {E : Expression U K} →
      (∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → R M N → R (M 〈 ρ 〉) (N 〈 ρ 〉)) →
      ρ ↠〈 R 〉s σ → E ⟦ ρ ⟧ ↠〈 R 〉 E ⟦ σ ⟧
    subredr {E = var x} _ ρ↠σ = ρ↠σ _ x
    subredr {E = app c _} hyp ρ↠σ = redapp c (subredrB hyp ρ↠σ)

    subredrB : ∀ {U} {V} {K} {C : ConstructorKind K} {ρ σ : Sub U V} {R : Reduction} {EE : Body U C} →
      (∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → R M N → R (M 〈 ρ 〉) (N 〈 ρ 〉)) →
      ρ ↠〈 R 〉s σ → redB R (EE ⟦ ρ ⟧B) (EE ⟦ σ ⟧B)
    subredrB {EE = out} _ _ = ref
    subredrB {U} {V} {K} {Π L C} {ρ} {σ} {R} {app A EE} hyp ρ↠σ = trans-red (redappl (subredrA hyp ρ↠σ)) (redappr (subredrB hyp ρ↠σ))

    subredrA : ∀ {U} {V} {K} {ρ σ : Sub U V} {R : Reduction} {A : Abstraction U K} →
      (∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → R M N → R (M 〈 ρ 〉) (N 〈 ρ 〉)) →
      ρ ↠〈 R 〉s σ → redA R (A ⟦ ρ ⟧A) (A ⟦ σ ⟧A)
    subredrA {A = out E} hyp ρ↠σ = redout (subredr {E = E} hyp ρ↠σ)
    subredrA {U} {V} {(Π K C)} {ρ} {σ} {R} {Λ A} hyp ρ↠σ = redΛ (subredrA hyp (liftSub-red hyp ρ↠σ))
\end{code}

\subsection{Strong Normalization}

The \emph{strongly normalizable} expressions are defined inductively as follows.

\begin{code}
  data SN (R : Reduction) {V} {K} : Expression V K → Set where
    SNI : ∀ E → (∀ F → E →〈 R 〉 F → SN R F) → SN R E

  data SNA (R : Reduction) {V} {K} : Abstraction V K → Set where
    SNI : ∀ A → (∀ B → osrA R A B → SNA R B) → SNA R A

  data SNB (R : Reduction) {V} {K} {C : ConstructorKind K} : Body V C → Set where
    SNI : ∀ EE → (∀ FF → osrB R EE FF → SNB R FF) → SNB R EE
\end{code}

\begin{lemma}
\begin{enumerate}
\item
If $c([\vec{x_1}]E_1, \ldots, [\vec{x_n}]E_n)$ is strongly normalizable, then each $E_i$ is strongly normalizable.
\item
If $E[\sigma]$ is strongly normalizable then $E$ is strongly normalizable.
\item
If $E$ is strongly normalizable and $E \twoheadrightarrow_R F$ then $F$ is strongly normalizable.
\end{enumerate}
\end{lemma}

\begin{code}
  SNsubexp : ∀ {V} {K} {C : ConstructorKind K} {c : Constructor C} {EE : Body V C} {R : Reduction} → SN R (app c EE) → SNB R EE
  SNsubexp {c = c} {EE = EE} (SNI .(app c EE) SNcEE) = SNI EE (λ FF EE→FF → SNsubexp (SNcEE (app c FF) (app EE→FF)))

  SNout : ∀ {V} {K} {R : Reduction} → SNB R {V = V} {K = K} out
  SNout = λ {V} {K} {R} → SNI out (λ _ ())

  SNsubbodyl : ∀ {V} {K} {L} {C : ConstructorKind K} {A : Abstraction V L} {EE : Body V C} {R : Reduction} →
    SNB R (app A EE) → SNA R A
  SNsubbodyl {V} {K} {L} {C} {A} {EE} (SNI .(app A EE) SNAEE) = SNI A (λ B A↠B → SNsubbodyl (SNAEE (app B EE) (appl A↠B)))
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
  data Context : Alphabet → Set where
    〈〉 : Context ∅
    _,_ : ∀ {V} {K} {L} {_ : parent K L} → Context V → Expression V L → Context (V , K)

  typekindof : ∀ {V} {K} → Var V K → Context V → ExpressionKind
  typekindof x₀ (_,_ {L = L} _ _) = L
  typekindof (↑ x) (Γ , _) = typekindof x Γ

  typeof : ∀ {V} {K} (x : Var V K) (Γ : Context V) → Expression V (typekindof x Γ)
  typeof x₀ (_ , A)    = A 〈 (λ _ → ↑) 〉
  typeof (↑ x) (Γ , _) = typeof x Γ 〈 ( λ _ → ↑ ) 〉
\end{code}
