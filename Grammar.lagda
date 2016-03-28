\section{Grammars}

\begin{code}
module Grammar where

open import Prelims
\end{code}

Before we begin investigating the several theories we wish to consider, we present a general theory of syntax and
capture-avoiding substitution.

A \emph{grammar} consists of:
\begin{itemize}
\item a set of \emph{expression kinds};
\item a subset of expression kinds, the \emph{variable kinds};
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

An \emph{alphabet} $V = \{ V_E \}_E$ consists of a set $V_E$ of \emph{variables} of kind $E$ for each expression kind $E$.  The \emph{expressions}
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

  extend : Alphabet → VarKind → FinSet → Alphabet
  extend A K ∅ = A
  extend A K (Lift F) = extend A K F , K

  embed : ∀ {A} {K} {F} → El F → Var (extend A K F) K
  embed ⊥ = x₀
  embed (↑ x) = ↑ (embed x)

record ToGrammar (T : Taxonomy) : Set₁ where
  open Taxonomy T
  field
    Constructor    : ∀ {K : ExpressionKind} → Kind (-Constructor K) → Set
    parent         : VarKind → ExpressionKind

  data Subexpression (V : Alphabet) : ∀ C → Kind C → Set where
    var : ∀ {K} → Var V K → Subexpression V -Expression (base (varKind K))
    app : ∀ {K} {C : Kind (-Constructor K)} → Constructor C → Subexpression V (-Constructor K) C → Subexpression V -Expression (base K)
    out : ∀ {K} → Subexpression V -Expression (base K) → Subexpression V -Abstraction (out K)
    Λ   : ∀ {K} {A} → Subexpression (V , K) -Abstraction A → Subexpression V -Abstraction (Π K A)
    out₂ : ∀ {K} → Subexpression V (-Constructor K) out₂
    app₂ : ∀ {K} {A} {C} → Subexpression V -Abstraction A → Subexpression V (-Constructor K) C → Subexpression V (-Constructor K) (Π₂ A C)

  var-inj : ∀ {V} {K} {x y : Var V K} → var x ≡ var y → x ≡ y
  var-inj ref = ref

  Expression : Alphabet → ExpressionKind → Set
  Expression V K = Subexpression V -Expression (base K)
\end{code}

Given alphabets $U$, $V$, and a function $\rho$ that maps every variable in $U$ of kind $K$ to a variable in $V$ of kind $K$,
we denote by $E \{ \rho \}$ the result of \emph{replacing} every variable $x$ in $E$ with $\rho(x)$.

\begin{code}
  record PreOpFamily : Set₂ where
    field
      Op : Alphabet → Alphabet → Set
      apV : ∀ {U} {V} {K} → Op U V → Var U K → Expression V (varKind K)
      liftOp : ∀ {U} {V} {K} → Op U V → Op (U , K) (V , K)
      comp : ∀ {U} {V} {W} → Op V W → Op U V → Op U W

    _∼op_ : ∀ {U} {V} → Op U V → Op U V → Set
    _∼op_ {U} {V} ρ σ = ∀ {K} (x : Var U K) → apV ρ x ≡ apV σ x

    ap : ∀ {U} {V} {C} {K} → Op U V → Subexpression U C K → Subexpression V C K
    ap ρ (var x) = apV ρ x
    ap ρ (app c EE) = app c (ap ρ EE)
    ap ρ (out E) = out (ap ρ E)
    ap ρ (Λ E) = Λ (ap (liftOp ρ) E)
    ap _ out₂ = out₂
    ap ρ (app₂ E EE) = app₂ (ap ρ E) (ap ρ EE)

  record IsOpFamily (opfamily : PreOpFamily) : Set₂ where
    open PreOpFamily opfamily
    field
      liftOp-wd : ∀ {V} {W} {K} {ρ σ : Op V W} → ρ ∼op σ →
        liftOp {K = K} ρ ∼op liftOp σ
      apV-comp : ∀ {U} {V} {W} {K} {σ : Op V W} {ρ : Op U V} {x : Var U K} →
        apV (comp σ ρ) x ≡ ap σ (apV ρ x)
      liftOp-comp : ∀ {U} {V} {W} {K} {σ : Op V W} {ρ : Op U V} →
        liftOp {K = K} (comp σ ρ) ∼op comp (liftOp σ) (liftOp ρ)
      
    ap-wd : ∀ {U} {V} {C} {K} {ρ σ : Op U V} {E : Subexpression U C K} →
      ρ ∼op σ → ap ρ E ≡ ap σ E
    ap-wd {E = var x} ρ-is-σ = ρ-is-σ x
    ap-wd {E = app c EE} ρ-is-σ = wd (app c) (ap-wd {E = EE} ρ-is-σ)
    ap-wd {E = out E} ρ-is-σ = wd out (ap-wd {E = E} ρ-is-σ)
    ap-wd {E = Λ {K} E} ρ-is-σ = wd Λ (ap-wd {E = E} (liftOp-wd {K = K} ρ-is-σ))
    ap-wd {E = out₂} _ = ref
    ap-wd {E = app₂ E F} ρ-is-σ = wd2 app₂ (ap-wd {E = E} ρ-is-σ) (ap-wd {E = F} ρ-is-σ)

    ap-comp : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {F : Op V W} {G : Op U V} → ap (comp F G) E ≡ ap F (ap G E)
    ap-comp {E = var x} = apV-comp
    ap-comp {E = app c EE} = wd (app c) (ap-comp {E = EE})
    ap-comp {E = out E} = wd out (ap-comp {E = E})
    ap-comp {U} {V} {W} {E = Λ E} {σ} {ρ} = wd Λ (let open Equational-Reasoning _ in 
      ∵ ap (liftOp (comp σ ρ)) E
      ≡ ap (comp (liftOp σ) (liftOp ρ)) E [ ap-wd {E = E} (liftOp-comp {σ = σ} {ρ = ρ}) ]
      ≡ ap (liftOp σ) (ap (liftOp ρ) E)   [ ap-comp {E = E} ])
    ap-comp {E = out₂} = ref
    ap-comp {E = app₂ E F} = wd2 app₂ (ap-comp {E = E}) (ap-comp {E = F})

  record OpFamily : Set₂ where
    field
      preOpFamily : PreOpFamily
      isOpFamily  : IsOpFamily preOpFamily
    open PreOpFamily preOpFamily public
    open IsOpFamily isOpFamily public

  Rep : Alphabet → Alphabet → Set
  Rep U V = ∀ K → Var U K → Var V K

  Rep↑ : ∀ {U} {V} {K} → Rep U V → Rep (U , K) (V , K)
  Rep↑ _ _ x₀ = x₀
  Rep↑ ρ K (↑ x) = ↑ (ρ K x)

  infixl 75 _•R_
  _•R_ : ∀ {U} {V} {W} → Rep V W → Rep U V → Rep U W
  (ρ' •R ρ) K x = ρ' K (ρ K x)

  pre-replacement : PreOpFamily
  pre-replacement = record { 
    Op = Rep; 
    apV = λ ρ x → var (ρ _ x); 
    liftOp = Rep↑;
    comp = _•R_ }

  _∼R_ : ∀ {U} {V} → Rep U V → Rep U V → Set
  _∼R_ = PreOpFamily._∼op_ pre-replacement

  Rep↑-wd : ∀ {U} {V} {K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → Rep↑ {K = K} ρ ∼R Rep↑ ρ'
  Rep↑-wd ρ-is-ρ' x₀ = ref
  Rep↑-wd ρ-is-ρ' (↑ x) = wd (var ∘ ↑) (var-inj (ρ-is-ρ' x))

  Rep↑-comp : ∀ {U} {V} {W} {K} {ρ' : Rep V W} {ρ : Rep U V} → Rep↑ {K = K} (ρ' •R ρ) ∼R Rep↑ ρ' •R Rep↑ ρ
  Rep↑-comp x₀ = ref
  Rep↑-comp (↑ _) = ref

  replacement : OpFamily
  replacement = record { 
    preOpFamily = pre-replacement; 
    isOpFamily = record { 
      liftOp-wd = Rep↑-wd; 
      apV-comp = ref; 
      liftOp-comp = Rep↑-comp } }

  embedl : ∀ {A} {K} {F} → Rep A (extend A K F)
  embedl {F = ∅} _ x = x
  embedl {F = Lift F} K x = ↑ (embedl {F = F} K x)
\end{code}

The alphabets and replacements form a category.

\begin{code}
  idRep : ∀ V → Rep V V
  idRep _ _ x = x

  --We choose not to prove the category axioms, as they hold up to judgemental equality.
\end{code}

Given a replacement $\rho : U \rightarrow V$, we can `lift´ this to a replacement $(\rho , K) : (U , K) \rightarrow (V , K)$.
Under this operation, the mapping $(- , K)$ becomes an endofunctor on the category of alphabets and replacements.

\begin{code}
  Rep↑-id : ∀ {V} {K} → Rep↑ (idRep V) ∼R idRep (V , K)
  Rep↑-id x₀ = ref
  Rep↑-id (↑ _) = ref
\end{code}

Finally, we can define $E \langle \rho \rangle$, the result of replacing each variable $x$ in $E$ with $\rho(x)$.
Under this operation, the mapping $\mathsf{Expression}\ -\ K$ becomes a functor from the category of
alphabets and replacements to the category of sets.

\begin{code}
  infix 60 _〈_〉
  _〈_〉 : ∀ {U} {V} {C} {K} → Subexpression U C K → Rep U V → Subexpression V C K
  E 〈 ρ 〉 = OpFamily.ap replacement ρ E

  rep = _〈_〉
  --TODO Inline this

  rep-wd : ∀ {U} {V} {C} {K} {E : Subexpression U C K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → E 〈 ρ 〉 ≡ E 〈 ρ' 〉
  rep-wd {U} {V} {C} {K} {E} {ρ} {ρ'} ρ-is-ρ' = OpFamily.ap-wd replacement {U} {V} {C} {K} {ρ} {ρ'} {E} ρ-is-ρ'

  rep-id : ∀ {V} {C} {K} {E : Subexpression V C K} → E 〈 idRep V 〉 ≡ E
  rep-id {E = var _} = ref
  rep-id {E = app c EE} = wd (app c) rep-id
  rep-id {E = out E} = wd out rep-id
  rep-id {V} {E = Λ {K} {A} E} = wd Λ (let open Equational-Reasoning (Subexpression (V , K) -Abstraction A) in 
    ∵ E 〈 Rep↑ (idRep V) 〉
    ≡ E 〈 idRep (V , K) 〉        [ rep-wd {E = E} Rep↑-id ]
    ≡ E                          [ rep-id ])
  rep-id {E = out₂} = ref
  rep-id {E = app₂ E EE} = wd2 app₂ rep-id rep-id  

  rep-comp : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {ρ : Rep U V} {σ : Rep V W} →
    E 〈 σ •R ρ 〉 ≡ E 〈 ρ 〉 〈 σ 〉
  rep-comp {E = var _} = ref
  rep-comp {E = app c EE} = wd (app c) (rep-comp {E = EE})
  rep-comp {E = out E} = wd out (rep-comp {E = E})
  rep-comp {E = Λ E} {ρ} {σ} = wd Λ (let open Equational-Reasoning _ in 
    ∵ E 〈 Rep↑ (σ •R ρ) 〉
    ≡ E 〈 Rep↑ σ •R Rep↑ ρ 〉 [ rep-wd {E = E} Rep↑-comp ]
    ≡ E 〈 Rep↑ ρ 〉 〈 Rep↑ σ 〉 [ rep-comp {E = E} ])
  rep-comp {E = out₂} = ref
  rep-comp {E = app₂ E EE} = wd2 app₂ (rep-comp {E = E}) (rep-comp {E = EE})
\end{code}

This provides us with the canonical mapping from an expression over $V$ to an expression over $(V , K)$:
\begin{code}
  liftE : ∀ {V} {K} {L} → Expression V L → Expression (V , K) L
  liftE E = E 〈 (λ _ → ↑) 〉
\end{code}

A \emph{substitution} $\sigma$ from alphabet $U$ to alphabet $V$, $\sigma : U \Rightarrow V$, is a function $\sigma$ that maps every variable $x$ of kind $K$ in $U$ to an
\emph{expression} $\sigma(x)$ of kind $K$ over $V$.  Then, given an expression $E$ of kind $K$ over $U$, we write $E[\sigma]$ for
the result of substituting $\sigma(x)$ for $x$ for each variable in $E$, avoiding capture.

\begin{code}
  Sub : Alphabet → Alphabet → Set
  Sub U V = ∀ K → Var U K → Expression V (varKind K)

  _∼_ : ∀ {U} {V} → Sub U V → Sub U V → Set
  σ ∼ τ = ∀ K x → σ K x ≡ τ K x
\end{code}

\newcommand{\id}[1]{\mathsf{id}_{#1}}
The \emph{identity} substitution $\id{V} : V \rightarrow V$ is defined as follows.

\begin{code}
  idSub : ∀ {V} → Sub V V
  idSub _ = var
\end{code}

Given $\sigma : U \rightarrow V$ and an expression $E$ over $U$, we want to define the expression $E[\sigma]$ over $V$,
the result of applying the substitution $\sigma$ to $M$.
Only after this will we be able to define the composition of two substitutions.  However, there is some work we need to do before we are able to do this.

We can define the composition of a substitution and a replacement as follows
\begin{code}
  infix 75 _•₁_
  _•₁_ : ∀ {U} {V} {W} → Rep V W → Sub U V → Sub U W
  (ρ •₁ σ) K x = (σ K x) 〈 ρ 〉

  infix 75 _•₂_
  _•₂_ : ∀ {U} {V} {W} → Sub V W → Rep U V → Sub U W
  (σ •₂ ρ) K x = σ K (ρ K x)
\end{code}

Given a substitution $\sigma : U \Rightarrow V$,  define a substitution $
(\sigma , K) : (U , K) \Rightarrow (V , K)$ as follows.

\begin{code}
  Sub↑ : ∀ {U} {V} {K} → Sub U V → Sub (U , K) (V , K)
  Sub↑ _ _ x₀ = var x₀
  Sub↑ σ K (↑ x) = liftE (σ K x)

  Sub↑-wd : ∀ {U} {V} {K} {σ σ' : Sub U V} → σ ∼ σ' → Sub↑ {K = K} σ ∼ Sub↑ σ'
  Sub↑-wd {K = K} σ-is-σ' ._ x₀ = ref
  Sub↑-wd σ-is-σ' L (↑ x) = wd liftE (σ-is-σ' L x)
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
  Sub↑-comp₁ {U} {V} {W} {K} {ρ} {σ} L (↑ x) = let open Equational-Reasoning (Expression (W , K) (varKind L)) in 
    ∵ liftE ((σ L x) 〈 ρ 〉)
    ≡ (σ L x) 〈 (λ _ x → ↑ (ρ _ x)) 〉 [[ rep-comp {E = σ L x} ]]
    ≡ (liftE (σ L x)) 〈 Rep↑ ρ 〉     [ rep-comp {E = σ L x} ]

  Sub↑-comp₂ : ∀ {U} {V} {W} {K} {σ : Sub V W} {ρ : Rep U V} → Sub↑ {K = K} (σ •₂ ρ) ∼ Sub↑ σ •₂ Rep↑ ρ
  Sub↑-comp₂ {K = K} ._ x₀ = ref
  Sub↑-comp₂ L (↑ x) = ref
\end{code}

We can now define the result of applying a substitution $\sigma$ to an expression $E$,
which we denote $E [ \sigma ]$.

\begin{code}
  infix 60 _⟦_⟧
  _⟦_⟧ : ∀ {U} {V} {C} {K} → Subexpression U C K → Sub U V → Subexpression V C K
  var x ⟦ σ ⟧ = σ _ x
  app c EE ⟦ σ ⟧ = app c (EE ⟦ σ ⟧)
  out E ⟦ σ ⟧ = out (E ⟦ σ ⟧)
  Λ E ⟦ σ ⟧ = Λ (E ⟦ Sub↑ σ ⟧)
  out₂ ⟦ _ ⟧ = out₂
  app₂ E EE ⟦ σ ⟧ = app₂ (E ⟦ σ ⟧) (EE ⟦ σ ⟧)

  sub-wd : ∀ {U} {V} {C} {K} {E : Subexpression U C K} {σ σ' : Sub U V} → σ ∼ σ' → E ⟦ σ ⟧ ≡ E ⟦ σ' ⟧
  sub-wd {E = var x} σ-is-σ' = σ-is-σ' _ x
  sub-wd {E = app c EE} σ-is-σ' = wd (app c) (sub-wd {E = EE} σ-is-σ')
  sub-wd {E = out E} σ-is-σ' = wd out (sub-wd {E = E} σ-is-σ')
  sub-wd {E = Λ E} σ-is-σ' = wd Λ (sub-wd {E = E} (Sub↑-wd σ-is-σ'))
  sub-wd {E = out₂} _ = ref
  sub-wd {E = app₂ E EE} σ-is-σ' = wd2 app₂ (sub-wd {E = E} σ-is-σ') (sub-wd {E = EE} σ-is-σ')
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
  sub-id : ∀ {V} {C} {K} {E : Subexpression V C K} → E ⟦ idSub ⟧ ≡ E
  sub-id {E = var _} = ref
  sub-id {E = app c EE} = wd (app c) sub-id
  sub-id {E = out E} = wd out sub-id
  sub-id {E = Λ E} = wd Λ (let open Equational-Reasoning _ in 
    ∵ E ⟦ Sub↑ idSub ⟧
    ≡ E ⟦ idSub ⟧         [ sub-wd {E = E} Sub↑-id ]
    ≡ E                   [ sub-id ])
  sub-id {E = out₂} = ref
  sub-id {E = app₂ E EE} = wd2 app₂ sub-id sub-id

  sub-comp₁ : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {ρ : Rep V W} {σ : Sub U V} →
      E ⟦ ρ •₁ σ ⟧ ≡ E ⟦ σ ⟧ 〈 ρ 〉
  sub-comp₁ {E = var _} = ref
  sub-comp₁ {E = app c EE} = wd (app c) (sub-comp₁ {E = EE})
  sub-comp₁ {E = out₂} = ref
  sub-comp₁ {E = app₂ A EE} = wd2 app₂ (sub-comp₁ {E = A}) (sub-comp₁ {E = EE})
  sub-comp₁ {E = out E} = wd out (sub-comp₁ {E = E})
  sub-comp₁ {E = Λ A} {ρ} {σ} = 
    wd Λ (let open Equational-Reasoning _ in 
    ∵ A ⟦ Sub↑ (ρ •₁ σ) ⟧
    ≡ A ⟦ Rep↑ ρ •₁ Sub↑ σ ⟧   [ sub-wd {E = A} Sub↑-comp₁ ]
    ≡ A ⟦ Sub↑ σ ⟧ 〈 Rep↑ ρ 〉  [ sub-comp₁ {E = A} ])

  sub-comp₂ : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {σ : Sub V W} {ρ : Rep U V} → E ⟦ σ •₂ ρ ⟧ ≡ E 〈 ρ 〉 ⟦ σ ⟧
  sub-comp₂ {E = var _} = ref
  sub-comp₂ {E = app c EE} = wd (app c) (sub-comp₂ {E = EE})
  sub-comp₂ {E = out₂} = ref
  sub-comp₂ {E = app₂ A EE} = wd2 app₂ (sub-comp₂ {E = A}) (sub-comp₂ {E = EE})
  sub-comp₂ {E = out E} = wd out (sub-comp₂ {E = E})
  sub-comp₂ {E = Λ A} {σ} {ρ} = wd Λ (let open Equational-Reasoning _ in 
    ∵ A ⟦ Sub↑ (σ •₂ ρ) ⟧
    ≡ A ⟦ Sub↑ σ •₂ Rep↑ ρ ⟧ [ sub-wd {E = A} Sub↑-comp₂ ]
    ≡ A 〈 Rep↑ ρ 〉 ⟦ Sub↑ σ ⟧ [ sub-comp₂ {E = A} ])
\end{code}

We define the composition of two substitutions, as follows.

\begin{code}
  subid : ∀ {V} → Sub V V
  subid {V} K x = var x

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
  pre-substitution : PreOpFamily
  pre-substitution = record { 
    Op = Sub; 
    apV = λ σ x → σ _ x; 
    liftOp = Sub↑; 
    comp = _•_ }

--TODO Remove this
  sub-is-sub : ∀ {U} {V} {σ : Sub U V} {C} {K} {E : Subexpression U C K} →
               E ⟦ σ ⟧ ≡ PreOpFamily.ap pre-substitution σ E
  sub-is-sub {E = var _} = ref
  sub-is-sub {E = app c E} = wd (app c) (sub-is-sub {E = E})
  sub-is-sub {E = out E} = wd out (sub-is-sub {E = E})
  sub-is-sub {E = Λ E} = wd Λ (sub-is-sub {E = E})
  sub-is-sub {E = out₂} = ref
  sub-is-sub {E = app₂ E F} = wd2 app₂ (sub-is-sub {E = E}) (sub-is-sub {E = F})

  Sub↑-comp : ∀ {U} {V} {W} {ρ : Sub U V} {σ : Sub V W} {K} →
    Sub↑ {K = K} (σ • ρ) ∼ Sub↑ σ • Sub↑ ρ
  Sub↑-comp _ x₀ = ref
  Sub↑-comp {W = W} {ρ = ρ} {σ = σ} {K = K} L (↑ x) =
    let open Equational-Reasoning (Expression (W , K) (varKind L)) in 
      ∵ liftE ((ρ L x) ⟦ σ ⟧)
      ≡ ρ L x ⟦ (λ _ → ↑) •₁ σ ⟧  [[ sub-comp₁ {E = ρ L x} ]]
      ≡ (liftE (ρ L x)) ⟦ Sub↑ σ ⟧ [ sub-comp₂ {E = ρ L x} ]

  substitution : OpFamily
  substitution = record { 
    preOpFamily = pre-substitution; 
    isOpFamily = record { 
      liftOp-wd = λ ρ-is-σ → Sub↑-wd (λ _ → ρ-is-σ) _; 
      apV-comp = λ {U} {V} {W} {K} {σ} {ρ} {x} → sub-is-sub {E = ρ K x};
      liftOp-comp = Sub↑-comp _ } }

  mutual
    sub-compA : ∀ {U} {V} {W} {K} {A : Subexpression U -Abstraction K} {σ : Sub V W} {ρ : Sub U V} →
      A ⟦ σ • ρ ⟧ ≡ A ⟦ ρ ⟧ ⟦ σ ⟧
    sub-compA {A = out E} = wd out (sub-comp {E = E})
    sub-compA {U} {V} {W} .{Π K L} {Λ {K} {L} A} {σ} {ρ} = wd Λ (let open Equational-Reasoning (Subexpression (W , K) -Abstraction L) in 
      ∵ A ⟦ Sub↑ (σ • ρ) ⟧
      ≡ A ⟦ Sub↑ σ • Sub↑ ρ ⟧    [ sub-wd {E = A} Sub↑-comp ]
      ≡ A ⟦ Sub↑ ρ ⟧ ⟦ Sub↑ σ ⟧  [ sub-compA {A = A} ])

    sub-compB : ∀ {U} {V} {W} {K} {C : Kind (-Constructor K)} {EE : Subexpression U (-Constructor K) C} {σ : Sub V W} {ρ : Sub U V} →
      EE ⟦ σ • ρ ⟧ ≡ EE ⟦ ρ ⟧ ⟦ σ ⟧
    sub-compB {EE = out₂} = ref
    sub-compB {U} {V} {W} {K} {(Π₂ L C)} {app₂ A EE} = wd2 app₂ (sub-compA {A = A}) (sub-compB {EE = EE})

    sub-comp : ∀ {U} {V} {W} {K} {E : Expression U K} {σ : Sub V W} {ρ : Sub U V} →
      E ⟦ σ • ρ ⟧ ≡ E ⟦ ρ ⟧ ⟦ σ ⟧
    sub-comp {E = var _} = ref
    sub-comp {U} {V} {W} {K} {app c EE} = wd (app c) (sub-compB {EE = EE})
\end{code}

\begin{lemma}
The alphabets and substitutions form a category under this composition.
\end{lemma}

\begin{code}
  assoc : ∀ {U V W X} {ρ : Sub W X} {σ : Sub V W} {τ : Sub U V} → ρ • (σ • τ) ∼ (ρ • σ) • τ
  assoc {τ = τ} K x = sym (sub-comp {E = τ K x})

  sub-unitl : ∀ {U} {V} {σ : Sub U V} → idSub • σ ∼ σ
  sub-unitl _ _ = sub-id

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
    rep-is-sub : ∀ {U} {V} {K} {E : Expression U K} {ρ : Rep U V} →
             E 〈 ρ 〉 ≡ E ⟦ (λ K x → var (ρ K x)) ⟧
    rep-is-sub {E = var _} = ref
    rep-is-sub {U} {V} {K} {app c EE} = wd (app c) (rep-is-subB {EE = EE})

    rep-is-subB : ∀ {U} {V} {K} {C : Kind (-Constructor K)} {EE : Subexpression U (-Constructor K) C} {ρ : Rep U V} →
      EE 〈 ρ 〉 ≡ EE ⟦ (λ K x → var (ρ K x)) ⟧
    rep-is-subB {EE = out₂} = ref
    rep-is-subB {EE = app₂ A EE} = wd2 app₂ (rep-is-subA {A = A}) (rep-is-subB {EE = EE})

    rep-is-subA : ∀ {U} {V} {K} {A : Subexpression U -Abstraction K} {ρ : Rep U V} →
      A 〈 ρ 〉 ≡ A ⟦ (λ K x → var (ρ K x)) ⟧
    rep-is-subA {A = out E} = wd out (rep-is-sub {E = E})
    rep-is-subA {U} {V} .{Π K L} {Λ {K} {L} A} {ρ} = wd Λ (let open Equational-Reasoning (Subexpression (V , K) -Abstraction L) in 
      ∵ A 〈 Rep↑ ρ 〉
      ≡ A ⟦ (λ M x → var (Rep↑ ρ M x)) ⟧ [ rep-is-subA {A = A} ]
      ≡ A ⟦ Sub↑ (λ M x → var (ρ M x)) ⟧ [ sub-wd {E = A} Rep↑-is-Sub↑ ])
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
  comp₁-botsub _ x₀ = ref
  comp₁-botsub _ (↑ _) = ref

  comp-botsub : ∀ {U} {V} {K} {E : Expression U (varKind K)} {σ : Sub U V} →
    σ • (x₀:= E) ∼ (x₀:= (E ⟦ σ ⟧)) • Sub↑ σ
  comp-botsub _ x₀ = ref
  comp-botsub {σ = σ} L (↑ x) = trans (sym sub-id) (sub-comp₂ {E = σ L x})
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
