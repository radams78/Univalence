\section{Grammars}

\begin{code}
module Grammar where
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

  Rep↑ : ∀ {U} {V} {K} → Rep U V → Rep (U , K) (V , K)
  Rep↑ _ _ x₀ = x₀
  Rep↑ ρ K (↑ x) = ↑ (ρ K x)

  mutual
    _〈_〉 : ∀ {U} {V} {K} → Expression U K → Rep U V → Expression V K
    var x 〈 ρ 〉 = var (ρ _ x)
    (app c EE) 〈 ρ 〉 = app c (EE 〈 ρ 〉B)
  
    _〈_〉B : ∀ {U} {V} {K} {C : ConstructorKind K} → Body U C → Rep U V → Body V C
    out 〈 ρ 〉B = out
    (app A EE) 〈 ρ 〉B = app (A 〈 ρ 〉A) (EE 〈 ρ 〉B)

    _〈_〉A : ∀ {U} {V} {A} → Abstraction U A → Rep U V → Abstraction V A
    out E 〈 ρ 〉A = out (E 〈 ρ 〉)
    Λ A 〈 ρ 〉A = Λ (A 〈 Rep↑ ρ 〉A)
\end{code}

A \emph{substitution} from alphabet $U$ to alphabet $V$ is a function $\sigma$ that maps every variable $x$ of kind $K$ in $U$ to an
\emph{expression} $\sigma(x)$ of kind $K$ over $V$.  Then, given an expression $E$ of kind $K$ over $U$, we write $E[\sigma]$ for
the result of substituting $\sigma(x)$ for $x$ for each variable in $E$, avoiding capture.

\begin{code}
  Sub : Alphabet → Alphabet → Set
  Sub U V = ∀ K → Var U K → Expression V K

  Sub↑ : ∀ {U} {V} {K} → Sub U V → Sub (U , K) (V , K)
  Sub↑ _ _ x₀ = var x₀
  Sub↑ σ K (↑ x) = (σ K x) 〈 (λ _ → ↑) 〉

  mutual
    _⟦_⟧ : ∀ {U} {V} {K} → Expression U K → Sub U V → Expression V K
    (var x) ⟦ σ ⟧ = σ _ x
    (app c EE) ⟦ σ ⟧ = app c (EE ⟦ σ ⟧B)

    _⟦_⟧B : ∀ {U} {V} {K} {C : ConstructorKind K} → Body U C → Sub U V → Body V C
    out ⟦ σ ⟧B = out
    (app A EE) ⟦ σ ⟧B = app (A ⟦ σ ⟧A) (EE ⟦ σ ⟧B)

    _⟦_⟧A : ∀ {U} {V} {A} → Abstraction U A → Sub U V → Abstraction V A
    (out E) ⟦ σ ⟧A = out (E ⟦ σ ⟧)
    (Λ A) ⟦ σ ⟧A = Λ (A ⟦ Sub↑ σ ⟧A)
\end{code}

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
