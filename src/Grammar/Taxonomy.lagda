\newcommand{\id}[1]{\mathsf{id}_{#1}}

\section{Grammars}

\subsection{Taxonomy}

\AgdaHide{
\begin{code}
module Grammar.Taxonomy where
open import Data.List
open import Prelims
\end{code}
}

Before we begin investigating the several theories we wish to consider, we present a general theory of syntax and
capture-avoiding substitution.

A \emph{taxononmy} consists of:
\begin{itemize}
\item a set of \emph{expression kinds};
\item a subset of expression kinds, called the \emph{variable kinds}.  We refer to the other expession kinds as \emph{non-variable kinds}.
\end{itemize}

%<*Taxonomy>
\begin{code}
record Taxonomy : Set₁ where
  field
    VarKind : Set
    NonVarKind : Set

  data ExpKind : Set where
    varKind : VarKind → ExpKind
    nonVarKind : NonVarKind → ExpKind
\end{code}
%</Taxonomy>

\begin{frame}[fragile]
\frametitle{Alphabets}
An \emph{alphabet} $A$ consists of a finite set of \emph{variables},
\mode<article>{to each of which is assigned a variable kind $K$.
Let $\emptyset$ be the empty alphabet, and $(A , K)$ be the result of extending the alphabet $A$ with one
fresh variable $x₀$ of kind $K$.  We write $\mathsf{Var}\ A\ K$ for the set of all variables in $A$ of kind $K$.}
\mode<beamer>{each with a variable kind.}

\begin{code}
  infixl 55 _,_
  data Alphabet : Set where
    ∅ : Alphabet
    _,_ : Alphabet → VarKind → Alphabet
\end{code}

\AgdaHide{
\begin{code}
  extend : Alphabet → List VarKind → Alphabet
  extend A [] = A
  extend A (K ∷ KK) = extend (A , K) KK

  snoc-extend : Alphabet → snocList VarKind → Alphabet
  snoc-extend A [] = A
  snoc-extend A (KK snoc K) = snoc-extend A KK , K
\end{code}
}

\begin{code}
  data Var : Alphabet → VarKind → Set where
    x₀ : ∀ {V} {K} → Var (V , K) K
    ↑ : ∀ {V} {K} {L} → Var V L → Var (V , K) L
\end{code}

\AgdaHide{
\begin{code}
  x₁ : ∀ {V} {K} {L} → Var (V , K , L) K
\end{code}
}

\begin{code}
  x₁ = ↑ x₀
\end{code}

\AgdaHide{
\begin{code}
  x₂ : ∀ {V} {K} {L} {L'} → Var (V , K , L , L') K
\end{code}
}

\begin{code}
  x₂ = ↑ x₁
\end{code}
\end{frame}

A \emph{constructor kind} is an expression of the form

\[ ((A_{11} \rightarrow \cdots \rightarrow A_{1r_1} \rightarrow B_1) \rightarrow \cdots \rightarrow (A_{m1} \rightarrow \cdots \rightarrow A_{mr_m} \rightarrow B_m) \rightarrow C) \]

where each $A_{ij}$ is a variable kind, and each $B_i$ and $C$ is an expression kind.

A constructor $c$ of kind (\ref{eq:conkind}) is a constructor that takes $m$ arguments of kind $B_1$, \ldots, $B_m$, and binds $r_i$ variables in its $i$th argument of kind $A_{ij}$,
producing an expression of kind $C$.  We write this expression as

\begin{equation}
\label{eq:expression}
c([x_{11}, \ldots, x_{1r_1}]E_1, \ldots, [x_{m1}, \ldots, x_{mr_m}]E_m) \enspace .
\end{equation}

The subexpressions of the form $[x_{i1}, \ldots, x_{ir_i}]E_i$ shall be called \emph{abstractions}.

We formalise this as follows.  First, a \emph{simple kind} over the sets $A$ and $B$ is an expression of the form
\[ a_1 \longrightarrow \cdots \longrightarrow a_n \longrightarrow b \]
where each $a_i \in A$ and $b \in B$.

\begin{code}
  record SimpleKind (A B : Set) : Set where
    constructor SK
    field
      dom : List A
      cod : B

  infix 71 _✧
  _✧ : ∀ {A} {B} → B → SimpleKind A B
  b ✧ = SK [] b

  infixr 70 _⟶_
  _⟶_ : ∀ {A} {B} → A → SimpleKind A B → SimpleKind A B
  a ⟶ SK dom cod = SK (a ∷ dom) cod
\end{code}

An abstraction kind is a simple kind over variable kinds and expression kinds.
A constructor kind is a simple kind over abstraction kinds and expression kinds.

\begin{code}
  AbsKind = SimpleKind VarKind ExpKind
  ConKind = SimpleKind AbsKind ExpKind
\end{code}

\begin{code}
  data KindClass : Set where
    -Expression : KindClass
    -ListAbs : KindClass

  Kind : KindClass → Set
  Kind -Expression = ExpKind
  Kind -ListAbs = List AbsKind
\end{code}

