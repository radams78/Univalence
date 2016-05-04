\newcommand{\id}[1]{\mathsf{id}_{#1}}

\section{Grammars}

\begin{code}
module Taxonomy where

open import Function
open import Data.Empty
open import Data.Product
open import Data.Nat public
open import Data.Fin public using (Fin;zero;suc)
open import Data.List
open import Prelims
\end{code}

Before we begin investigating the several theories we wish to consider, we present a general theory of syntax and
capture-avoiding substitution.

A \emph{taxononmy} consists of:
\begin{itemize}
\item a set of \emph{expression kinds};
\item a subset of expression kinds, called the \emph{variable kinds}.  We refer to the other expession kinds as \emph{non-variable kinds}.
\end{itemize}

\begin{code}
record Taxonomy : Set₁ where
  field
    VarKind : Set
    NonVarKind : Set

  data ExpressionKind : Set where
    varKind : VarKind → ExpressionKind
    nonVarKind : NonVarKind → ExpressionKind
\end{code}

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

  data KindClass' : Set where
    -Expression : KindClass'
    -Constructor : ExpressionKind → KindClass'

  data Kind' : KindClass' → Set where
    base : ExpressionKind → Kind' -Expression
    out  : ∀ {K} → Kind' (-Constructor K)
    Π    : ∀ {K} → List VarKind → ExpressionKind → Kind' (-Constructor K) → Kind' (-Constructor K)
\end{code}

An \emph{alphabet} $A$ consists of a finite set of \emph{variables}, to each of which is assigned a variable kind $K$.
Let $\emptyset$ be the empty alphabet, and $(A , K)$ be the result of extending the alphabet $A$ with one
fresh variable $x₀$ of kind $K$.  We write $\mathsf{Var}\ A\ K$ for the set of all variables in $A$ of kind $K$.

\begin{code}
  data Alphabet : Set where
    ∅ : Alphabet
    _,_ : Alphabet → VarKind → Alphabet

  extend' : Alphabet → List VarKind → Alphabet
  extend' A [] = A
  extend' A (K ∷ KK) = extend' (A , K) KK
--TODO Replace extend

  data Var : Alphabet → VarKind → Set where
    x₀ : ∀ {V} {K} → Var (V , K) K
    ↑ : ∀ {V} {K} {L} → Var V L → Var (V , K) L
\end{code}

We give ourselves the following operations.  Given an extend'bet $A$ and finite set $F$, let $\mathsf{extend}\ A\ K\ F$ be the
extend'bet $A \uplus F$, where each element of $F$ has kind $K$.  Let $\mathsf{embedr}$ be the canonical injection
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
