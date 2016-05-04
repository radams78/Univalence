\subsection{Congruences}

A \emph{congruence} is a relation $R$ on expressions such that:
\begin{enumerate}
\item
if $M R N$, then $M$ and $N$ have the same kind;
\item
if $M_i R N_i$ for all $i$, then $c[[\vec{x_1}]M_1, \ldots, [\vec{x_n}]M_n] R c[[\vec{x_1}]N_1, \ldots, [\vec{x_n}]N_n]$.
\end{enumerate}

\begin{code}
open import Grammar

module Grammar.Congruence (G : Grammar) where
  open Grammar.Grammar G

  Relation : Set₁
  Relation = ∀ {V} {C} {K} → Subexpression V C K → Subexpression V C K → Set

  record IsCongruence (R : Relation) : Set where
    field
        ICapp : ∀ {V} {K} {C} {c} {MM NN : Body V {K} C} → R MM NN → R (app c MM) (app c NN)
        ICout : ∀ {V} {K} → R {V} { -Constructor K} {out} out out
        ICappl : ∀ {V} {K} {A} {L} {C} {M N : Expression (extend' V A) L} {PP : Body V {K} C} → R M N → R (_,,_ {A = A} M PP) (N ,, PP)
        ICappr : ∀ {V} {K} {A} {L} {C} {M : Expression (extend' V A) L} {NN PP : Body V {K} C} → R NN PP → R (_,,_ {A = A} M NN) (M ,, PP)
\end{code}

