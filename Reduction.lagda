\begin{code}
open import Grammar
module Reduction (G : Grammar) where
  open Grammar.Grammar G 
\end{code}

\section{Reduction}

Let $R$ be a relation on expressions of the same kind, such that we never have $x R E$ for $x$ a variable.  We define $\rightarrow_R$ to be the
congruence generated by $R$, $\twoheadrightarrow_R$ to be its reflexive, transitive closure.

\begin{code}
  Reduction : Set₁
  Reduction = ∀ {V} {K} {C : ConstructorKind K} → Constructor C → Body V C → Expression V K → Set

  mutual
    data osr (R : Reduction) : ∀ {V} {K} → Expression V K → Expression V K → Set where
      redex : ∀ {V} {K} {C : ConstructorKind K} {c : Constructor C} {EE : Body V C} {F : Expression V K} → R c EE F → osr R (app c EE) F
      app : ∀ {V} {K} {C : ConstructorKind K} {c : Constructor C} {MM NN : Body V C} → osrB R MM NN → osr R (app c MM) (app c NN)

    data osrB (R : Reduction) : ∀ {V} {K} {C : ConstructorKind K} → Body V C → Body V C → Set where
      appl : ∀ {V} {K} {L} {C : ConstructorKind L} {M N : Abstraction V K} {PP : Body V C} → osrA R M N → osrB R (app M PP) (app N PP)
      appr : ∀ {V} {K} {L} {C : ConstructorKind L} {M : Abstraction V K} {NN PP : Body V C} → osrB R NN PP → osrB R (app M NN) (app M PP)

    data osrA (R : Reduction) : ∀ {V} {K} → Abstraction V K → Abstraction V K → Set where
      out : ∀ {V} {K} {M N : Expression V K} → osr R M N → osrA R (out M) (out N)
      Λ : ∀ {V} {K} {L} {M N : Abstraction (V , K) L} → osrA R M N → osrA R (Λ M) (Λ N)

  _→〈_〉_ : ∀ {V} {K} → Expression V K → Reduction → Expression V K → Set
  M →〈 R 〉 N = osr R M N

  data red (R : Reduction) {V} {K} : Expression V K → Expression V K → Set where
    osr-red : ∀ {M} {N} → M →〈 R 〉 N → red R M N
    ref : ∀ {M} → red R M M
    trans-red : ∀ {M N P : Expression V K} → red R M N → red R N P → red R M P

  _↠〈_〉_ : ∀ {V} {K} → Expression V K → Reduction → Expression V K → Set
  M ↠〈 R 〉 N = red R M N

  data redB (R : Reduction) {V} {K} {C : ConstructorKind K} : Body V C → Body V C → Set where
    osr-red : ∀ {M} {N} → osrB R M N → redB R M N
    ref : ∀ {M} → redB R M M
    trans-red : ∀ {M N P : Body V C} → redB R M N → redB R N P → redB R M P

  redapp : ∀ {R : Reduction} {V} {K} {C : ConstructorKind K} (c : Constructor C) {MM NN : Body V C} →
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

  data conv (R : Reduction) {V} {K} : Expression V K → Expression V K → Set where
    osr-conv : ∀ {M} {N} → M →〈 R 〉 N → conv R M N
    ref : ∀ {M} → conv R M M
    sym-conv : ∀ {M} {N} → conv R M N → conv R N M
    trans-conv : ∀ {M} {N} {P} → conv R M N → conv R N P → conv R M P

  _≃〈_〉_ : ∀ {V} {K} → Expression V K → Reduction → Expression V K → Set
  M ≃〈 R 〉 N = conv R M N
\end{code}

If $R$ respects replacement (substitution), then so does each of these relations.

\begin{code}
  --REFACTOR: Do this for a general relation on Expression V K
  respect-rep : Reduction → Set
  respect-rep R = ∀ {U} {V} {K} {C} {c} {EE} {F : Expression U K} {ρ : Rep U V} → R {U} {K} {C} c EE F → R c (EE 〈 ρ 〉B) (F 〈 ρ 〉)

  respect-sub : Reduction → Set
  respect-sub R = ∀ {U} {V} {K} {C} {c} {EE} {F : Expression U K} {ρ : Sub U V} → R {U} {K} {C} c EE F → R c (EE ⟦ ρ ⟧B) (F ⟦ ρ ⟧)

  mutual
    reposr : ∀ {R : Reduction} → respect-rep R →
      ∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → M →〈 R 〉 N → M 〈 ρ 〉 →〈 R 〉 N 〈 ρ 〉
    reposr hyp (redex M▷N) = redex (hyp M▷N)
    reposr hyp (app MM→NN) = app (reposrB hyp MM→NN)

    reposrB : ∀ {R : Reduction} → respect-rep R →
      ∀ {U} {V} {K} {C : ConstructorKind K} {M N : Body U C} {ρ : Rep U V} → osrB R M N → osrB R (M 〈 ρ 〉B) (N 〈 ρ 〉B)
    reposrB hyp (appl M→N) = appl (reposrA hyp M→N)
    reposrB hyp (appr NN→PP) = appr (reposrB hyp NN→PP)

    reposrA : ∀ {R : Reduction} → respect-rep R →
      ∀ {U} {V} {K} {A B : Abstraction U K} {ρ : Rep U V} → osrA R A B → osrA R (A 〈 ρ 〉A) (B 〈 ρ 〉A)
    reposrA hyp (out M→N) = out (reposr hyp M→N)
    reposrA hyp (Λ M→N) = Λ (reposrA hyp M→N)

  repred : ∀ {R : Reduction} → respect-rep R →
    ∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → M ↠〈 R 〉 N → M 〈 ρ 〉 ↠〈 R 〉 N 〈 ρ 〉
  repred hyp (osr-red M→N) = osr-red (reposr hyp M→N)
  repred _ ref = ref
  repred hyp (trans-red M↠N N↠P) = trans-red (repred hyp M↠N) (repred hyp N↠P)

  repconv : ∀ {R : Reduction} → respect-rep R →
    ∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} → M ≃〈 R 〉 N → M 〈 ρ 〉 ≃〈 R 〉 N 〈 ρ 〉
  repconv hyp (osr-conv M→N) = osr-conv (reposr hyp M→N)
  repconv hyp ref = ref
  repconv hyp (sym-conv δ) = sym-conv (repconv hyp δ)
  repconv hyp (trans-conv δ δ₁) = trans-conv (repconv hyp δ) (repconv hyp δ₁)

  mutual
    subosr : ∀ {R : Reduction} → respect-sub R →
      ∀ {U} {V} {K} {M N : Expression U K} {ρ : Sub U V} → M →〈 R 〉 N → M ⟦ ρ ⟧ →〈 R 〉 N ⟦ ρ ⟧
    subosr hyp (redex M▷N) = redex (hyp M▷N)
    subosr hyp (app MM→NN) = app (subosrB hyp MM→NN)

    subosrB : ∀ {R : Reduction} → respect-sub R →
      ∀ {U} {V} {K} {C : ConstructorKind K} {M N : Body U C} {ρ : Sub U V} → osrB R M N → osrB R (M ⟦ ρ ⟧B) (N ⟦ ρ ⟧B)
    subosrB hyp (appl M→N) = appl (subosrA hyp M→N)
    subosrB hyp (appr NN→PP) = appr (subosrB hyp NN→PP)

    subosrA : ∀ {R : Reduction} → respect-sub R →
      ∀ {U} {V} {K} {A B : Abstraction U K} {ρ : Sub U V} → osrA R A B → osrA R (A ⟦ ρ ⟧A) (B ⟦ ρ ⟧A)
    subosrA hyp (out M→N) = out (subosr hyp M→N)
    subosrA hyp (Λ M→N) = Λ (subosrA hyp M→N)

  subred : ∀ {R : Reduction} → respect-sub R →
    ∀ {U} {V} {K} {M N : Expression U K} {ρ : Sub U V} → M ↠〈 R 〉 N → M ⟦ ρ ⟧ ↠〈 R 〉 N ⟦ ρ ⟧
  subred hyp (osr-red M→N) = osr-red (subosr hyp M→N)
  subred _ ref = ref
  subred hyp (trans-red M↠N N↠P) = trans-red (subred hyp M↠N) (subred hyp N↠P)

  subconv : ∀ {R : Reduction} → respect-sub R →
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
    respect-rep R →
    ρ ↠〈 R 〉s σ → Sub↑ {K = K} ρ ↠〈 R 〉s Sub↑ σ
  liftSub-red _ _ _ x₀ = ref
  liftSub-red hyp ρ↠σ L (↑ x) = repred hyp (ρ↠σ L x)

  mutual
    subredr : ∀ {U} {V} {K} {ρ σ : Sub U V} {R : Reduction} {E : Expression U K} → respect-rep R →
      ρ ↠〈 R 〉s σ → E ⟦ ρ ⟧ ↠〈 R 〉 E ⟦ σ ⟧
    subredr {E = var x} _ ρ↠σ = ρ↠σ _ x
    subredr {E = app c _} hyp ρ↠σ = redapp c (subredrB hyp ρ↠σ)

    subredrB : ∀ {U} {V} {K} {C : ConstructorKind K} {ρ σ : Sub U V} {R : Reduction} {EE : Body U C} →
      respect-rep R →
      ρ ↠〈 R 〉s σ → redB R (EE ⟦ ρ ⟧B) (EE ⟦ σ ⟧B)
    subredrB {EE = out} _ _ = ref
    subredrB {U} {V} {K} {Π₂ L C} {ρ} {σ} {R} {app A EE} hyp ρ↠σ = trans-red (redappl (subredrA hyp ρ↠σ)) (redappr (subredrB hyp ρ↠σ))

    subredrA : ∀ {U} {V} {K} {ρ σ : Sub U V} {R : Reduction} {A : Abstraction U K} →
      respect-rep R →
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
If $E[\sigma]$ is strongly normalizable and $R$ respects substitution then $E$ is strongly normalizable.
\item
If $E$ is strongly normalizable and $E \twoheadrightarrow_R F$ then $F$ is strongly normalizable.
\end{enumerate}
\end{lemma}

\begin{code}
  SNsubexp : ∀ {V} {K} {C : ConstructorKind K} {c : Constructor C} {EE : Body V C} {R : Reduction} → SN R (app c EE) → SNB R EE
  SNsubexp {c = c} {EE = EE} (SNI .(app c EE) SNcEE) = SNI EE (λ FF EE→FF → SNsubexp (SNcEE (app c FF) (app EE→FF)))

  SNout : ∀ {V} {K} {R : Reduction} → SNB R {V = V} {K = K} out
  SNout = SNI out (λ _ ())

  SNsubbodyl : ∀ {V} {K} {L} {C : ConstructorKind K} {A : Abstraction V L} {EE : Body V C} {R : Reduction} →
    SNB R (app A EE) → SNA R A
  SNsubbodyl {A = A} {EE = EE} (SNI .(app A EE) SNAEE) = SNI A (λ B A↠B → SNsubbodyl (SNAEE (app B EE) (appl A↠B)))

  SNsubbodyr : ∀ {V} {K} {L} {C : ConstructorKind K} {A : Abstraction V L} {EE : Body V C} {R : Reduction} →
    SNB R (app A EE) → SNB R EE
  SNsubbodyr {A = A} {EE = EE} (SNI .(app A EE) SNAEE) = SNI EE (λ FF EE↠FF → SNsubbodyr (SNAEE (app A FF) (appr EE↠FF)))

  SNoutA : ∀ {V} {K} {R : Reduction} {E : Expression V K} → SNA R (out E) → SN R E
  SNoutA {E = E} (SNI .(out E) SNE) = SNI E (λ F E→F → SNoutA (SNE (out F) (out E→F)))
  
  SNlam : ∀ {V} {K} {L} {R : Reduction} {A : Abstraction (V , K) L} → SNA R (Λ A) → SNA R A
  SNlam {A = A} (SNI .(Λ A) SNlamA) = SNI A (λ B A→B → SNlam (SNlamA (Λ B) (Λ A→B)))

  SNsub : ∀ {U} {V} {K} {E : Expression U K} {σ : Sub U V} {R : Reduction} → 
    respect-sub R → SN R (E ⟦ σ ⟧) → SN R E
  SNsub {E = var x} _ SNEsigma = SNI (Grammar.var x) (λ _ ())
  SNsub {E = app c EE} {σ} hyp (SNI ._ SNEsigma) = SNI (app c EE) (λ F cEE→F → SNsub hyp (SNEsigma (F ⟦ σ ⟧) (subosr hyp cEE→F)))

  SNred : ∀ {V} {K} {E F : Expression V K} {R : Reduction} → SN R E → E ↠〈 R 〉 F → SN R F
  SNred {V} {K} {E} {F} (SNI .E SNE) (osr-red E→F) = SNE F E→F
  SNred SNE ref = SNE
  SNred SNE (trans-red E↠F F↠G) = SNred (SNred SNE E↠F) F↠G
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
