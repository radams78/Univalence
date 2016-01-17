\section{Preliminaries}

\begin{code}
module Prelims where
\end{code}

\subsection{Functions}

\newcommand{\id}[1]{\mathrm{id}_{#1}}
We write $\id{A}$ for the identity function on the type $A$, and $g \circ f$ for the composition of functions $g$ and $f$.

\begin{code}
id : ∀ (A : Set) → A → A
id A x = x

infix 75 _∘_
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)
\end{code}

\subsection{Equality}

We use the inductively defined equality $=$ on every datatype.

\begin{code}
data _≡_ {A : Set} (a : A) : A → Set where
  ref : a ≡ a

subst : ∀ {A : Set} (P : A → Set) {a} {b} → a ≡ b → P a → P b
subst P ref Pa = Pa

sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
sym ref = ref

trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans ref ref = ref

wd : ∀ {A B : Set} (f : A → B) {a a' : A} → a ≡ a' → f a ≡ f a'
wd _ ref = ref

wd2 : ∀ {A B C : Set} (f : A → B → C) {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
wd2 _ ref ref = ref

module Equational-Reasoning (A : Set) where
  ∵_ : ∀ (a : A) → a ≡ a
  ∵ _ = ref

  _≡_[_] : ∀ {a b : A} → a ≡ b → ∀ c → b ≡ c → a ≡ c
  δ ≡ c [ δ' ] = trans δ δ'

  _≡_[[_]] : ∀ {a b : A} → a ≡ b → ∀ c → c ≡ b → a ≡ c
  δ ≡ c [[ δ' ]] = trans δ (sym δ')
\end{code}

We also write $f \sim g$ iff the functions $f$ and $g$ are extensionally equal, that is, $f(x) = g(x)$ for all $x$.

\begin{code}
infix 50 _∼_
_∼_ : ∀ {A B : Set} → (A → B) → (A → B) → Set
f ∼ g = ∀ x → f x ≡ g x
\end{code}

\section{Datatypes}

\newcommand{\FinSet}{\mathbf{FinSet}}
We introduce a universe $\FinSet$ of (names of) finite sets.  There is an empty set $\emptyset : \FinSet$,
and for every $A : \FinSet$, the type $A + 1 : \FinSet$ has one more element:
\[ A + 1 = \{ \bot \} \uplus \{ \uparrow a : a \in A \} \]

\begin{code}
data FinSet : Set where
  ∅ : FinSet
  Lift : FinSet → FinSet

data El : FinSet → Set where
  ⊥ : ∀ {V} → El (Lift V)
  ↑ : ∀ {V} → El V → El (Lift V)
\end{code}

Given $f : A \rightarrow B$, define $f + 1 : A + 1 \rightarrow B + 1$ by
\begin{align*}
(f + 1)(\bot) & = \bot \\
(f + 1)(\uparrow x) & = \uparrow f(x)
\end{align*}

\begin{code}
lift : ∀ {U} {V} → (El U → El V) → El (Lift U) → El (Lift V)
lift _ ⊥ = ⊥
lift f (↑ x) = ↑ (f x)

liftwd : ∀ {U} {V} {f g : El U → El V} → f ∼ g → lift f ∼ lift g
liftwd f-is-g ⊥ = ref
liftwd f-is-g (↑ x) = wd ↑ (f-is-g x)
\end{code}

This makes $(-) + 1$ into a functor $\FinSet \rightarrow \FinSet$; that is,
\begin{align*}
\id{V} + 1 & = \id{V + 1} \\
(g \circ f) + 1 & = (g + 1) \circ (f + 1)
\end{align*}

\begin{code}
liftid : ∀ {V} → lift (id (El V)) ∼ id (El (Lift V))
liftid ⊥ = ref
liftid (↑ _) = ref

liftcomp : ∀ {U} {V} {W} {g : El V → El W} {f : El U → El V} → lift (g ∘ f) ∼ lift g ∘ lift f
liftcomp ⊥ = ref
liftcomp (↑ _) = ref
\end{code}
