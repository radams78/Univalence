\section{Preliminaries}

\begin{code}
module Prelims where
open import Level using ()

{-postulate Level : Set
postulate zro : Level
postulate suc : Level → Level -}
\end{code}

\subsection{The Empty Type}

\begin{code}
data False : Set where
\end{code}

\subsection{Conjunction}

\begin{code}
data _∧_ {i} (P Q : Set i) : Set i where
  _,_ : P → Q → P ∧ Q

π₁ : ∀ {i} {P Q : Set i} → P ∧ Q → P
π₁ (x , _) = x

π₂ : ∀ {i} {P Q : Set i} → P ∧ Q → Q
π₂ (_ , y) = y
\end{code}

\subsection{Functions}

\begin{code}
infix 75 _∘_
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)
\end{code}

\subsection{Equality}

We use the inductively defined equality $=$ on every datatype.

\begin{code}
infix 50 _≡_
data _≡_ {A : Set} (a : A) : A → Set where
  ref : a ≡ a

subst : ∀ {i} {A : Set} (P : A → Set i) {a} {b} → a ≡ b → P a → P b
subst P ref Pa = Pa

subst2 : ∀ {A B : Set} (P : A → B → Set) {a a' b b'} → a ≡ a' → b ≡ b' → P a b → P a' b'
subst2 P ref ref Pab = Pab

sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
sym ref = ref

trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans ref ref = ref

wd : ∀ {A B : Set} (f : A → B) {a a' : A} → a ≡ a' → f a ≡ f a'
wd _ ref = ref

wd2 : ∀ {A B C : Set} (f : A → B → C) {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
wd2 _ ref ref = ref

module Equational-Reasoning (A : Set) where
  infix 2 ∵_
  ∵_ : ∀ (a : A) → a ≡ a
  ∵ _ = ref

  infix 1 _≡_[_]
  _≡_[_] : ∀ {a b : A} → a ≡ b → ∀ c → b ≡ c → a ≡ c
  δ ≡ c [ δ' ] = trans δ δ'

  infix 1 _≡_[[_]]
  _≡_[[_]] : ∀ {a b : A} → a ≡ b → ∀ c → c ≡ b → a ≡ c
  δ ≡ c [[ δ' ]] = trans δ (sym δ')
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

lift : ∀ {A} {B} → (El A → El B) → El (Lift A) → El (Lift B)
lift _ ⊥ = ⊥
lift f (↑ x) = ↑ (f x)
\end{code}
