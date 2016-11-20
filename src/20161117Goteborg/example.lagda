\begin{code}
module 20161117Goteborg.example where

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A
\end{code}

%<*Term>
\begin{code}
data Term : Set → Set where
  var : ∀ {V} → V → Term V
  app : ∀ {V} → Term V → Term V → Term V
  Λ   : ∀ {V} → Term (Maybe V) → Term V
\end{code}
%</Term>

\begin{code}
postulate Sub : Set → Set → Set
postulate _•_ : ∀ {U V W} → Sub V W → Sub U V → Sub U W
postulate _≡_ : ∀ {A : Set} → A → A → Set
postulate sub : ∀ {U V} → Sub U V → Term U → Term V
postulate sublm' : ∀ {U V W} {σ : Sub V W} {ρ : Sub U V} {M : Term U} →
                   sub (σ • ρ) M ≡ sub σ (sub ρ M)
\end{code}

%<*Sub>
\begin{code}
sublm : ∀ {U V W} 
  {σ : Sub V W} {ρ : Sub U V} {M : Term U} →
  sub (σ • ρ) M ≡ sub σ (sub ρ M)
\end{code}
%</Sub>

\begin{code}
sublm = sublm'

open import Grammar.Taxonomy
\end{code}

%<*Taxonomy>
\begin{code}
data lmmVK : Set where
  -producer : lmmVK
  -consumer : lmmVK

data lmmNVK : Set where
  -command : lmmNVK

lmmKinds : Taxonomy
lmmKinds = record { 
  VarKind = lmmVK ; 
  NonVarKind = lmmNVK }
\end{code}
%</Taxonomy>

\begin{code}
open import Grammar.Base
open Taxonomy lmmKinds

prod : ExpKind
prod = varKind -producer

cons : ExpKind
cons = varKind -consumer

comm : ExpKind
comm = nonVarKind -command
\end{code}

%<*Grammar>
\begin{code}
data lmmCon : ConKind → Set where
  Λ : lmmCon ((-producer ⟶ prod ✧) ⟶ prod ✧)
  μ : lmmCon ((-producer ⟶ comm ✧) ⟶ prod ✧)
  μ∼ : lmmCon ((-producer ⟶ comm ✧) ⟶ cons ✧)
  app : lmmCon (prod ✧ ⟶ cons ✧ ⟶ cons ✧)
  〈|〉 : lmmCon (prod ✧ ⟶ cons ✧ ⟶ comm ✧)
\end{code}
%</Grammar>
