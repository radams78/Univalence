\begin{code}
module PL where
open import Prelims
\end{code}

\section{Propositional Logic}

Fix sets of \emph{proof variables} and \emph{term variables}.

The syntax of the system is given by the following grammar.

\newcommand{\vald}{\ensuremath{\ \mathrm{valid}}}
%Changes from Marc and Thierry's system:
%Taken out the proof c of \bot
\[ \begin{array}{lrcl}
\text{Proof} & \delta & ::= & p \mid \delta \delta \mid \lambda p : \phi . \delta \\
\text{Proposition} & φ & ::= & ⊥ \mid \phi \rightarrow \phi \\
\text{Proof Context} & \Delta & ::= & \langle \rangle \mid \Delta, p : \phi \\
\text{Judgement} & \mathcal{J} & ::= & \Delta \vdash \delta : \phi
\end{array} \]
where $p$ ranges over proof variables and $x$ ranges over term variables.  The variable $p$ is bound within $\delta$ in the proof $\lambda p : \phi . \delta$,
and the variable $x$ is bound within $M$ in the term $\lambda x : A . M$.  We identify proofs and terms up to $\alpha$-conversion.

\newcommand{\FV}[1]{\mathrm{FV} \left( {#1} \right)}
\newcommand{\Proof}[1]{\mathbf{Proof} \left( {#1} \right)}
We write $\Proof{P}$ for the set of all proofs $\delta$ with $\FV{\delta} \subseteq V$.

\begin{code}
infix 75 _⇒_
data Prp : Set where
  ⊥ : Prp
  _⇒_ : Prp → Prp → Prp

infix 80 _,_
data PContext : FinSet → Set where
  〈〉 : PContext ∅
  _,_ : ∀ {P} → PContext P → Prp → PContext (Lift P)

--Proof V P is the set of all proofs with term variables among V and proof variables among P
data Proof : FinSet → Set where
  var : ∀ {P} → El P → Proof P
  app : ∀ {P} → Proof P → Proof P → Proof P
  Λ : ∀ {P} → Prp → Proof (Lift P) → Proof P
\end{code}

Let $P, Q : \FinSet$.  A \emph{replacement} from $P$ to $Q$ is just a function $P \rightarrow Q$.  Given a term $M : \Proof{P}$
and a replacement $\rho : P \rightarrow Q$, we write $M \{ \rho \} : \Proof{Q}$ for the result of replacing each variable $x$ in
$M$ with $\rho(x)$.

\begin{code}
infix 60 _<_>
_<_> : ∀ {P Q} → Proof P → Rep P Q → Proof Q
var p < ρ > = var (ρ p)
app δ ε < ρ > = app (δ < ρ >) (ε < ρ >)
Λ φ δ < ρ > = Λ φ (δ < lift ρ >)
\end{code}

With this as the action on arrows, $\Proof{}$ becomes a functor $\FinSet \rightarrow \Set$.

\begin{code}
repwd : ∀ {P Q : FinSet} {ρ ρ' : El P → El Q} → ρ ∼ ρ' → ∀ δ → δ < ρ > ≡ δ < ρ' >
repwd ρ-is-ρ' (var p) = wd var (ρ-is-ρ' p)
repwd ρ-is-ρ' (app δ ε) = wd2 app (repwd ρ-is-ρ' δ) (repwd ρ-is-ρ' ε)
repwd ρ-is-ρ' (Λ φ δ) = wd (Λ φ) (repwd (liftwd ρ-is-ρ') δ)

repid : ∀ {Q : FinSet} δ → δ < id (El Q) > ≡ δ
repid (var _) = ref
repid (app δ ε) = wd2 app (repid δ) (repid ε)
repid {Q} (Λ φ δ) = wd (Λ φ) (let open Equational-Reasoning (Proof (Lift Q)) in 
  ∵ δ < lift (id (El Q)) >
  ≡ δ < id (El (Lift Q)) >  [ repwd liftid δ ]
  ≡ δ                       [ repid δ ])

repcomp : ∀ {P Q R : FinSet} (ρ : El Q → El R) (σ : El P → El Q) M → M < ρ ∘ σ > ≡ M < σ > < ρ >
repcomp ρ σ (var _) = ref
repcomp ρ σ (app δ ε) = wd2 app (repcomp ρ σ δ) (repcomp ρ σ ε)
repcomp {R = R} ρ σ (Λ φ δ) = wd (Λ φ) (let open Equational-Reasoning (Proof (Lift R)) in 
  ∵ δ < lift (ρ ∘ σ) >
  ≡ δ < lift ρ ∘ lift σ >     [ repwd liftcomp δ ]
  ≡ (δ < lift σ >) < lift ρ > [ repcomp _ _ δ ])
\end{code}

A \emph{substitution} $\sigma$ from $P$ to $Q$, $\sigma : P \Rightarrow Q$, is a function $\sigma : P \rightarrow \Proof{Q}$.

\begin{code}
Sub : FinSet → FinSet → Set
Sub P Q = El P → Proof Q
\end{code}

The identity substitution $\id{Q} : Q \Rightarrow Q$ is defined as follows.

\begin{code}
idSub : ∀ Q → Sub Q Q
idSub _ = var
\end{code}

Given $\sigma : P \Rightarrow Q$ and $M : \Proof{P}$, we want to define $M[\sigma] : \Proof{Q}$, the result of applying the substitution $\sigma$ to $M$.  Only after this will we be able to define the composition of two substitutions.  However, there is some work we need to do before we are able to do this.

We can define the composition of a substitution and a replacement as follows.
\begin{code}
infix 75 _•₁_
_•₁_ : ∀ {P} {Q} {R} → Rep Q R → Sub P Q → Sub P R
(ρ •₁ σ) u = σ u < ρ >
\end{code}

(On the other side, given $\rho : P \rightarrow Q$ and $\sigma : Q \Rightarrow R$, the composition is just function composition $\sigma \circ \rho : P \Rightarrow R$.)

Given a substitution $\sigma : P \Rightarrow Q$,  define the substitution $\sigma + 1 :
P + 1 \Rightarrow Q + 1$ as follows.

\begin{code}
liftSub : ∀ {P} {Q} → Sub P Q → Sub (Lift P) (Lift Q)
liftSub _ ⊥ = var ⊥
liftSub σ (↑ x) = σ x < ↑ >

liftSub-wd : ∀ {P Q} {σ σ' : Sub P Q} → σ ∼ σ' → liftSub σ ∼ liftSub σ'
liftSub-wd σ-is-σ' ⊥ = ref
liftSub-wd σ-is-σ' (↑ x) = wd (λ x → x < ↑ >) (σ-is-σ' x)
\end{code}

\begin{lemma}
The operations $\bullet$ and $(-) + 1$ satisfiesd the following properties.
\begin{enumerate}
\item
$\id{Q} + 1 = \id{Q + 1}$
\item
For $\rho : Q → R$ and $\sigma : P \Rightarrow Q$, we have $(\rho \bullet \sigma) + 1 = (\rho + 1) \bullet (\sigma + 1)$.
\item
For $\sigma : Q \Rightarrow R$ and $\rho : P \rightarrow Q$, we have $(\sigma \circ \rho) + 1 = (\sigma + 1) \circ (\rho + 1)$.
\end{enumerate}
\end{lemma}

\begin{code}
liftSub-id : ∀ {Q : FinSet} → liftSub (idSub Q) ∼ idSub (Lift Q)
liftSub-id ⊥ = ref
liftSub-id (↑ x) = ref

liftSub-comp₁ : ∀ {P Q R : FinSet} (σ : Sub P Q) (ρ : Rep Q R) → 
  liftSub (ρ •₁ σ) ∼ lift ρ •₁ liftSub σ
liftSub-comp₁ σ ρ ⊥ = ref
liftSub-comp₁ {R = R} σ ρ (↑ x) = let open Equational-Reasoning (Proof (Lift R)) in 
   ∵ σ x < ρ > < ↑ > 
   ≡ σ x < ↑ ∘ ρ >        [[ repcomp ↑ ρ (σ x) ]]
   ≡ σ x < ↑ > < lift ρ > [ repcomp (lift ρ) ↑ (σ x) ]
--because lift ρ (↑ x) = ↑ (ρ x)

liftSub-comp₂ : ∀ {P Q R : FinSet} (σ : Sub Q R) (ρ : Rep P Q) →
  liftSub (σ ∘ ρ) ∼ liftSub σ ∘ lift ρ
liftSub-comp₂ σ ρ ⊥ = ref
liftSub-comp₂ σ ρ (↑ x) = ref
\end{code}

Now define $M[\sigma]$ as follows.

\begin{code}
infix 60 _⟦_⟧
_⟦_⟧ : ∀ {P Q : FinSet} → Proof P → Sub P Q → Proof Q
(var x)   ⟦ σ ⟧ = σ x
(app δ ε) ⟦ σ ⟧ = app (δ ⟦ σ ⟧) (ε ⟦ σ ⟧)
(Λ A δ)   ⟦ σ ⟧ = Λ A (δ ⟦ liftSub σ ⟧)

subwd : ∀ {P Q : FinSet} {σ σ' : Sub P Q} → σ ∼ σ' → ∀ δ → δ ⟦ σ ⟧ ≡ δ ⟦ σ' ⟧
subwd σ-is-σ' (var x) = σ-is-σ' x
subwd σ-is-σ' (app δ ε) = wd2 app (subwd σ-is-σ' δ) (subwd σ-is-σ' ε)
subwd σ-is-σ' (Λ A δ) = wd (Λ A) (subwd (liftSub-wd σ-is-σ') δ)
\end{code}

This interacts with our previous operations in a good way:
\begin{lemma}
\begin{enumerate}
\item
$M[\id{Q}] \equiv M$
\item
$M[\rho \bullet \sigma] \equiv δ [ \sigma ] \{ \rho \}$
\item
$M[\sigma \circ \rho] \equiv δ < \rho > [ \sigma ]$
\end{enumerate}
\end{lemma}

\begin{code}
subid : ∀ {Q : FinSet} (δ : Proof Q) → δ ⟦ idSub Q ⟧ ≡ δ
subid (var x) = ref
subid (app δ ε) = wd2 app (subid δ) (subid ε)
subid {Q} (Λ A δ) = let open Equational-Reasoning (Proof Q) in 
  ∵ Λ A (δ ⟦ liftSub (idSub Q) ⟧)
  ≡ Λ A (δ ⟦ idSub (Lift Q) ⟧)     [ wd (Λ A) (subwd liftSub-id δ) ]
  ≡ Λ A δ                          [ wd (Λ A) (subid δ) ]

rep-sub : ∀ {P} {Q} {R} (σ : Sub P Q) (ρ : Rep Q R) (δ : Proof P) → δ ⟦ σ ⟧ < ρ > ≡ δ ⟦ ρ •₁ σ ⟧
rep-sub σ ρ (var x) = ref
rep-sub σ ρ (app δ ε) = wd2 app (rep-sub σ ρ δ) (rep-sub σ ρ ε)
rep-sub {R = R} σ ρ (Λ A δ) = let open Equational-Reasoning (Proof R) in 
  ∵ Λ A ((δ ⟦ liftSub σ ⟧) < lift ρ >) 
  ≡ Λ A (δ ⟦ lift ρ •₁ liftSub σ ⟧) [ wd (Λ A) (rep-sub (liftSub σ) (lift ρ) δ) ]
  ≡ Λ A (δ ⟦ liftSub (ρ •₁ σ) ⟧)    [[ wd (Λ A) (subwd (liftSub-comp₁ σ ρ) δ) ]]

sub-rep : ∀ {P} {Q} {R} (σ : Sub Q R) (ρ : Rep P Q) δ → δ < ρ > ⟦ σ ⟧ ≡ δ ⟦ σ ∘ ρ ⟧
sub-rep σ ρ (var x) = ref
sub-rep σ ρ (app δ ε) = wd2 app (sub-rep σ ρ δ) (sub-rep σ ρ ε)
sub-rep {R = R} σ ρ (Λ A δ) = let open Equational-Reasoning (Proof R) in 
  ∵ Λ A ((δ < lift ρ >) ⟦ liftSub σ ⟧)
  ≡ Λ A (δ ⟦ liftSub σ ∘ lift ρ ⟧)      [ wd (Λ A) (sub-rep (liftSub σ) (lift ρ) δ) ]
  ≡ Λ A (δ ⟦ liftSub (σ ∘ ρ) ⟧)         [[ wd (Λ A) (subwd (liftSub-comp₂ σ ρ) δ) ]]
\end{code}

We define the composition of two substitutions, as follows.

\begin{code}
infix 75 _•_
_•_ : ∀ {P Q R : FinSet} → Sub Q R → Sub P Q → Sub P R
(σ • ρ) x = ρ x ⟦ σ ⟧
\end{code}

\begin{lemma}
Let $\sigma : Q \Rightarrow R$ and $\rho : P \Rightarrow Q$.
\begin{enumerate}
\item
$(\sigma \bullet \rho) + 1 = (\sigma + 1) \bullet (\rho + 1)$
\item
$M[\sigma \bullet \rho] \equiv δ [ \rho ] [ \sigma ]$
\end{enumerate}
\end{lemma}

\begin{code}
liftSub-comp : ∀ {P} {Q} {R} (σ : Sub Q R) (ρ : Sub P Q) →
  liftSub (σ • ρ) ∼ liftSub σ • liftSub ρ
liftSub-comp σ ρ ⊥ = ref
liftSub-comp σ ρ (↑ x) = trans (rep-sub σ ↑ (ρ x)) (sym (sub-rep (liftSub σ) ↑ (ρ x)))

subcomp : ∀ {P} {Q} {R} (σ : Sub Q R) (ρ : Sub P Q) δ → δ ⟦ σ • ρ ⟧ ≡ δ ⟦ ρ ⟧ ⟦ σ ⟧
subcomp σ ρ (var x) = ref
subcomp σ ρ (app δ ε) = wd2 app (subcomp σ ρ δ) (subcomp σ ρ ε)
subcomp σ ρ (Λ A δ) = wd (Λ A) (trans (subwd (liftSub-comp σ ρ) δ)  (subcomp (liftSub σ) (liftSub ρ) δ))
\end{code}

\begin{lemma}
The finite sets and substitutions form a category under this composition.
\end{lemma}

\begin{code}
assoc : ∀ {P Q R X} {ρ : Sub R X} {σ : Sub Q R} {τ : Sub P Q} →
  ρ • (σ • τ) ∼ (ρ • σ) • τ
assoc {P} {Q} {R} {X} {ρ} {σ} {τ} x = sym (subcomp ρ σ (τ x))

subunitl : ∀ {P} {Q} {σ : Sub P Q} → idSub Q • σ ∼ σ
subunitl {P} {Q} {σ} x = subid (σ x)

subunitr : ∀ {P} {Q} {σ : Sub P Q} → σ • idSub P ∼ σ
subunitr _ = ref

-- The second monad law

rep-is-sub : ∀ {P} {Q} {ρ : El P → El Q} δ → δ < ρ > ≡ δ ⟦ var ∘ ρ ⟧
rep-is-sub (var x) = ref
rep-is-sub (app δ ε) = wd2 app (rep-is-sub δ) (rep-is-sub ε)
rep-is-sub {Q = Q} {ρ} (Λ A δ) = let open Equational-Reasoning (Proof Q) in 
  ∵ Λ A (δ < lift ρ >)
  ≡ Λ A (δ ⟦ var ∘ lift ρ ⟧)         [ wd (Λ A) (rep-is-sub δ) ]
  ≡ Λ A (δ ⟦ liftSub var ∘ lift ρ ⟧) [[ wd (Λ A) (subwd (λ x → liftSub-id (lift ρ x)) δ) ]]
  ≡ Λ A (δ ⟦ liftSub (var ∘ ρ) ⟧)    [[ wd (Λ A) (subwd (liftSub-comp₂ var ρ) δ) ]]
--wd (Λ A) (trans (rep-is-sub δ) (subwd {!!} δ))

propof : ∀ {P} → El P → PContext P → Prp
propof ⊥ (_ , φ) = φ
propof (↑ p) (Γ , _) = propof p Γ

liftSub-var' : ∀ {P} {Q} (ρ : El P → El Q) → liftSub (var ∘ ρ) ∼ var ∘ lift ρ
liftSub-var' ρ ⊥ = ref
liftSub-var' ρ (↑ x) = ref

botsub : ∀ {Q} → Proof Q → Sub (Lift Q) Q
botsub δ ⊥ = δ
botsub _ (↑ x) = var x

sub-botsub : ∀ {P} {Q} (σ : Sub P Q) (δ : Proof P) (x : El (Lift P)) →
  botsub δ x ⟦ σ ⟧ ≡ liftSub σ x ⟦ botsub (δ ⟦ σ ⟧) ⟧
sub-botsub σ δ ⊥ = ref
sub-botsub σ δ (↑ x) = let open Equational-Reasoning (Proof _) in 
  ∵ σ x
  ≡ σ x ⟦ idSub _ ⟧                    [[ subid (σ x) ]]
  ≡ σ x < ↑ > ⟦ botsub (δ ⟦ σ ⟧) ⟧     [[ sub-rep (botsub (δ ⟦ σ ⟧)) ↑ (σ x) ]]

rep-botsub : ∀ {P} {Q} (ρ : El P → El Q) (δ : Proof P) (x : El (Lift P)) →
  botsub δ x < ρ > ≡ botsub (δ < ρ >) (lift ρ x)
rep-botsub ρ δ x = trans (rep-is-sub (botsub δ x)) 
  (trans (sub-botsub (var ∘ ρ) δ x) (trans (subwd (λ x₁ → wd (λ y → botsub y x₁) (sym (rep-is-sub δ))) (liftSub (λ z → var (ρ z)) x)) 
  (wd (λ x → x ⟦ botsub (δ < ρ >)⟧) (liftSub-var' ρ x))))
--TODO Inline this?

subbot : ∀ {Q} → Proof (Lift Q) → Proof Q → Proof Q
subbot δ ε = δ ⟦ botsub ε ⟧
\end{code}

We write $δ ≃ N$ iff the terms $M$ and $N$ are $\beta$-convertible, and similarly for proofs.

\begin{code}
data _↠_ : ∀ {Q} → Proof Q → Proof Q → Set where
  β : ∀ {Q} A (δ : Proof (Lift Q)) ε → app (Λ A δ) ε ↠ subbot δ ε
  ref : ∀ {Q} {δ : Proof Q} → δ ↠ δ
  ↠trans : ∀ {Q} {δ ε P : Proof Q} → δ ↠ ε → ε ↠ P → δ ↠ P
  app : ∀ {Q} {δ δ' ε ε' : Proof Q} → δ ↠ δ' → ε ↠ ε' → app δ ε ↠ app δ' ε'
  ξ : ∀ {Q} {δ ε : Proof (Lift Q)} {φ} → δ ↠ ε → Λ φ δ ↠ Λ φ ε

repred : ∀ {P} {Q} {ρ : El P → El Q} {δ ε : Proof P} → δ ↠ ε → δ < ρ > ↠ ε < ρ >
repred {P} {Q} {ρ} (β A δ ε) = subst (λ x → app (Λ A (δ < lift ρ > )) (ε < ρ >) ↠ x) (sym (trans (rep-sub (botsub ε) ρ δ) (sym (trans (sub-rep _ _ δ) (subwd (λ x → sym (rep-botsub ρ ε x)) δ))))) (β A (δ < lift _ >) (ε < _ >))
repred ref = ref
repred (↠trans M↠ε N↠P) = ↠trans (repred M↠ε) (repred N↠P)
repred (app M↠ε M'↠N') = app (repred M↠ε) (repred M'↠N')
repred (ξ M↠ε) = ξ (repred M↠ε)

liftSub-red : ∀ {P} {Q} {ρ σ : Sub P Q} → (∀ x → ρ x ↠ σ x) → (∀ x → liftSub ρ x ↠ liftSub σ x)
liftSub-red ρ↠σ ⊥ = ref
liftSub-red ρ↠σ (↑ x) = repred (ρ↠σ x)

subred : ∀ {P} {Q} {ρ σ : Sub P Q} (δ : Proof P) → (∀ x → ρ x ↠ σ x) → δ ⟦ ρ ⟧ ↠ δ ⟦ σ ⟧
subred (var x) ρ↠σ = ρ↠σ x
subred (app δ ε) ρ↠σ = app (subred δ ρ↠σ) (subred ε ρ↠σ)
subred (Λ φ δ) ρ↠σ = ξ (subred δ (liftSub-red ρ↠σ))

subsub : ∀ {P} {Q} {R} (σ : Sub Q R) (ρ : Sub P Q) δ → δ ⟦ ρ ⟧ ⟦ σ ⟧ ≡ δ ⟦ σ • ρ ⟧
subsub σ ρ (var x) = ref
subsub σ ρ (app δ ε) = wd2 app (subsub σ ρ δ) (subsub σ ρ ε)
subsub σ ρ (Λ A δ) = wd (Λ A) (trans (subsub (liftSub σ) (liftSub ρ) δ) 
  (subwd (λ x → sym (liftSub-comp σ ρ x)) δ))

subredr : ∀ {P} {Q} {σ : Sub P Q} {δ ε : Proof P} → δ ↠ ε → δ ⟦ σ ⟧ ↠ ε ⟦ σ ⟧
subredr {P} {Q} {σ} (β A δ ε) = subst (λ x → app (Λ A (δ ⟦ liftSub σ ⟧)) (ε ⟦ σ ⟧) ↠ x) (sym (trans (subsub σ (botsub ε) δ) 
  (sym (trans (subsub (botsub (ε ⟦ σ ⟧)) (liftSub σ) δ) (subwd (λ x → sym (sub-botsub σ ε x)) δ))))) (β A (δ ⟦ liftSub σ ⟧) (ε ⟦ σ ⟧))
subredr ref = ref
subredr (↠trans M↠ε N↠P) = ↠trans (subredr M↠ε) (subredr N↠P)
subredr (app M↠M' N↠N') = app (subredr M↠M') (subredr N↠N')
subredr (ξ δ↠δ') = ξ (subredr δ↠δ')

data _≃_ : ∀ {Q} → Proof Q → Proof Q → Set₁ where
  β : ∀ {Q} {A} {δ : Proof (Lift Q)} {ε} → app (Λ A δ) ε ≃ subbot δ ε
  ref : ∀ {Q} {δ : Proof Q} → δ ≃ δ
  ≃sym : ∀ {Q} {δ ε : Proof Q} → δ ≃ ε → ε ≃ ε
  ≃trans : ∀ {Q} {δ ε P : Proof Q} → δ ≃ ε → ε ≃ P → δ ≃ P
  app : ∀ {Q} {δ M' ε N' : Proof Q} → δ ≃ M' → ε ≃ N' → app δ ε ≃ app M' N'
  Λ : ∀ {Q} {δ ε : Proof (Lift Q)} {A} → δ ≃ ε → Λ A δ ≃ Λ A ε
\end{code}

The \emph{strongly normalizable} terms are defined inductively as follows.

\begin{code}
data SN {Q} : Proof Q → Set₁ where
  SNI : ∀ {δ} → (∀ ε → δ ↠ ε → SN ε) → SN δ
\end{code}

\begin{lemma}
\begin{enumerate}
\item
If $δε \in SN$ then $δ \in SN$ and $ε \in SN$.
\item
If $δ[x:=N] \in SN$ then $δ \in SN$.
\item
If $δ \in SN$ and $δ \rhd N$ then $ε \in SN$.
\item
If $δ[x:=N]\vec{P} \in SN$ and $ε \in SN$ then $(\lambda x δ) ε \vec{P} \in SN$.
\end{enumerate}
\end{lemma}

\begin{code}
SNappl : ∀ {Q} {δ ε : Proof Q} → SN (app δ ε) → SN δ
SNappl {Q} {δ} {ε} (SNI δN-is-SN) = SNI (λ P δ▷P → SNappl (δN-is-SN (app P ε) (app δ▷P ref)))

SNappr : ∀ {Q} {δ ε : Proof Q} → SN (app δ ε) → SN ε
SNappr {Q} {δ} {ε} (SNI δN-is-SN) = SNI (λ P N▷P → SNappr (δN-is-SN (app δ P) (app ref N▷P)))

SNsub : ∀ {Q} {δ : Proof (Lift Q)} {ε} → SN (subbot δ ε) → SN δ
SNsub {Q} {δ} {ε} (SNI δN-is-SN) = SNI (λ P δ▷P → SNsub (δN-is-SN (P ⟦ botsub ε ⟧) (subredr δ▷P)))
\end{code}

The rules of deduction of the system are as follows.

\[ \infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald} \]

\[ \infer{\Gamma \vdash \delta \epsilon : \psi}{\Gamma \vdash \delta : \phi \rightarrow \psi}{\Gamma \vdash \epsilon : \phi} \]

\[ \infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \rightarrow \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]


\begin{code}
data _⊢_∶∶_ : ∀ {P} → PContext P → Proof P → Prp → Set₁ where
  var : ∀ {P} {Γ : PContext P} {p} → Γ ⊢ var p ∶∶ propof p Γ
  app : ∀ {P} {Γ : PContext P} {δ} {ε} {φ} {ψ} → Γ ⊢ δ ∶∶ φ ⇒ ψ → Γ ⊢ ε ∶∶ φ → Γ ⊢ app δ ε ∶∶ ψ
  Λ : ∀ {P} {Γ : PContext P} {φ} {δ} {ψ} → Γ , φ ⊢ δ ∶∶ ψ → Γ ⊢ Λ φ δ ∶∶ φ ⇒ ψ
\end{code}



