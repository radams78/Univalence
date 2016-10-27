\AgdaHide{
\begin{code}
module PHOPL.Red where
open import Data.Empty renaming (⊥ to False)
open import Data.Unit
open import Data.Vec
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.PathSub
\end{code}
}

\subsection{The Reduction Relation}

\begin{definition}
We make the following definitions simultaneously:
\begin{enumerate}
\item
Let \emph{contraction} $\rhd$ be the relation consisting of the pairs $s \rhd t$ shown in Figure \ref{fig:red}, 
such that $s$ is closed, and every proper subexpression of $s$ is in normal form.
%The only time we need this restriction is that M is in normal form when reducing ref(λx:A.M)_NN' P

\begin{figure}
\begin{framed}
\begin{align*}
(\lambda x:A.M)N & \rhd M[x:=N] & (\lambda p:\phi.\delta)\epsilon & \rhd \delta[p:=\epsilon] \\
 \reff{\phi}^+ & \rhd \lambda p:\phi.p & \reff{\phi}^- & \rhd \lambda p:\phi.p \\
\univ{\phi}{\psi}{\delta}{\epsilon}^+ & \rhd \delta & \univ{\phi}{\psi}{\delta}{\epsilon}^- & \rhd \epsilon
\end{align*}
\begin{align*}
& \reff \phi \supset^* \univ{\psi}{\chi}{\delta}{\epsilon} \\
& \quad \rhd \mathsf{univ}_{\phi \supset \psi,\phi \supset \chi}(\lambda p : \phi \supset \psi. \lambda q : \phi . \delta (p q), 
\lambda p : \phi \supset \chi. \lambda q : \phi . \epsilon (p q)) \\
& \univ{\phi}{\psi}{\delta}{\epsilon} \supset^* \reff{\chi} \\
& \quad \rhd \univ{\phi \supset \chi}{\psi \supset \chi}{\lambda p : \phi \supset \chi . \lambda q : \psi .p (\epsilon q)}{\lambda p : \psi \supset \chi . \lambda q : \phi .p (\delta q)} \\
& \univ{\phi}{\psi}{\delta}{\epsilon} \supset^* \univ{\phi'}{\psi'}{\delta'}{\epsilon'} \\
& \quad \rhd \univ{\phi \supset \phi'}{\psi \supset \psi'}
{\lambda p : \phi \supset \phi' . \lambda q : \psi . \delta' (p (\epsilon q))}{\lambda p : \psi \supset \psi'. \lambda q : \phi . \epsilon' (p (\delta q))}
\end{align*}
\begin{align*}
\reff{\phi} \supset^* \reff{\psi} & \rhd \reff{\phi \supset \psi} \\
\reff{M}_{N_1N_2} \reff{N} & \rhd \reff{MN} \\
(\triplelambda e:x =_A y. P)_{MN}Q & \rhd P[x:=M, y:=N, e:=Q] \\
\text{If $P$ does not have the form } \reff{-}, \text{ then } \\ \reff{\lambda x:A.M}_{N,N'} P & \rhd M \{ x := P : N ∼ N' \}
\end{align*}
\end{framed}
\caption{Contractions for $\lambda o e$}
\label{fig:red}
\end{figure}
\item
{One-step reduction} $\rightarrow$ is the congruence generated by $\rhd$.  That is, the expression $s$ \emph{reduces in one step} to the expression $t$, $s \rightarrow t$, iff $t$ is formed from $s$ by replacing a subexpression $s'$ with a subterm $t'$, where $s' \rhd t'$.  (This subexpression may be in the subscripts of a path application; thus, if $M \rightarrow M'$, then $P_{MN}Q \rightarrow P_{M'N}Q$.)
\item
An expression $s$ is in \emph{normal form} iff there is no expression $t$ such that $s \rightarrow t$.
\end{enumerate}

\begin{code}
--Redex for a path ref ⊃* univ:
ru-redex-half : ∀ {V} → Term V → Term V → Proof V → Proof V
ru-redex-half {V} φ ψ δ = ΛP (φ ⊃ ψ) (ΛP (φ ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (var x₀))))

ru-redex : ∀ {V} → Term V → Term V → Term V → Proof V → Proof V → Path V
ru-redex φ ψ χ δ ε = univ (φ ⊃ ψ) (φ ⊃ χ) (ru-redex-half φ ψ δ) (ru-redex-half φ χ ε)

--Redex for a path univ ⊃* ref:
ur-redex-half : ∀ {V} → Term V → Term V → Term V → Proof V → Proof V
ur-redex-half φ ψ χ δ = ΛP (φ ⊃ ψ) (ΛP (χ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀))))

ur-redex : ∀ {V} → Term V → Term V → Term V → Proof V → Proof V → Path V
ur-redex φ ψ χ δ ε = univ (φ ⊃ χ) (ψ ⊃ χ) (ur-redex-half φ χ ψ ε) (ur-redex-half ψ χ φ δ)

--Redex for a path univ ⊃* univ;
uu-redex-half : ∀ {V} → Term V → Term V → Term V → Proof V → Proof V → Proof V
uu-redex-half φ φ' ψ δ ε = ΛP (φ ⊃ φ') (ΛP (ψ ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀)))))

uu-redex : ∀ {V} → Term V → Term V → Term V → Term V → Proof V → Proof V → Proof V → Proof V → Path V
uu-redex φ φ' ψ ψ' δ δ' ε ε' = univ (φ ⊃ φ') (ψ ⊃ ψ') (uu-redex-half φ φ' ψ δ' ε) (uu-redex-half ψ ψ' φ ε' δ)

data not-ref-univ {V} : Path V → Set where
  nruvar : ∀ e → not-ref-univ (var e)
  nru⊃*  : ∀ {P} {Q} → not-ref-univ (P ⊃* Q)
  nruλλλ : ∀ {A P} → not-ref-univ (λλλ A P)
  nruapp* : ∀ {M N P Q} → not-ref-univ (app* M N P Q)

data not-ref-λλλ {V} : Path V → Set where
  nrλvar : ∀ e → not-ref-λλλ (var e)
  nrλ⊃*  : ∀ {P Q} → not-ref-λλλ (P ⊃* Q)
  nrλuniv : ∀ {φ ψ δ ε} → not-ref-λλλ (univ φ ψ δ ε)
  nrλapp* : ∀ {M N P Q} → not-ref-λλλ (app* M N P Q)

data not-ref {V} : Path V → Set where
  nrλvar : ∀ e → not-ref (var e)
  nrλ⊃*  : ∀ {P Q} → not-ref (P ⊃* Q)
  nrλuniv : ∀ {φ ψ δ ε} → not-ref (univ φ ψ δ ε)
  nrλλλλ : ∀ {A P} → not-ref (λλλ A P)
  nrλapp* : ∀ {M N P Q} → not-ref (app* M N P Q)

--TODO Do the same for nfappT and nfappP

data R : Reduction
data nf : ∀ {V} {K} → Expression V K → Set

data R where
  βT : ∀ {V} {A} {M} {N} → R {V} -appTerm (ΛT A M ∷ N ∷ []) (M ⟦ x₀:= N ⟧)
  βR : ∀ {V} {φ} {δ} {ε} → nf (ΛP φ δ) → nf ε → R {V} -appProof (ΛP φ δ ∷ ε ∷ []) (δ ⟦ x₀:= ε ⟧)
  dir-ref : ∀ {V} {φ} {d} → nf (reff φ) → R {V} (-dir d) (reff φ ∷ []) (ΛP φ (var x₀))
  plus-univ : ∀ {V} {φ} {ψ} {δ} {ε} → nf (univ φ ψ δ ε) → R {V} (-dir -plus) (univ φ ψ δ ε ∷ []) δ 
  minus-univ : ∀ {V} {φ} {ψ} {δ} {ε} → nf (univ φ ψ δ ε) → R {V} (-dir -minus) (univ φ ψ δ ε ∷ []) ε
  ref⊃*univ : ∀ {V} {φ} {ψ} {χ} {δ} {ε} → nf (reff φ) → nf (univ ψ χ δ ε) → R {V} -imp* (reff φ ∷ univ ψ χ δ ε ∷ []) (ru-redex φ ψ χ δ ε)
  univ⊃*ref : ∀ {V} {φ} {ψ} {χ} {δ} {ε} → nf (univ φ ψ δ ε) → nf (reff χ) → R {V} -imp* (univ φ ψ δ ε ∷ reff χ ∷ []) (ur-redex φ ψ χ δ ε)
  univ⊃*univ : ∀ {V} {φ} {φ'} {ψ} {ψ'} {δ} {δ'} {ε} {ε'} → nf (univ φ ψ δ ε) → nf (univ φ' ψ' δ' ε') →
    R {V} -imp* (univ φ ψ δ ε ∷ univ φ' ψ' δ' ε' ∷ []) (uu-redex φ φ' ψ ψ' δ δ' ε ε')
  ref⊃*ref : ∀ {V} {φ} {ψ} → nf (reff φ) → nf (reff ψ) → R {V} -imp* (reff φ ∷ reff ψ ∷ []) (reff (φ ⊃ ψ))
  refref : ∀ {V} {M} {N} → nf (reff M) → nf (reff N) → R {V} -app* (N ∷ N ∷ reff M ∷ reff N ∷ []) (reff (appT M N))
  βE : ∀ {V} {M} {N} {A} {P} {Q} → nf M → nf N → nf (λλλ A P) → nf Q → R {V} -app* (M ∷ N ∷ λλλ A P ∷ Q ∷ []) 
    (P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧)
  reflam : ∀ {V} {N} {N'} {A} {M} {P} → nf N → nf N' → nf (reff (ΛT A M)) → nf P → not-ref P → R {V} -app* (N ∷ N' ∷ reff (ΛT A M) ∷ P ∷ []) (M ⟦⟦ x₀::= P ∶ x₀:= N ∼ x₀:= N' ⟧⟧)

data nf where
  nfvar  : ∀ {V} {K} (x : Var V K) → nf (var x)
  nf⊥    : ∀ {V} → nf {V} ⊥
  nf⊃    : ∀ {V} {φ ψ : Term V} → nf φ → nf ψ → nf (φ ⊃ ψ)
  nfΛT   : ∀ {V} A {M : Term (V , -Term)} → nf M → nf (ΛT A M)
  nfappTvar : ∀ {V} (x : Var V -Term) {M} → nf M → nf (appT (var x) M)
  nfappT⊥   : ∀ {V} {M : Term V} → nf M → nf (appT ⊥ M)
  nfappT⊃   : ∀ {V} {M N P : Term V} → nf M → nf N → nf P → nf (appT (M ⊃ N) P)
  nfappTappT : ∀ {V} {M N P : Term V} → nf (appT M N) → nf P → nf (appT (appT M N) P)
  nfΛP   : ∀ {V} {φ : Term V} {δ} → nf φ → nf δ → nf (ΛP φ δ)
  nfappPvar : ∀ {V} (p : Var V -Proof) {δ} → nf δ → nf (appP (var p) δ)
  nfappPappP : ∀ {V} {δ ε ε' : Proof V} → nf (appP δ ε) → nf ε' → nf (appP (appP δ ε) ε')
  nfappPdir : ∀ {V d} {P : Path V} {δ} → nf (dir d P) → nf δ → nf (appP (dir d P) δ)
  nfdirvar : ∀ {V d} (P : Path V) → nf P → not-ref-univ P → nf (dir d P)
  nfreff : ∀ {V} {M : Term V} → nf M → nf (reff M)
  nf⊃*l  : ∀ {V} {P Q : Path V} → nf P → nf Q → not-ref-univ P → nf (P ⊃* Q)
  nf⊃*r  : ∀ {V} {P Q : Path V} → nf P → nf Q → not-ref-univ Q → nf (P ⊃* Q)
  nfuniv : ∀ {V} {φ ψ : Term V} {δ ε} → nf φ → nf ψ → nf δ → nf ε → nf (univ φ ψ δ ε)
  nfλλλ  : ∀ {V A} {P : Path (V , -Term , -Term , -Path)} → nf P → nf (λλλ A P)
  nfapp* : ∀ {V} {M N : Term V} {P Q} → nf M → nf N → nf P → nf Q → not-ref-λλλ P → nf (app* M N P Q)

postulate R-det : ∀ {V} {K} {C} {c : Con (SK C K)} {E : ListAbs V C} {F} {G} → R c E F → R c E G → F ≡ G
{- R-det βT βT = refl
R-det (βR _ _) (βR _ _) = refl
R-det (dir-ref _) (dir-ref _) = refl
R-det (plus-univ _) (plus-univ _) = refl
R-det (minus-univ _) (minus-univ _) = refl
R-det (ref⊃*univ _ _) (ref⊃*univ _ _) = refl
R-det (univ⊃*ref _ _) (univ⊃*ref _ _) = refl
R-det (univ⊃*univ _ _) (univ⊃*univ _ _) = refl
R-det (ref⊃*ref _ _) (ref⊃*ref _ _) = refl
R-det (refref _ _) (refref _ _) = refl
R-det (refref _ _) (reflam _ _ _ _ ())
R-det (βE _ _ _ _) (βE _ _ _ _) = refl
R-det (reflam _ _ _ _ _) (reflam _ _ _ _ _) = refl
R-det (reflam _ _ _ _ ()) (refref _ _) -}
\end{code}

Let $\rightarrow^?$ be the reflexive closure of $\rightarrow$;
let $\twoheadrightarrow^+$ be the transitive closure;
let \emph{reduction} $\twoheadrightarrow$ be the reflexive, transitive closure; and \emph{conversion} $\simeq$ the equivalence relation generated by $\rightarrow$.
\end{definition}

\AgdaHide{
\begin{code}
open import Reduction PHOPL R public 

postulate nf-is-nf : ∀ {V K} {E E' : Expression V K} → nf E → E ⇒ E' → False
{- nf-is-nf (nfvar _) ()
nf-is-nf nf⊥ (redex ())
nf-is-nf nf⊥ (app ())
nf-is-nf (nf⊃ _ _) (redex ())
nf-is-nf (nf⊃ nfφ _) (app (appl φ⇒φ')) = nf-is-nf nfφ φ⇒φ'
nf-is-nf (nf⊃ _ nfψ) (app (appr (appl ψ⇒ψ'))) = nf-is-nf nfψ ψ⇒ψ'
nf-is-nf (nf⊃ _ _) (app (appr (appr ())))
nf-is-nf (nfΛT _ _) (redex ())
nf-is-nf (nfΛT _ nfM) (app (appl M⇒M')) = nf-is-nf nfM M⇒M'
nf-is-nf (nfΛT _ _) (app (appr ()))
nf-is-nf (nfappTvar _ _) (redex ())
nf-is-nf (nfappTvar _ _) (app (appl ()))
nf-is-nf (nfappTvar _ nfM) (app (appr (appl M⇒M'))) = nf-is-nf nfM M⇒M'
nf-is-nf (nfappTvar _ _) (app (appr (appr ())))
nf-is-nf (nfappT⊥ _) (redex ())
nf-is-nf (nfappT⊥ _) (app (appl ⊥⇒E')) = nf-is-nf nf⊥ ⊥⇒E'
nf-is-nf (nfappT⊥ nfM) (app (appr (appl M⇒M'))) = nf-is-nf nfM M⇒M'
nf-is-nf (nfappT⊥ _) (app (appr (appr ())))
nf-is-nf (nfappT⊃ _ _ _) (redex ())
nf-is-nf (nfappT⊃ nfM nfM' _) (app (appl M⊃M'⇒E')) = nf-is-nf (nf⊃ nfM nfM') M⊃M'⇒E'
nf-is-nf (nfappT⊃ _ _ nfN) (app (appr (appl N⇒N'))) = nf-is-nf nfN N⇒N'
nf-is-nf (nfappT⊃ _ _ _) (app (appr (appr ())))
nf-is-nf (nfappTappT _ _) (redex ())
nf-is-nf (nfappTappT nfMM' _) (app (appl MM'⇒E')) = nf-is-nf nfMM' MM'⇒E'
nf-is-nf (nfappTappT _ nfN) (app (appr (appl N⇒N'))) = nf-is-nf nfN N⇒N'
nf-is-nf (nfappTappT nfE nfE₁) (app (appr (appr ())))
nf-is-nf (nfΛP _ _) (redex ())
nf-is-nf (nfΛP nfφ _) (app (appl φ⇒φ')) = nf-is-nf nfφ φ⇒φ'
nf-is-nf (nfΛP _ nfδ) (app (appr (appl δ⇒δ'))) = nf-is-nf nfδ δ⇒δ'
nf-is-nf (nfΛP _ _) (app (appr (appr ())))
nf-is-nf (nfappPvar _ _) (redex ())
nf-is-nf (nfappPvar _ _) (app (appl ()))
nf-is-nf (nfappPvar _ nfδ) (app (appr (appl δ⇒δ'))) = nf-is-nf nfδ δ⇒δ'
nf-is-nf (nfappPvar _ _) (app (appr (appr ())))
nf-is-nf (nfappPappP _ _) (redex ())
nf-is-nf (nfappPappP nfδε _) (app (appl δε⇒E')) = nf-is-nf nfδε δε⇒E'
nf-is-nf (nfappPappP _ nfε') (app (appr (appl ε'⇒E'))) = nf-is-nf nfε' ε'⇒E'
nf-is-nf (nfappPappP _ _) (app (appr (appr ())))
nf-is-nf (nfappPdir _ _) (redex ())
nf-is-nf (nfappPdir nfdP _) (app (appl dP⇒E')) = nf-is-nf nfdP dP⇒E'
nf-is-nf (nfappPdir _ nfδ) (app (appr (appl δ⇒δ'))) = nf-is-nf nfδ δ⇒δ'
nf-is-nf (nfappPdir _ _) (app (appr (appr ())))
nf-is-nf (nfdirvar (var _) _ (nruvar _)) (redex ())
nf-is-nf (nfdirvar _ _ nru⊃*) (redex ())
nf-is-nf (nfdirvar _ _ nruλλλ) (redex ())
nf-is-nf (nfdirvar _ _ nruapp*) (redex ())
nf-is-nf (nfdirvar _ nfP _) (app (appl P⇒P')) = nf-is-nf nfP P⇒P'
nf-is-nf (nfdirvar _ _ _) (app (appr ()))
nf-is-nf (nfreff _) (redex ())
nf-is-nf (nfreff nfM) (app (appl M⇒M')) = nf-is-nf nfM M⇒M'
nf-is-nf (nfreff _) (app (appr ()))
nf-is-nf (nf⊃*l _ _ (nruvar _)) (redex ()) 
nf-is-nf (nf⊃*l _ _ nru⊃*) (redex ()) 
nf-is-nf (nf⊃*l _ _ nruλλλ) (redex ()) 
nf-is-nf (nf⊃*l _ _ nruapp*) (redex ()) 
nf-is-nf (nf⊃*l nfP _ _) (app (appl P⇒P')) = nf-is-nf nfP P⇒P'
nf-is-nf (nf⊃*l _ nfQ _) (app (appr (appl Q⇒Q'))) = nf-is-nf nfQ Q⇒Q'
nf-is-nf (nf⊃*l _ _ _) (app (appr (appr ())))
nf-is-nf (nf⊃*r _ _ (nruvar _)) (redex ()) 
nf-is-nf (nf⊃*r _ _ nru⊃*) (redex ()) 
nf-is-nf (nf⊃*r _ _ nruλλλ) (redex ()) 
nf-is-nf (nf⊃*r _ _ nruapp*) (redex ()) 
nf-is-nf (nf⊃*r nfP _ _) (app (appl P⇒P')) = nf-is-nf nfP P⇒P'
nf-is-nf (nf⊃*r _ nfQ _) (app (appr (appl Q⇒Q'))) = nf-is-nf nfQ Q⇒Q'
nf-is-nf (nf⊃*r _ _ _) (app (appr (appr ())))
nf-is-nf (nfuniv _ _ _ _) (redex ())
nf-is-nf (nfuniv nfφ _ _ _) (app (appl φ⇒φ')) = nf-is-nf nfφ φ⇒φ'
nf-is-nf (nfuniv _ nfψ _ _) (app (appr (appl ψ⇒ψ'))) = nf-is-nf nfψ ψ⇒ψ'
nf-is-nf (nfuniv _ _ nfδ _) (app (appr (appr (appl δ⇒δ')))) = nf-is-nf nfδ δ⇒δ'
nf-is-nf (nfuniv _ _ _ nfε) (app (appr (appr (appr (appl ε⇒ε'))))) = nf-is-nf nfε ε⇒ε'
nf-is-nf (nfuniv _ _ _ _) (app (appr (appr (appr (appr ())))))
nf-is-nf (nfλλλ _) (redex ())
nf-is-nf (nfλλλ nfP) (app (appl P⇒P')) = nf-is-nf nfP P⇒P'
nf-is-nf (nfλλλ _) (app (appr ()))
nf-is-nf (nfapp* _ _ _ _ (nrλvar _)) (redex ())
nf-is-nf (nfapp* _ _ _ _ nrλ⊃*) (redex ())
nf-is-nf (nfapp* _ _ _ _ nrλuniv) (redex ())
nf-is-nf (nfapp* _ _ _ _ nrλapp*) (redex ())
nf-is-nf (nfapp* nfM _ _ _ _) (app (appl M⇒M')) = nf-is-nf nfM M⇒M'
nf-is-nf (nfapp* _ nfN _ _ _) (app (appr (appl N⇒N'))) = nf-is-nf nfN N⇒N'
nf-is-nf (nfapp* _ _ nfP _ _) (app (appr (appr (appl P⇒P')))) = nf-is-nf nfP P⇒P'
nf-is-nf (nfapp* _ _ _ nfQ _) (app (appr (appr (appr (appl Q⇒Q'))))) = nf-is-nf nfQ Q⇒Q'
nf-is-nf (nfapp* _ _ _ _ _) (app (appr (appr (appr (appr ()))))) -}

nfredexproof : ∀ {V} {AA} {c : Con (SK AA (varKind -Proof))} {EE EE' : ListAbs V AA} {δ} → R c EE δ → EE ⇒ EE' → False
nfredexproof (βR nfΛPφδ _) (appl ΛPφδ⇒E') = nf-is-nf nfΛPφδ ΛPφδ⇒E'
nfredexproof (βR _ nfε) (appr (appl ε⇒ε')) = nf-is-nf nfε ε⇒ε'
nfredexproof (βR _ _) (appr (appr ()))
nfredexproof (dir-ref nfrefφ) (appl refφ⇒E') = nf-is-nf nfrefφ refφ⇒E'
nfredexproof (dir-ref _) (appr ())
nfredexproof (plus-univ nfP) (appl P⇒P') = nf-is-nf nfP P⇒P'
nfredexproof (plus-univ _) (appr ())
nfredexproof (minus-univ nfP) (appl P⇒P') = nf-is-nf nfP P⇒P'
nfredexproof (minus-univ _) (appr ())

nfredexpath : ∀ {V} {AA} {c : Con (SK AA (varKind -Path))} {EE EE' : ListAbs V AA} {P} → R c EE P → EE ⇒ EE' → False
nfredexpath (ref⊃*univ nfrefφ _) (appl refφ⇒EE') = nf-is-nf nfrefφ refφ⇒EE'
nfredexpath (ref⊃*univ _ nfunivδε) (appr (appl univδε⇒EE')) = nf-is-nf nfunivδε univδε⇒EE'
nfredexpath (ref⊃*univ _ _) (appr (appr ()))
nfredexpath (univ⊃*ref x x₁) (appl EE⇒EE') = {!!}
nfredexpath (univ⊃*ref x x₁) (appr EE⇒EE') = {!!}
nfredexpath (univ⊃*univ x x₁) EE⇒EE' = {!!}
nfredexpath (ref⊃*ref x x₁) EE⇒EE' = {!!}
nfredexpath (refref x x₁) EE⇒EE' = {!!}
nfredexpath (βE x x₁ x₂ x₃) EE⇒EE' = {!!}
nfredexpath (reflam x x₁ x₂ x₃ x₄) EE⇒EE' = {!!}
\end{code}
}

\begin{lm}
If $\univ{\phi}{\psi}{\delta}{\epsilon} \rightarrow E$ then $E$ is formed by reducing
one of $\phi$, $\psi$, $\delta$, $\epsilon$.
\end{lm}

\AgdaHide{
\begin{code}
postulate univ-osrE : ∀ {V} {φ} {ψ} {δ} {ε} {C : Path V → Set} →
                    (∀ φ' → φ ⇒ φ' → C (univ φ' ψ δ ε)) →
                    (∀ ψ' → ψ ⇒ ψ' → C (univ φ ψ' δ ε)) →
                    (∀ δ' → δ ⇒ δ' → C (univ φ ψ δ' ε)) →
                    (∀ ε' → ε ⇒ ε' → C (univ φ ψ δ ε')) →
                    ∀ {P} → univ φ ψ δ ε ⇒ P → C P
{- univ-osrE _ _ _ _ (redex ())
univ-osrE hypφ _ _ _ (app (appl φ⇒φ')) = hypφ _ φ⇒φ'
univ-osrE _ hypψ _ _ (app (appr (appl ψ⇒ψ'))) = hypψ _ ψ⇒ψ'
univ-osrE _ _ hypδ _ (app (appr (appr (appl δ⇒δ')))) = hypδ _ δ⇒δ'
univ-osrE _ _ _ hypε (app (appr (appr (appr (appl ε⇒ε'))))) = hypε _ ε⇒ε'
univ-osrE _ _ _ _ (app (appr (appr (appr (appr ()))))) -}

postulate eq-resp-conv : ∀ {V} {M M' N N' : Term V} {A : Type} →
                       M ≃ M' → N ≃ N' → M ≡〈 A 〉 N ≃ M' ≡〈 A 〉 N'
{- eq-resp-conv M≃M' N≃N' = app-resp-conv (trans-conv (convl M≃M') (convr (convl N≃N'))) -}

postulate R-creates-rep : creates' REP

postulate R-respects-replacement : respects' REP

postulate osr-rep : ∀ {U} {V} {C} {K} {E E' : Subexp U C K} {ρ : Rep U V} →
                  E ⇒ E' → E 〈 ρ 〉 ⇒ E' 〈 ρ 〉
--osr-rep = aposrr REP R-respects-replacement

postulate red-rep : ∀ {U} {V} {C} {K} {E E' : Subexp U C K} {ρ : Rep U V} →
                  E ↠ E' → E 〈 ρ 〉 ↠ E' 〈 ρ 〉
-- red-rep = apredr REP R-respects-replacement

postulate R-creates-replacement : creates' REP

postulate R-respects-sub : respects' SUB

postulate osr-subl : ∀ {U} {V} {C} {K} {E F : Subexp U C K} {σ : Sub U V} → E ⇒ F → E ⟦ σ ⟧ ⇒ F ⟦ σ ⟧
--osr-subl = aposrr SUB R-respects-sub

postulate red-subl : ∀ {U} {V} {C} {K} {E F : Subexp U C K} {σ : Sub U V} → E ↠ F → E ⟦ σ ⟧ ↠ F ⟦ σ ⟧
--red-subl E↠F = respects-red (aposrr SUB R-respects-sub) E↠F

postulate red-subr : ∀ {U} {V} {C} {K} (E : Subexp U C K) {ρ σ : Sub U V} → ρ ↠s σ → E ⟦ ρ ⟧ ↠ E ⟦ σ ⟧

postulate ⊥SN : ∀ {V} → SN {V} ⊥

postulate ⊃SN : ∀ {V} {φ ψ : Term V} → SN φ → SN ψ → SN (φ ⊃ ψ)

postulate SN-βexp : ∀ {V} {φ : Term V} {δ : Proof (V , -Proof)} {ε : Proof V} →
                  SN ε → SN (δ ⟦ x₀:= ε ⟧) → SN (appP (ΛP φ δ) ε) 

postulate univ-red : ∀ {V} {φ φ' ψ ψ' : Term V} {δ} {δ'} {ε} {ε'} → 
                   φ ↠ φ' → ψ ↠ ψ' → δ ↠ δ' → ε ↠ ε' → univ φ ψ δ ε ↠ univ φ' ψ' δ' ε'

postulate ΛP-red : ∀ {V} {φ φ' : Term V} {δ} {δ'} → φ ↠ φ' → δ ↠ δ' → ΛP φ δ ↠ ΛP φ' δ'

postulate ⊃-red : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ↠ φ' → ψ ↠ ψ' → φ ⊃ ψ ↠ φ' ⊃ ψ'
--⊃-red {V} {φ} {φ'} {ψ} {ψ'} φ↠φ' ψ↠ψ' = app-red (∷-red φ↠φ' (∷-redl ψ↠ψ'))

postulate appP-red : ∀ {V} {δ δ' ε ε' : Proof V} → δ ↠ δ' → ε ↠ ε' → appP δ ε ↠ appP δ' ε'
--appP-red δ↠δ' ε↠ε' = app-red (∷-red δ↠δ' (∷-redl ε↠ε'))

postulate ⊃*-red : ∀ {V} {P P' Q Q' : Path V} → P ↠ P' → Q ↠ Q' → (P ⊃* Q) ↠ (P' ⊃* Q')

postulate λλλ-red : ∀ {V A} {P Q : Path (V , -Term , -Term , -Path)} → P ↠ Q → λλλ A P ↠ λλλ A Q

postulate app*-red : ∀ {V} {M M' N N' : Term V} {P P' Q Q'} → M ↠ M' → N ↠ N' → P ↠ P' → Q ↠ Q' →
                   app* M N P Q ↠ app* M' N' P' Q'

postulate ru-redex-half-red : ∀ {V} {φ φ' ψ ψ' : Term V} {δ δ'} →
                            φ ↠ φ' → ψ ↠ ψ' → δ ↠ δ' → ru-redex-half φ ψ δ ↠ ru-redex-half φ' ψ' δ'
--ru-redex-half-red φ↠φ' ψ↠ψ' δ↠δ' = ΛP-red (⊃-red φ↠φ' ψ↠ψ') (ΛP-red (red-rep φ↠φ') (appP-red (red-rep (red-rep δ↠δ')) ref))

ru-redex-red : ∀ {V} {φ φ' ψ ψ' χ χ' : Term V} δ δ' ε ε' →
  φ ↠ φ' → ψ ↠ ψ' → χ ↠ χ' → δ ↠ δ' → ε ↠ ε' →
  ru-redex φ ψ χ δ ε ↠ ru-redex φ' ψ' χ' δ' ε'
ru-redex-red _ _ _ _ φ↠φ' ψ↠ψ' χ↠χ' δ↠δ' ε↠ε' = univ-red (⊃-red φ↠φ' ψ↠ψ') (⊃-red φ↠φ' χ↠χ') (ru-redex-half-red φ↠φ' ψ↠ψ' δ↠δ') (ru-redex-half-red φ↠φ' χ↠χ' ε↠ε')

postulate ur-redex-half-red : ∀ {V} {φ φ' ψ ψ' : Term V} {χ χ' δ δ'} →
                            φ ↠ φ' → ψ ↠ ψ' → χ ↠ χ' → δ ↠ δ' →
                            ur-redex-half φ ψ χ δ ↠ ur-redex-half φ' ψ' χ' δ'
--ur-redex-half-red φ↠φ' ψ↠ψ' χ↠χ' δ↠δ' = ΛP-red (⊃-red φ↠φ' ψ↠ψ') (ΛP-red (red-rep χ↠χ') (appP-red ref (appP-red (red-rep (red-rep δ↠δ')) ref)))

postulate ur-redex-red : ∀ {V} {φ φ' ψ ψ' χ χ' : Term V} δ δ' ε ε' →
                       φ ↠ φ' → ψ ↠ ψ' → χ ↠ χ' → δ ↠ δ' → ε ↠ ε' →
                       ur-redex φ ψ χ δ ε ↠ ur-redex φ' ψ' χ' δ' ε'
--ur-redex-red {φ = φ} {φ'} {ψ} {ψ'} {χ} {χ'} _ _ _ _ φ↠φ' ψ↠ψ' χ↠χ' δ↠δ' ε↠ε' = univ-red (⊃-red φ↠φ' χ↠χ') (⊃-red ψ↠ψ' χ↠χ') (ur-redex-half-red φ↠φ' χ↠χ' ψ↠ψ' ε↠ε') (ur-redex-half-red ψ↠ψ' χ↠χ' φ↠φ' δ↠δ')

postulate uu-redex-half-red : ∀ {V} {φ φ₁ φ' φ'₁ ψ ψ₁ : Term V} {δ δ₁ ε ε₁} →
                            φ ↠ φ₁ → φ' ↠ φ'₁ → ψ ↠ ψ₁ → δ ↠ δ₁ → ε ↠ ε₁ →
                            uu-redex-half φ φ' ψ δ ε ↠ uu-redex-half φ₁ φ'₁ ψ₁ δ₁ ε₁
--uu-redex-half-red φ↠φ₁ φ'↠φ'₁ ψ↠ψ₁ δ↠δ₁ ε↠ε₁ = ΛP-red (⊃-red φ↠φ₁ φ'↠φ'₁) (ΛP-red (red-rep ψ↠ψ₁) (appP-red (red-rep (red-rep δ↠δ₁)) (appP-red ref (appP-red (red-rep (red-rep ε↠ε₁)) ref))))

postulate uu-redex-red : ∀ {V} {φ φ₁ φ' φ'₁ ψ ψ₁ ψ' ψ'₁ : Term V} δ {δ₁} δ' {δ'₁} ε {ε₁} ε' {ε'₁} →
                       φ ↠ φ₁ → φ' ↠ φ'₁ → ψ ↠ ψ₁ → ψ' ↠ ψ'₁ → δ ↠ δ₁ → δ' ↠ δ'₁ → ε ↠ ε₁ → ε' ↠ ε'₁ →
                       uu-redex φ φ' ψ ψ' δ δ' ε ε' ↠ uu-redex φ₁ φ'₁ ψ₁ ψ'₁ δ₁ δ'₁ ε₁ ε'₁
--uu-redex-red {φ = φ} {φ₁} {φ'} {φ'₁} {ψ} {ψ₁} {ψ'} {ψ'₁} _ _ _ _ φ↠φ₁ φ'↠φ'₁ ψ↠ψ₁ ψ'↠ψ'₁ δ↠δ₁ δ'↠δ'₁ ε↠ε₁ ε'↠ε'₁ = 
--  univ-red (⊃-red φ↠φ₁ φ'↠φ'₁) (⊃-red ψ↠ψ₁ ψ'↠ψ'₁) (uu-redex-half-red φ↠φ₁ φ'↠φ'₁ ψ↠ψ₁ δ'↠δ'₁ ε↠ε₁) (uu-redex-half-red ψ↠ψ₁ ψ'↠ψ'₁ φ↠φ₁ ε'↠ε'₁ δ↠δ₁)

{-pre-Confluent βT (appl (redex ()))
pre-Confluent βT (appl (app (appl M⇒M'))) = _ ,p βT ,p red-subl (osr-red M⇒M')
pre-Confluent βT (appl (app (appr ())))
pre-Confluent (βT {M = M}) (appr (appl N⇒N')) = _ ,p βT ,p red-subr M (botsub-red N⇒N')
pre-Confluent βT (appr (appr ()))
pre-Confluent βR (appl (redex ()))
pre-Confluent βR (appl (app (appl _))) = _ ,p βR ,p ref
pre-Confluent βR (appl (app (appr (appl δ⇒δ')))) = _ ,p βR ,p red-subl (osr-red δ⇒δ')
pre-Confluent βR (appl (app (appr (appr ()))))
pre-Confluent (βR {δ = δ}) (appr (appl ε⇒ε')) = _ ,p βR ,p red-subr δ (botsub-red ε⇒ε')
pre-Confluent βR (appr (appr ()))
pre-Confluent plus-ref (appl (redex ()))
pre-Confluent plus-ref (appl (app (appl φ⇒φ'))) = _ ,p plus-ref ,p osr-red (app (appl φ⇒φ'))
pre-Confluent plus-ref (appl (app (appr ())))
pre-Confluent plus-ref (appr ())
pre-Confluent minus-ref (appl (redex ()))
pre-Confluent minus-ref (appl (app (appl φ⇒φ'))) = _ ,p minus-ref ,p osr-red (app (appl φ⇒φ'))
pre-Confluent minus-ref (appl (app (appr ())))
pre-Confluent minus-ref (appr ())
pre-Confluent plus-univ (appl (redex ()))
pre-Confluent plus-univ (appl (app (appl _))) = _ ,p plus-univ ,p ref
pre-Confluent plus-univ (appl (app (appr (appl _)))) = _ ,p plus-univ ,p ref
pre-Confluent plus-univ (appl (app (appr (appr (appl δ⇒δ'))))) = _ ,p plus-univ ,p osr-red δ⇒δ'
pre-Confluent plus-univ (appl (app (appr (appr (appr (appl _)))))) = _ ,p plus-univ ,p ref
pre-Confluent plus-univ (appl (app (appr (appr (appr (appr ()))))))
pre-Confluent plus-univ (appr ())
pre-Confluent minus-univ (appl (redex ()))
pre-Confluent minus-univ (appl (app (appl _))) = _ ,p minus-univ ,p ref
pre-Confluent minus-univ (appl (app (appr (appl _)))) = _ ,p minus-univ ,p ref
pre-Confluent minus-univ (appl (app (appr (appr (appl _))))) = _ ,p minus-univ ,p ref
pre-Confluent minus-univ (appl (app (appr (appr (appr (appl ε⇒ε')))))) = _ ,p minus-univ ,p osr-red ε⇒ε'
pre-Confluent minus-univ (appl (app (appr (appr (appr (appr ()))))))
pre-Confluent minus-univ (appr ())
pre-Confluent ref⊃*univ (appl (redex ()))
pre-Confluent ref⊃*univ (appl (app (appl {E = φ} {E' = φ'} φ⇒φ'))) = 
  let φ⊃ψ↠φ'⊃ψ : ∀ x → (φ ⊃ x) ↠ (φ' ⊃ x)
      φ⊃ψ↠φ'⊃ψ = λ _ → osr-red (app (appl φ⇒φ')) in
  _ ,p ref⊃*univ ,p univ-red (φ⊃ψ↠φ'⊃ψ _) (φ⊃ψ↠φ'⊃ψ _) (ΛP-red (φ⊃ψ↠φ'⊃ψ _) (osr-red (app (appl (aposrr replacement R-respects-replacement φ⇒φ'))))) 
  (ΛP-red (φ⊃ψ↠φ'⊃ψ _) (osr-red (app (appl (aposrr replacement R-respects-replacement φ⇒φ')))))
pre-Confluent ref⊃*univ (appl (app (appr ())))
pre-Confluent ref⊃*univ (appr (appl (redex ())))
pre-Confluent ref⊃*univ (appr (appl (app (appl ψ⇒ψ')))) = _ ,p ref⊃*univ ,p (univ-red (osr-red (app (appr (appl ψ⇒ψ')))) ref 
  (ΛP-red (osr-red (app (appr (appl ψ⇒ψ')))) ref) ref)
pre-Confluent ref⊃*univ (appr (appl (app (appr (appl χ⇒χ'))))) = _ ,p (ref⊃*univ ,p (univ-red ref (osr-red (app (appr (appl χ⇒χ')))) 
  ref (osr-red (app (appl (app (appr (appl χ⇒χ'))))))))
pre-Confluent ref⊃*univ (appr (appl (app (appr (appr (appl δ⇒δ')))))) = _ ,p ref⊃*univ ,p osr-red (app (appr (appr (appl (app (appr (appl (app (appr (appl 
  (app (appl (aposrr replacement R-respects-replacement (aposrr replacement R-respects-replacement δ⇒δ'))))))))))))))
pre-Confluent ref⊃*univ (appr (appl (app (appr (appr (appr (appl ε⇒ε'))))))) = _ ,p ref⊃*univ ,p osr-red (app (appr (appr (appr (appl (app (appr (appl (app (appr 
  (appl (app (appl (aposrr replacement R-respects-replacement (aposrr replacement R-respects-replacement ε⇒ε')))))))))))))))
pre-Confluent ref⊃*univ (appr (appl (app (appr (appr (appr (appr ())))))))
pre-Confluent ref⊃*univ (appr (appr ()))
pre-Confluent univ⊃*ref E⇒E' = {!!}
pre-Confluent univ⊃*univ E⇒E' = {!!}
pre-Confluent ref⊃*ref E⇒E' = {!!}
pre-Confluent refref E⇒E' = {!!}
pre-Confluent βE E⇒E' = {!!}
pre-Confluent reflamvar E⇒E' = {!!}
pre-Confluent reflam⊃* E⇒E' = {!!}
pre-Confluent reflamuniv E⇒E' = {!!}
pre-Confluent reflamλλλ E⇒E' = {!!} -}

\end{code}
}

\paragraph{Note}
Contraction is a relation between closed expressions only: if $s \rhd t$ then $s$ and $t$ are closed.  This is not true for $\rightarrow$, $\twoheadrightarrow$ or $\simeq$, however.  For example, we have $\reff{\bot}^+ x \rightarrow (\lambda p:\bot.p)x$.

\begin{lm}[Reduction respects substitution]
$ $
\begin{enumerate}
\item
If $t \rightarrow t'$ then $t[x:=s] \rightarrow t'[x:=s]$.
\item
If $t \rightarrow t'$ then $s[x:=t] \twoheadrightarrow s[x:=t']$.
\item
If $P \rightarrow P'$ then $M \{ x:= P : N \sim N' \} \twoheadrightarrow M \{ x:=P' : N \sim N' \}$.
\begin{code}
_↠p_ : ∀ {U V} → PathSub U V → PathSub U V → Set
τ ↠p τ' = ∀ x → τ x ↠ τ' x

postulate liftPathSub-red : ∀ {U V} {τ τ' : PathSub U V} → τ ↠p τ' → liftPathSub τ ↠p liftPathSub τ'

red-pathsub : ∀ {U V} (M : Term U) {ρ σ : Sub U V} {τ τ' : PathSub U V} →
            τ ↠p τ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ↠ M ⟦⟦ τ' ∶ ρ ∼ σ ⟧⟧
red-pathsub (var x) τ↠pτ' = τ↠pτ' x
red-pathsub (app -bot []) τ↠pτ' = ref
red-pathsub (app -imp (φ ∷ ψ ∷ [])) τ↠pτ' = ⊃*-red (red-pathsub φ τ↠pτ') (red-pathsub ψ τ↠pτ')
red-pathsub (app (-lamTerm A) (M ∷ [])) τ↠pτ' = λλλ-red (red-pathsub M (liftPathSub-red τ↠pτ'))
red-pathsub (app -appTerm (M ∷ N ∷ [])) τ↠pτ' = app*-red ref ref (red-pathsub M τ↠pτ') (red-pathsub N τ↠pτ')

postulate red-pathsub-endl : ∀ {U V} (M : Term U) {ρ ρ' σ : Sub U V} {τ : PathSub U V} →
                      ρ ↠s ρ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ↠ M ⟦⟦ τ ∶ ρ' ∼ σ ⟧⟧

postulate red-pathsub-endr : ∀ {U V} (M : Term U) {ρ σ σ' : Sub U V} {τ : PathSub U V} →
                      σ ↠s σ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ↠ M ⟦⟦ τ ∶ ρ ∼ σ' ⟧⟧
\end{code}
\end{enumerate}
\end{lm}

\begin{proof}
A straightforward induction in each case.
\end{proof}

\paragraph{Note}
It is not true in general that path substitution respects reduction; that is, that if $M \rightarrow M'$ then $M \{ x:=P : N \sim N' \} \twoheadrightarrow M' \{ x:=P : N \sim N' \}$.  For example, we have
$(\lambda x:\Omega.x)(\bot \supset \bot) \rightarrow \bot \supset \bot$,
but
\begin{align*}
(\bot \supset \bot) \{ \} & \equiv \reff{\bot} \supset^* \reff{\bot} \\
((\lambda x:\Omega.x)(\bot \supset \bot)) \{ \} & \equiv (\triplelambda e:x =_\Omega x'.e)(\reff{\bot} \supset^* \reff{\bot})
\end{align*}
The second of these paths does \emph{not} reduce to the first, because $\reff{\bot} \supset^* \reff{\bot}$ is not a normal form.

\AgdaHide{
\begin{code}
postulate SNE : ∀ {V} {C} {K} (P : Subexp V C K → Set) →
              (∀ {M : Subexp V C K} → SN M → (∀ N → M ↠⁺ N → P N) → P M) →
              ∀ {M : Subexp V C K} → SN M → P M

private postulate var-red' : ∀ {V} {K} {x : Var V K} {M} {N} → M ↠ N → M ≡ var x → N ≡ var x
{-var-red' (inc (redex _)) ()
var-red' (inc (app _)) ()
var-red' ref M≡x = M≡x
var-red' (trans M↠N N↠P) M≡x = var-red' N↠P (var-red' M↠N M≡x) -}

postulate var-red : ∀ {V} {K} {x : Var V K} {M} → var x ↠ M → M ≡ var x
--var-red x↠M = var-red' x↠M refl

private postulate bot-red' : ∀ {V} {φ ψ : Term V} → φ ↠ ψ → φ ≡ ⊥ → ψ ≡ ⊥
{- bot-red' (inc (redex βT)) ()
bot-red' (inc (app {c = -bot} {F = []} x)) _ = refl
bot-red' (inc (app {c = -imp} _)) ()
bot-red' (inc (app {c = -appTerm} _)) ()
bot-red' (inc (app {c = -lamTerm _} _)) ()
bot-red' ref φ≡⊥ = φ≡⊥
bot-red' (trans φ↠ψ ψ↠χ) φ≡⊥ = bot-red' ψ↠χ (bot-red' φ↠ψ φ≡⊥) -}

postulate bot-red : ∀ {V} {φ : Term V} → ⊥ ↠ φ → φ ≡ ⊥
--bot-red ⊥↠φ = bot-red' ⊥↠φ refl

postulate imp-red' : ∀ {V} {φ ψ χ θ : Term V} → φ ↠ ψ → φ ≡ χ ⊃ θ →
                   Σ[ χ' ∈ Term V ] Σ[ θ' ∈ Term V ] χ ↠ χ' × θ ↠ θ' × ψ ≡ χ' ⊃ θ'
{-imp-red' (inc (redex βT)) ()
imp-red' (inc (app {c = -bot} _)) ()
imp-red' {θ = θ} (inc (app {c = -imp} (appl {E' = χ'} {F = _ ∷ []} χ⇒χ'))) φ≡χ⊃θ = 
  χ' ,p θ ,p subst (λ x → x ↠ χ') (imp-injl φ≡χ⊃θ) (inc χ⇒χ') ,p 
  ref ,p (cong (λ x → χ' ⊃ x) (imp-injr φ≡χ⊃θ))
imp-red' {χ = χ} (inc (app {c = -imp} (appr (appl {E' = θ'} {F = []} θ⇒θ')))) φ≡χ⊃θ = 
  χ ,p θ' ,p ref ,p (subst (λ x → x ↠ θ') (imp-injr φ≡χ⊃θ) (inc θ⇒θ')) ,p 
  cong (λ x → x ⊃ θ') (imp-injl φ≡χ⊃θ)
imp-red' (inc (app {c = -imp} (appr (appr ())))) _
imp-red' (inc (app {c = -appTerm} _)) ()
imp-red' (inc (app {c = -lamTerm _} _)) ()
imp-red' {χ = χ} {θ} ref φ≡χ⊃θ = χ ,p θ ,p ref ,p ref ,p φ≡χ⊃θ
imp-red' (trans φ↠ψ ψ↠ψ') φ≡χ⊃θ = 
  let (χ' ,p θ' ,p χ↠χ' ,p θ↠θ' ,p ψ≡χ'⊃θ') = imp-red' φ↠ψ φ≡χ⊃θ in 
  let (χ'' ,p θ'' ,p χ'↠χ'' ,p θ'↠θ'' ,p ψ'≡χ''⊃θ'') = imp-red' ψ↠ψ' ψ≡χ'⊃θ' in 
  χ'' ,p θ'' ,p RTClose.trans χ↠χ' χ'↠χ'' ,p RTClose.trans θ↠θ' θ'↠θ'' ,p ψ'≡χ''⊃θ''-}

postulate imp-red : ∀ {V} {χ θ ψ : Term V} → χ ⊃ θ ↠ ψ →
                  Σ[ χ' ∈ Term V ] Σ[ θ' ∈ Term V ] χ ↠ χ' × θ ↠ θ' × ψ ≡ χ' ⊃ θ'
--imp-red χ⊃θ↠ψ = imp-red' χ⊃θ↠ψ refl

postulate conv-rep : ∀ {U} {V} {C} {K} {ρ : Rep U V} {M N : Subexp U C K} → M ≃ N → M 〈 ρ 〉 ≃ N 〈 ρ 〉

postulate conv-sub : ∀ {U} {V} {C} {K} {σ : Sub U V} {M N : Subexp U C K} → M ≃ N → M ⟦ σ ⟧ ≃ N ⟦ σ ⟧

postulate appT-convl : ∀ {V} {M M' N : Term V} → M ≃ M' → appT M N ≃ appT M' N

data redVT {V} : ∀ {n} → snocVec (Term V) n → snocVec (Term V) n → Set where
  redleft : ∀ {n} {MM MM' : snocVec (Term V) n} {N} → redVT MM MM' → redVT (MM snoc N) (MM' snoc N)
  redright : ∀ {n} {MM : snocVec (Term V) n} {N N'} → N ⇒ N' → redVT (MM snoc N) (MM snoc N')

data redVP {V} : ∀ {n} → snocVec (Proof V) n → snocVec (Proof V) n → Set where
  redleft : ∀ {n} {εε εε' : snocVec _ n} {δ} → redVP εε εε' → redVP (εε snoc δ) (εε' snoc δ)
  redright : ∀ {n} {εε : snocVec _ n} {δ} {δ'} → δ ⇒ δ' → redVP (εε snoc δ) (εε snoc δ')

data redVPa {V} : ∀ {n} → snocVec (Path V) n → snocVec (Path V) n → Set where
  redleft : ∀ {n} {PP PP' : snocVec (Path V) n} {Q} → redVPa PP PP' → redVPa (PP snoc Q) (PP' snoc Q)
  redright : ∀ {n} {PP : snocVec (Path V) n} {Q Q'} → Q ⇒ Q' → redVPa (PP snoc Q) (PP snoc Q')

postulate APPP-redl : ∀ {V n δ δ'} {εε : snocVec (Proof V) n} → δ ⇒ δ' → APPP δ εε ⇒ APPP δ' εε
{-APPP-redl {εε = []} δ⇒δ' = δ⇒δ'
APPP-redl {εε = εε snoc _} δ⇒δ' = app (appl (APPP-redl {εε = εε} δ⇒δ'))-}

postulate APP*-red₁ : ∀ {V n} {MM MM' NN : snocVec (Term V) n} {P PP} → redVT MM MM' → APP* MM NN P PP ⇒ APP* MM' NN P PP
--APP*-red₁ {NN = _ snoc _} {PP = _ snoc _} (redleft MM⇒MM') = app (appr (appr (appl (APP*-red₁ MM⇒MM'))))
--APP*-red₁ {NN = _ snoc _} {PP = _ snoc _} (redright M⇒M') = app (appl M⇒M')

postulate APP*-red₂ : ∀ {V n} MM {NN NN' : snocVec (Term V) n} {P PP} → redVT NN NN' → APP* MM NN P PP ⇒ APP* MM NN' P PP
--APP*-red₂ (MM snoc _) {_ snoc _} {_ snoc _} {PP = _ snoc _} (redleft NN⇒NN') = app (appr (appr (appl (APP*-red₂ MM NN⇒NN'))))
--APP*-red₂ (_ snoc _) {PP = _ snoc _} (redright N⇒N') = app (appr (appl N⇒N'))

postulate APP*-red₃ : ∀ {V n} MM {NN : snocVec (Term V) n} {P P' PP} → P ⇒ P' → APP* MM NN P PP ⇒ APP* MM NN P' PP
--APP*-red₃ [] {[]} {PP = []} P⇒P' = P⇒P'
--APP*-red₃ (MM snoc M) {NN snoc N} {PP = PP snoc P} P⇒P' = app (appr (appr (appl (APP*-red₃ MM P⇒P'))))
\end{code}
