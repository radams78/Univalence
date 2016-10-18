\AgdaHide{
\begin{code}
module PHOPL.Red where
open import Data.Unit
open import Data.Vec
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import Prelims
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
data R : Reduction where
  βT : ∀ {V} {A} {M} {N} → R {V} -appTerm (ΛT A M ∷ N ∷ []) (M ⟦ x₀:= N ⟧)
  βR : ∀ {V} {φ} {δ} {ε} → R {V} -appProof (ΛP φ δ ∷ ε ∷ []) (δ ⟦ x₀:= ε ⟧)
  plus-ref : ∀ {V} {φ} → R {V} -plus (reff φ ∷ []) (ΛP φ (var x₀))
  minus-ref : ∀ {V} {φ} → R {V} -minus (reff φ ∷ []) (ΛP φ (var x₀))
  plus-univ : ∀ {V} {φ} {ψ} {δ} {ε} → R {V} -plus (univ φ ψ δ ε ∷ []) δ 
  minus-univ : ∀ {V} {φ} {ψ} {δ} {ε} → R {V} -minus (univ φ ψ δ ε ∷ []) ε
  ref⊃*univ : ∀ {V} {φ} {ψ} {χ} {δ} {ε} → R {V} -imp* (reff φ ∷ univ ψ χ δ ε ∷ []) (univ (φ ⊃ ψ) (φ ⊃ χ) (ΛP (φ ⊃ ψ) (ΛP (φ ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (var x₀))))) (ΛP (φ ⊃ χ) (ΛP (φ ⇑) (appP (ε ⇑ ⇑) (appP (var x₁) (var x₀))))))
  univ⊃*ref : ∀ {V} {φ} {ψ} {χ} {δ} {ε} → R {V} -imp* (univ φ ψ δ ε ∷ reff χ ∷ []) (univ (φ ⊃ χ) (ψ ⊃ χ) (ΛP (φ ⊃ χ) (ΛP (ψ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀))))) (ΛP (ψ ⊃ χ) (ΛP (φ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀))))))
  univ⊃*univ : ∀ {V} {φ} {φ'} {ψ} {ψ'} {δ} {δ'} {ε} {ε'} →
    R {V} -imp* (univ φ ψ δ ε ∷ univ φ' ψ' δ' ε' ∷ [])
    (univ (φ ⊃ φ') (ψ ⊃ ψ') (ΛP (φ ⊃ φ') (ΛP (ψ ⇑) (appP (δ' ⇑ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀))))))
      (ΛP (ψ ⊃ ψ') (ΛP (φ ⇑) (appP (ε' ⇑ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀)))))))
  ref⊃*ref : ∀ {V} {φ} {ψ} → R {V} -imp* (reff φ ∷ reff ψ ∷ []) (reff (φ ⊃ ψ))
  refref : ∀ {V} {M} {N} → R {V} -app* (N ∷ N ∷ reff M ∷ reff N ∷ []) (reff (appT M N))
  βE : ∀ {V} {M} {N} {A} {P} {Q} → R {V} -app* (M ∷ N ∷ λλλ A P ∷ Q ∷ []) 
    (P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧)
  reflamvar : ∀ {V} {N} {N'} {A} {M} {e} → R {V} -app* (N ∷ N' ∷ reff (ΛT A M) ∷ var e ∷ []) (M ⟦⟦ x₀::= (var e) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
  reflam⊃* : ∀ {V} {N} {N'} {A} {M} {P} {Q} → R {V} -app* (N ∷ N' ∷ reff (ΛT A M) ∷ (P ⊃* Q) ∷ []) (M ⟦⟦ x₀::= (P ⊃* Q) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
  reflamuniv : ∀ {V} {N} {N'} {A} {M} {φ} {ψ} {δ} {ε} → R {V} -app* (N ∷ N' ∷ reff (ΛT A M) ∷ univ φ ψ δ ε ∷ []) (M ⟦⟦ x₀::= (univ φ ψ δ ε) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
  reflamλλλ : ∀ {V} {N} {N'} {A} {M} {B} {P} → R {V} -app* (N ∷ N' ∷ reff (ΛT A M) ∷ λλλ B P ∷ []) (M ⟦⟦ x₀::= (λλλ B P) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
\end{code}

Let $\rightarrow^?$ be the reflexive closure of $\rightarrow$;
let $\twoheadrightarrow^+$ be the transitive closure;
let \emph{reduction} $\twoheadrightarrow$ be the reflexive, transitive closure; and \emph{conversion} $\simeq$ the equivalence relation generated by $\rightarrow$.
\end{definition}

\AgdaHide{
\begin{code}
open import Reduction PHOPL R public 

eq-resp-conv : ∀ {V} {M M' N N' : Term V} {A : Type} →
  M ≃ M' → N ≃ N' → M ≡〈 A 〉 N ≃ M' ≡〈 A 〉 N'
eq-resp-conv M≃M' N≃N' = app-resp-conv (trans-conv (convl M≃M') (convr (convl N≃N')))

postulate R-creates-rep : creates' REP

postulate R-respects-replacement : respects' REP

postulate R-creates-replacement : creates' REP

postulate R-respects-sub : respects' SUB

osr-subl : ∀ {U} {V} {C} {K} {E F : Subexpression U C K} {σ : Sub U V} → E ⇒ F → E ⟦ σ ⟧ ⇒ F ⟦ σ ⟧
osr-subl = respects-osr SUB R-respects-sub

red-subl : ∀ {U} {V} {C} {K} {E F : Subexpression U C K} {σ : Sub U V} → E ↠ F → E ⟦ σ ⟧ ↠ F ⟦ σ ⟧
red-subl E↠F = respects-red (respects-osr SUB R-respects-sub) E↠F

postulate red-subr : ∀ {U} {V} {C} {K} (E : Subexpression U C K) {ρ σ : Sub U V} → _↠s_ SUB ρ σ → E ⟦ ρ ⟧ ↠ E ⟦ σ ⟧

postulate ⊥SN : ∀ {V} → SN {V} ⊥

postulate ⊃SN : ∀ {V} {φ ψ : Term V} → SN φ → SN ψ → SN (φ ⊃ ψ)

postulate SN-βexp : ∀ {V} {φ : Term V} {δ : Proof (V , -Proof)} {ε : Proof V} →
                  SN ε → SN (δ ⟦ x₀:= ε ⟧) → SN (appP (ΛP φ δ) ε) 

postulate univ-red : ∀ {V} {φ φ' ψ ψ' : Term V} {δ} {δ'} {ε} {ε'} → 
                   φ ↠ φ' → ψ ↠ ψ' → δ ↠ δ' → ε ↠ ε' → univ φ ψ δ ε ↠ univ φ' ψ' δ' ε'

postulate ΛP-red : ∀ {V} {φ φ' : Term V} {δ} {δ'} → φ ↠ φ' → δ ↠ δ' → ΛP φ δ ↠ ΛP φ' δ'


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
  _ ,p ref⊃*univ ,p univ-red (φ⊃ψ↠φ'⊃ψ _) (φ⊃ψ↠φ'⊃ψ _) (ΛP-red (φ⊃ψ↠φ'⊃ψ _) (osr-red (app (appl (respects-osr replacement R-respects-replacement φ⇒φ'))))) 
  (ΛP-red (φ⊃ψ↠φ'⊃ψ _) (osr-red (app (appl (respects-osr replacement R-respects-replacement φ⇒φ')))))
pre-Confluent ref⊃*univ (appl (app (appr ())))
pre-Confluent ref⊃*univ (appr (appl (redex ())))
pre-Confluent ref⊃*univ (appr (appl (app (appl ψ⇒ψ')))) = _ ,p ref⊃*univ ,p (univ-red (osr-red (app (appr (appl ψ⇒ψ')))) ref 
  (ΛP-red (osr-red (app (appr (appl ψ⇒ψ')))) ref) ref)
pre-Confluent ref⊃*univ (appr (appl (app (appr (appl χ⇒χ'))))) = _ ,p (ref⊃*univ ,p (univ-red ref (osr-red (app (appr (appl χ⇒χ')))) 
  ref (osr-red (app (appl (app (appr (appl χ⇒χ'))))))))
pre-Confluent ref⊃*univ (appr (appl (app (appr (appr (appl δ⇒δ')))))) = _ ,p ref⊃*univ ,p osr-red (app (appr (appr (appl (app (appr (appl (app (appr (appl 
  (app (appl (respects-osr replacement R-respects-replacement (respects-osr replacement R-respects-replacement δ⇒δ'))))))))))))))
pre-Confluent ref⊃*univ (appr (appl (app (appr (appr (appr (appl ε⇒ε'))))))) = _ ,p ref⊃*univ ,p osr-red (app (appr (appr (appr (appl (app (appr (appl (app (appr 
  (appl (app (appl (respects-osr replacement R-respects-replacement (respects-osr replacement R-respects-replacement ε⇒ε')))))))))))))))
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
postulate SNE : ∀ {V} {C} {K} (P : Subexpression V C K → Set) →
              (∀ {M : Subexpression V C K} → SN M → (∀ N → M ↠⁺ N → P N) → P M) →
              ∀ {M : Subexpression V C K} → SN M → P M

private var-red' : ∀ {V} {K} {x : Var V K} {M} {N} → M ↠ N → M ≡ var x → N ≡ var x
var-red' (osr-red (redex _)) ()
var-red' (osr-red (app _)) ()
var-red' ref M≡x = M≡x
var-red' (trans-red M↠N N↠P) M≡x = var-red' N↠P (var-red' M↠N M≡x)

var-red : ∀ {V} {K} {x : Var V K} {M} → var x ↠ M → M ≡ var x
var-red x↠M = var-red' x↠M refl

private bot-red' : ∀ {V} {φ ψ : Term V} → φ ↠ ψ → φ ≡ ⊥ → ψ ≡ ⊥
bot-red' (osr-red (redex βT)) ()
bot-red' (osr-red (app {c = -bot} {F = []} x)) _ = refl
bot-red' (osr-red (app {c = -imp} _)) ()
bot-red' (osr-red (app {c = -appTerm} _)) ()
bot-red' (osr-red (app {c = -lamTerm _} _)) ()
bot-red' ref φ≡⊥ = φ≡⊥
bot-red' (trans-red φ↠ψ ψ↠χ) φ≡⊥ = bot-red' ψ↠χ (bot-red' φ↠ψ φ≡⊥)

bot-red : ∀ {V} {φ : Term V} → ⊥ ↠ φ → φ ≡ ⊥
bot-red ⊥↠φ = bot-red' ⊥↠φ refl

imp-red' : ∀ {V} {φ ψ χ θ : Term V} → φ ↠ ψ → φ ≡ χ ⊃ θ →
  Σ[ χ' ∈ Term V ] Σ[ θ' ∈ Term V ] χ ↠ χ' × θ ↠ θ' × ψ ≡ χ' ⊃ θ'
imp-red' (osr-red (redex βT)) ()
imp-red' (osr-red (app {c = -bot} _)) ()
imp-red' {θ = θ} (osr-red (app {c = -imp} (appl {E' = χ'} {F = _ ∷ []} χ⇒χ'))) φ≡χ⊃θ = 
  χ' ,p θ ,p subst (λ x → x ↠ χ') (imp-injl φ≡χ⊃θ) (osr-red χ⇒χ') ,p 
  ref ,p (cong (λ x → χ' ⊃ x) (imp-injr φ≡χ⊃θ))
imp-red' {χ = χ} (osr-red (app {c = -imp} (appr (appl {E' = θ'} {F = []} θ⇒θ')))) φ≡χ⊃θ = 
  χ ,p θ' ,p ref ,p (subst (λ x → x ↠ θ') (imp-injr φ≡χ⊃θ) (osr-red θ⇒θ')) ,p 
  cong (λ x → x ⊃ θ') (imp-injl φ≡χ⊃θ)
imp-red' (osr-red (app {c = -imp} (appr (appr ())))) _
imp-red' (osr-red (app {c = -appTerm} _)) ()
imp-red' (osr-red (app {c = -lamTerm _} _)) ()
imp-red' {χ = χ} {θ} ref φ≡χ⊃θ = χ ,p θ ,p ref ,p ref ,p φ≡χ⊃θ
imp-red' (trans-red φ↠ψ ψ↠ψ') φ≡χ⊃θ = 
  let (χ' ,p θ' ,p χ↠χ' ,p θ↠θ' ,p ψ≡χ'⊃θ') = imp-red' φ↠ψ φ≡χ⊃θ in 
  let (χ'' ,p θ'' ,p χ'↠χ'' ,p θ'↠θ'' ,p ψ'≡χ''⊃θ'') = imp-red' ψ↠ψ' ψ≡χ'⊃θ' in 
  χ'' ,p θ'' ,p trans-red χ↠χ' χ'↠χ'' ,p trans-red θ↠θ' θ'↠θ'' ,p ψ'≡χ''⊃θ''

imp-red : ∀ {V} {χ θ ψ : Term V} → χ ⊃ θ ↠ ψ →
  Σ[ χ' ∈ Term V ] Σ[ θ' ∈ Term V ] χ ↠ χ' × θ ↠ θ' × ψ ≡ χ' ⊃ θ'
imp-red χ⊃θ↠ψ = imp-red' χ⊃θ↠ψ refl

postulate red-rep : ∀ {U} {V} {C} {K} {ρ : Rep U V} {M N : Subexpression U C K} → M ↠ N → M 〈 ρ 〉 ↠ N 〈 ρ 〉

postulate conv-rep : ∀ {U} {V} {C} {K} {ρ : Rep U V} {M N : Subexpression U C K} → M ≃ N → M 〈 ρ 〉 ≃ N 〈 ρ 〉

postulate conv-sub : ∀ {U} {V} {C} {K} {σ : Sub U V} {M N : Subexpression U C K} → M ≃ N → M ⟦ σ ⟧ ≃ N ⟦ σ ⟧

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

APPP-redl : ∀ {V n δ δ'} {εε : snocVec (Proof V) n} → δ ⇒ δ' → APPP δ εε ⇒ APPP δ' εε
APPP-redl {εε = []} δ⇒δ' = δ⇒δ'
APPP-redl {εε = εε snoc _} δ⇒δ' = app (appl (APPP-redl {εε = εε} δ⇒δ'))

APP*-red₁ : ∀ {V n} {MM MM' NN : snocVec (Term V) n} {P PP} → redVT MM MM' → APP* MM NN P PP ⇒ APP* MM' NN P PP
APP*-red₁ {NN = _ snoc _} {PP = _ snoc _} (redleft MM⇒MM') = app (appr (appr (appl (APP*-red₁ MM⇒MM'))))
APP*-red₁ {NN = _ snoc _} {PP = _ snoc _} (redright M⇒M') = app (appl M⇒M')

APP*-red₂ : ∀ {V n} MM {NN NN' : snocVec (Term V) n} {P PP} → redVT NN NN' → APP* MM NN P PP ⇒ APP* MM NN' P PP
APP*-red₂ (MM snoc _) {_ snoc _} {_ snoc _} {PP = _ snoc _} (redleft NN⇒NN') = app (appr (appr (appl (APP*-red₂ MM NN⇒NN'))))
APP*-red₂ (_ snoc _) {PP = _ snoc _} (redright N⇒N') = app (appr (appl N⇒N'))

APP*-red₃ : ∀ {V n} MM {NN : snocVec (Term V) n} {P P' PP} → P ⇒ P' → APP* MM NN P PP ⇒ APP* MM NN P' PP
APP*-red₃ [] {[]} {PP = []} P⇒P' = P⇒P'
APP*-red₃ (MM snoc M) {NN snoc N} {PP = PP snoc P} P⇒P' = app (appr (appr (appl (APP*-red₃ MM P⇒P'))))
\end{code}
