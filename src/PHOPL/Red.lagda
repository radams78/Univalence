\AgdaHide{
\begin{code}
module PHOPL.Red where
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import Prelims
open import PHOPL.Grammar
open import PHOPL.PathSub
\end{code}
}

\subsection{The Reduction Relation}

We make the following definitions simultaneously:
\begin{enumerate}
\item
Let \emph{contraction} $\rhd$ be the relation consisting of the following pairs, where $M$, $N$, $N'$, $N_1$, $N_2$, $P$, $Q$, $\phi$, $\phi'$, $\psi$, $\psi'$, $\chi$, $\delta$, $\delta'$, $\epsilon$, $\epsilon'$ are closed expressions in normal form:
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
\item
{One-step reduction} $\rightarrow$ is the congruence generated by $\rhd$.  That is, the expression $E$ \emph{reduces in one step} to the expression $F$, $E \rightarrow F$, iff $F$ is formed from $E$ by replacing a subterm $G$ with a subterm $H$, where $G \rhd H$.
\item
An expression $E$ is in \emph{normal form} iff there is no expression $F$ such that $E \rightarrow F$.
\end{enumerate}

\todo{Conjecture: We can remove the restriction on $P$ in the last clause if we add reduction rules:
$\triplelambda e:y=_Ay'.M\{x:=e:y\sim y'\} \rhd \reff{\lambda x:A.M}$}

\begin{code}
data R : Reduction where
  βT : ∀ {V} {A} {M} {N} → R {V} -appTerm (ΛT A M ,, N ,, out) (M ⟦ x₀:= N ⟧)
  βR : ∀ {V} {φ} {δ} {ε} → R {V} -appProof (ΛP φ δ ,, ε ,, out) (δ ⟦ x₀:= ε ⟧)
  plus-ref : ∀ {V} {φ} → R {V} -plus (reff φ ,, out) (ΛP φ (var x₀))
  minus-ref : ∀ {V} {φ} → R {V} -minus (reff φ ,, out) (ΛP φ (var x₀))
  plus-univ : ∀ {V} {φ} {ψ} {δ} {ε} → R {V} -plus (univ φ ψ δ ε ,, out) δ 
  minus-univ : ∀ {V} {φ} {ψ} {δ} {ε} → R {V} -minus (univ φ ψ δ ε ,, out) ε
  ref⊃*univ : ∀ {V} {φ} {ψ} {χ} {δ} {ε} → R {V} -imp* (reff φ ,, univ ψ χ δ ε ,, out) (univ (φ ⊃ ψ) (φ ⊃ χ) (ΛP (φ ⊃ ψ) (ΛP (φ ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (var x₀))))) (ΛP (φ ⊃ χ) (ΛP (φ ⇑) (appP (ε ⇑ ⇑) (appP (var x₁) (var x₀))))))
  univ⊃*ref : ∀ {V} {φ} {ψ} {χ} {δ} {ε} → R {V} -imp* (univ φ ψ δ ε ,, reff χ ,, out) (univ (φ ⊃ χ) (ψ ⊃ χ) (ΛP (φ ⊃ χ) (ΛP (ψ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀))))) (ΛP (ψ ⊃ χ) (ΛP (φ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀))))))
  univ⊃*univ : ∀ {V} {φ} {φ'} {ψ} {ψ'} {δ} {δ'} {ε} {ε'} →
    R {V} -imp* (univ φ ψ δ ε ,, univ φ' ψ' δ' ε' ,, out)
    (univ (φ ⊃ φ') (ψ ⊃ ψ') (ΛP (φ ⊃ φ') (ΛP (ψ ⇑) (appP (δ' ⇑ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀))))))
      (ΛP (ψ ⊃ ψ') (ΛP (φ ⇑) (appP (ε' ⇑ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀)))))))
  ref⊃*ref : ∀ {V} {φ} {ψ} → R {V} -imp* (reff φ ,, reff ψ ,, out) (reff (φ ⊃ ψ))
  refref : ∀ {V} {M} {N} → R {V} -app* (N ,, N ,, reff M ,, reff N ,, out) (reff (appT M N))
  βE : ∀ {V} {M} {N} {A} {P} {Q} → R {V} -app* (M ,, N ,, λλλ A P ,, Q ,, out) 
    (P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧)
  reflamvar : ∀ {V} {N} {N'} {A} {M} {e} → R {V} -app* (N ,, N' ,, reff (ΛT A M) ,, var e ,, out) (M ⟦⟦ x₀::= (var e) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
  reflam⊃* : ∀ {V} {N} {N'} {A} {M} {P} {Q} → R {V} -app* (N ,, N' ,, reff (ΛT A M) ,, (P ⊃* Q) ,, out) (M ⟦⟦ x₀::= (P ⊃* Q) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
  reflamuniv : ∀ {V} {N} {N'} {A} {M} {φ} {ψ} {δ} {ε} → R {V} -app* (N ,, N' ,, reff (ΛT A M) ,, univ φ ψ δ ε ,, out) (M ⟦⟦ x₀::= (univ φ ψ δ ε) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
  reflamλλλ : ∀ {V} {N} {N'} {A} {M} {B} {P} → R {V} -app* (N ,, N' ,, reff (ΛT A M) ,, λλλ B P ,, out) (M ⟦⟦ x₀::= (λλλ B P) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
\end{code}

Let \emph{reduction} $\twoheadrightarrow$ be the reflexive, transitive closure of $\rightarrow$, and \emph{conversion} $\simeq$ the equivalence relation generated by $\rightarrow$.

\AgdaHide{
\begin{code}
open import Reduction PHOPL R public 

postulate eq-resp-conv : ∀ {V} {M M' N N' : Term V} {A : Type} →
                       M ≃ M' → N ≃ N' → M ≡〈 A 〉 N ≃ M' ≡〈 A 〉 N'

postulate R-creates-rep : creates' replacement

postulate R-respects-replacement : respects' replacement

postulate R-creates-replacement : creates' replacement

postulate R-respects-sub : respects' SUB

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

postulate pre-Confluent : ∀ {V} {K} {C} {c : Constructor C} {E E' : Body V C} {F} →
                        R c E F → E ⇒ E' → Σ[ F' ∈ Expression V K ] R c E' F' × F ↠ F'
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

Critical-Pairs : ∀ {V} {K} {C} {c : Constructor C} {E : Body V C} {F} {G} → R c E F → R c E G → Σ[ H ∈ Expression V K ] F ↠ H × G ↠ H
Critical-Pairs βT βT = _ ,p ref ,p ref
Critical-Pairs βR βR = _ ,p ref ,p ref
Critical-Pairs plus-ref plus-ref = _ ,p ref ,p ref
Critical-Pairs minus-ref minus-ref = _ ,p ref ,p ref
Critical-Pairs plus-univ plus-univ = _ ,p ref ,p ref
Critical-Pairs minus-univ minus-univ = _ ,p ref ,p ref
Critical-Pairs ref⊃*univ ref⊃*univ = _ ,p ref ,p ref
Critical-Pairs univ⊃*ref univ⊃*ref = _ ,p ref ,p ref
Critical-Pairs univ⊃*univ univ⊃*univ = _ ,p ref ,p ref
Critical-Pairs ref⊃*ref ref⊃*ref = _ ,p ref ,p ref
Critical-Pairs refref refref = _ ,p ref ,p ref
Critical-Pairs βE βE = _ ,p ref ,p ref
Critical-Pairs reflamvar reflamvar = _ ,p ref ,p ref
Critical-Pairs reflam⊃* reflam⊃* = _ ,p ref ,p ref
Critical-Pairs reflamuniv reflamuniv = _ ,p ref ,p ref
Critical-Pairs reflamλλλ reflamλλλ = _ ,p ref ,p ref
\end{code}
}

\paragraph{Note}
\begin{enumerate}
\item
Contraction is a relation between closed terms only: if $E \rhd F$ then $E$ and $F$ are closed.  This is not true for $\rightarrow$, $\twoheadrightarrow$ or $\simeq$, however.  For example, we have $\reff{\bot}^+ x \rightarrow (\lambda p:\bot.p)x$.
\item
This relation does not play any part in the rules of deduction of $\lambda o e$.
The relation $\simeq_\beta$ that appears in the rules of $\lambda o e$ is the usual $\beta$-convertibility relation.  In particular, we \emph{do} allow $\beta$-contraction of open terms there: thus, the judgement $x : \Omega, p : (\lambda y : \Omega . y) x \vdash p : x$ is derivable in $\lambda o e$.  We shall always use the subscript $\beta$ when referring to this relation.
\end{enumerate}

\begin{lm}
$ $
\begin{enumerate}
\item
If $t \rightarrow t'$ then $t[x:=s] \rightarrow t'[x:=s]$.
\item
If $t \rightarrow t'$ then $s[x:=t] \twoheadrightarrow s[x:=t']$.
\item
If $M \rightarrow M'$ then $M \{ x:=P : N \sim N' \} \twoheadrightarrow M' \{ x:=P : N \sim N' \}$.
\item
If $P \rightarrow P'$ then $M \{ x:= P : N \sim N' \} \twoheadrightarrow M \{ x:=P' : N \sim N' \}$.
\end{enumerate}
\end{lm}

\begin{proof}
A straightforward induction in each case.  We give the details for one case in part 3, where $M \equiv (\lambda y:A.L)L'$ and $M' \equiv L[y:=L']$.  We have
\begin{align*}
((\lambda y:A.L)L') \{ x:=P \} & \eqdef (\triplelambda e : y =_A y' . L \{ x := P, y := e \})_{L'[x:=N] L'[x:=N']} L'\{ x:= P \} \\
& \rightarrow L \{ x:= P : N \sim N' , y := e : y \sim y' \} [ y := L' [x:=N], y' := L'[x:=Nl], e := L' \{ x:=P \} ] \\
& \equiv L \{ x := P : N \sim N' , y := L' \{ x := P \} : L' [ x := N ] \sim L' [ x := N' ] \} \\
& \equiv L [ y := L' ] \{ x := P \}
\end{align*}
\end{proof}

\begin{prop}
Reduction satisfies the diamond property: if $E \rightarrow F$ and $E \rightarrow G$ then there exists $H$ such that $F \rightarrow H$ and $G \rightarrow H$.
\end{prop}

\begin{proof}
Case analysis on $E \rightarrow F$ and $E \rightarrow G$.  There are no critical pairs thanks to our restriction that, if $E \rhd F$, then all proper subterms of $E$ are normal forms.
\end{proof}

\begin{cor}[Confluence]
$ $
\begin{enumerate}
\item
The reduction relation is confluent: if $E \twoheadrightarrow F$ and $E \twoheadrightarrow G$, then there exists $H$ such that $F \twoheadrightarrow H$ and $G \twoheadrightarrow H$.
\item
If $E \simeq F$, then there exists $G$ such that $E \twoheadrightarrow G$ and $F \twoheadrightarrow G$.
\end{enumerate}
\end{cor}

%<*Local-Confluent>
\begin{code}
Local-Confluent : ∀ {V} {C} {K} 
  {E F G : Subexpression V C K} → E ⇒ F → E ⇒ G → 
  Σ[ H ∈ Subexpression V C K ] (F ↠ H × G ↠ H)
\end{code}
%</Local-Confluent>

\AgdaHide{
\begin{code}
Local-Confluent (redex x) (redex y) = Critical-Pairs x y
Local-Confluent (redex r) (app E⇒G) = let (H ,p r⇒H ,p G↠H) = pre-Confluent r E⇒G in 
  H ,p G↠H ,p osr-red (redex r⇒H)
Local-Confluent (app E⇒F) (redex r) = let (H ,p r⇒H ,p G↠H) = pre-Confluent r E⇒F in 
  H ,p osr-red (redex r⇒H) ,p G↠H
Local-Confluent (app E⇒F) (app E⇒G) = let (H ,p F↠H ,p G↠H) = Local-Confluent E⇒F E⇒G in 
  app _ H ,p respects-red app F↠H ,p respects-red app G↠H
Local-Confluent (appl E⇒F) (appl E⇒G) = let (H ,p F↠H ,p G↠H) = Local-Confluent E⇒F E⇒G in 
  (H ,, _) ,p respects-red appl F↠H ,p respects-red appl G↠H
Local-Confluent (appl {E' = E'} E⇒F) (appr {F' = F'} E⇒G) = (E' ,, F') ,p osr-red (appr E⇒G) ,p osr-red (appl E⇒F)
Local-Confluent (appr {F' = F'} E⇒F) (appl {E' = E'} E⇒G) = E' ,, F' ,p (osr-red (appl E⇒G)) ,p (osr-red (appr E⇒F))
Local-Confluent (appr E⇒F) (appr E⇒G) = let (H ,p F↠H ,p G↠H) = Local-Confluent E⇒F E⇒G in
  (_ ,, H) ,p respects-red appr F↠H ,p respects-red appr G↠H
{-Local-Confluent (redex βT) (redex βT) = _ ,p ref ,p ref
Local-Confluent (redex βT) (app (appl (redex ())))
Local-Confluent (redex (βT {M = M} {N})) (app (appl (app (appl {E' = M'} M⇒M')))) = 
  M' ⟦ x₀:= N ⟧ ,p (red-subl (osr-red M⇒M')) ,p (osr-red (redex βT))
Local-Confluent (redex βT) (app (appl (app (appr ()))))
Local-Confluent (redex (βT {M = M})) (app (appr (appl {E' = N'} N⇒N'))) =
  M ⟦ x₀:= N' ⟧ ,p red-subr M (botsub-red N⇒N') ,p 
  (osr-red (redex βT))
Local-Confluent (redex βT) (app (appr (appr ())))
Local-Confluent (redex βR) (redex βR) = _ ,p ref ,p ref
Local-Confluent (redex βR) (app (appl (redex ())))
Local-Confluent (redex βR) (app (appl (app (appl φ⇒φ')))) = _ ,p ref ,p (osr-red (redex βR))
Local-Confluent (redex (βR {δ = δ} {ε = ε})) 
  (app (appl (app (appr (appl {E' = δ'} δ⇒δ'))))) = 
  δ' ⟦ x₀:= ε ⟧ ,p red-subl (osr-red δ⇒δ') ,p osr-red (redex βR)
Local-Confluent (redex βR) (app (appl (app (appr (appr ())))))
Local-Confluent (redex (βR {δ = δ})) (app (appr (appl {E' = ε'} ε⇒ε'))) = 
  δ ⟦ x₀:= ε' ⟧ ,p red-subr δ (botsub-red ε⇒ε') ,p osr-red (redex βR)
Local-Confluent (redex βR) (app (appr (appr ())))
Local-Confluent (redex βE) (redex βE) = _ ,p ref ,p ref
Local-Confluent (redex (βE {N = N} {A = A} {P = P} {Q = Q})) (app (appl {E' = M'} M⇒M')) = 
  P ⟦ x₂:= M' ,x₁:= N ,x₀:= Q ⟧ ,p red-subr P (botsub₃-red (osr-red M⇒M') ref ref) ,p osr-red (redex βE)
Local-Confluent (redex (βE {M = M} {P = P} {Q = Q})) (app (appr (appl {E' = N'} N⇒N'))) = 
  P ⟦ x₂:= M ,x₁:= N' ,x₀:= Q ⟧ ,p (red-subr P (botsub₃-red ref (osr-red N⇒N') ref)) ,p 
  osr-red (redex βE)
Local-Confluent (redex βE) (app (appr (appr (appl (redex ())))))
Local-Confluent (redex (βE {M = M} {N = N} {Q = Q})) (app (appr (appr (appl (app (appl {E' = P'} P⇒P')))))) = P' ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧ ,p (red-subl (osr-red P⇒P')) ,p osr-red (redex βE)
Local-Confluent (redex βE) (app (appr (appr (appl (app (appr ()))))))
Local-Confluent (redex (βE {M = M} {N = N} {P = P})) (app (appr (appr (appr (appl {E' = Q'} Q⇒Q'))))) = P ⟦ x₂:= M ,x₁:= N ,x₀:= Q' ⟧ ,p (red-subr P (botsub₃-red ref ref (osr-red Q⇒Q'))) ,p (osr-red (redex βE))
Local-Confluent (redex βE) (app (appr (appr (appr (appr ())))))
Local-Confluent (redex plus-ref) (redex plus-ref) = _ ,p (ref ,p ref)
Local-Confluent (redex plus-ref) (app (appl (redex ())))
Local-Confluent (redex plus-ref) (app (appl (app (appl {E' = φ'} φ⇒φ')))) = ΛP φ' (var x₀)  ,p (osr-red (app (appl φ⇒φ'))) ,p (osr-red (redex plus-ref))
Local-Confluent (redex plus-ref) (app (appl (app (appr ()))))
Local-Confluent (redex plus-ref) (app (appr ()))
Local-Confluent (redex minus-ref) (redex minus-ref) = _ ,p ref ,p ref
Local-Confluent (redex minus-ref) (app (appl (redex ())))
Local-Confluent (redex minus-ref) (app (appl (app (appl {E' = φ'} φ⇒φ')))) = ΛP φ' (var x₀) ,p (osr-red (app (appl φ⇒φ'))) ,p (osr-red (redex minus-ref))
Local-Confluent (redex minus-ref) (app (appl (app (appr ()))))
Local-Confluent (redex minus-ref) (app (appr ()))
Local-Confluent (redex plus-univ) (redex plus-univ) = _ ,p ref ,p ref
Local-Confluent (redex plus-univ) (app (appl (redex ())))
Local-Confluent (redex plus-univ) (app (appl (app (appl _)))) = 
  _ ,p ref ,p osr-red (redex plus-univ)
Local-Confluent (redex plus-univ) (app (appl (app (appr (appl _))))) = 
  _ ,p ref ,p (osr-red (redex plus-univ))
Local-Confluent (redex plus-univ) (app (appl (app (appr (appr (appl δ⇒δ')))))) = 
  _ ,p osr-red δ⇒δ' ,p osr-red (redex plus-univ)
Local-Confluent (redex plus-univ) (app (appl (app (appr (appr (appr (appl E⇒G))))))) = 
  _ ,p ref ,p osr-red (redex plus-univ)
Local-Confluent (redex plus-univ) (app (appl (app (appr (appr (appr (appr ())))))))
Local-Confluent (redex plus-univ) (app (appr ()))
Local-Confluent (redex minus-univ) (redex minus-univ) = _ ,p ref ,p ref
Local-Confluent (redex minus-univ) (app (appl (redex ())))
Local-Confluent (redex minus-univ) (app (appl (app (appl _)))) = 
  _ ,p ref ,p osr-red (redex minus-univ)
Local-Confluent (redex minus-univ) (app (appl (app (appr (appl _))))) = 
  _ ,p ref ,p (osr-red (redex minus-univ))
Local-Confluent (redex minus-univ) (app (appl (app (appr (appr (appl _)))))) = 
  _ ,p ref ,p osr-red (redex minus-univ)
Local-Confluent (redex minus-univ) (app (appl (app (appr (appr (appr (appl ε⇒ε'))))))) = 
  _ ,p osr-red ε⇒ε' ,p osr-red (redex minus-univ)
Local-Confluent (redex minus-univ) (app (appl (app (appr (appr (appr (appr ())))))))
Local-Confluent (redex minus-univ) (app (appr ()))
Local-Confluent (redex ref⊃*univ) (redex ref⊃*univ) = 
  _ ,p ref ,p ref
Local-Confluent (redex ref⊃*univ) (app (appl (redex ())))
Local-Confluent (redex ref⊃*univ) (app (appl (app (appl φ⇒φ')))) = 
  _ ,p univ-red (osr-red (app (appl φ⇒φ'))) (osr-red (app (appl φ⇒φ'))) 
    (ΛP-red (osr-red (app (appl φ⇒φ'))) (ΛP-red (apredr replacement R-respects-replacement (osr-red φ⇒φ')) ref)) (ΛP-red (osr-red (app (appl φ⇒φ'))) (ΛP-red (apredr replacement R-respects-replacement (osr-red φ⇒φ')) ref)) ,p osr-red (redex ref⊃*univ)
Local-Confluent (redex ref⊃*univ) (app (appl (app (appr ()))))
Local-Confluent (redex ref⊃*univ) (app (appr (appl E⇒G))) = {!!}
Local-Confluent (redex ref⊃*univ) (app (appr (appr E⇒G))) = {!!}
Local-Confluent (redex univ⊃*ref) E⇒G = {!!}
Local-Confluent (redex univ⊃*univ) E⇒G = {!!}
Local-Confluent (redex ref⊃*ref) E⇒G = {!!}
Local-Confluent (redex refref) E⇒G = {!!}
Local-Confluent (redex reflamvar) E⇒G = {!!}
Local-Confluent (redex reflam⊃*) E⇒G = {!!}
Local-Confluent (redex reflamuniv) E⇒G = {!!}
Local-Confluent (redex reflamλλλ) E⇒G = {!!}
Local-Confluent (app E⇒F) E⇒G = {!!} -}
--TODO General theory of reduction
\end{code}
}

\begin{code}
postulate Newmans : ∀ {V} {C} {K} {E F G : Subexpression V C K} → 
                  SN E → (E ↠ F) → (E ↠ G) →
                  Σ[ H ∈ Subexpression V C K ] (F ↠ H × G ↠ H)

postulate ChurchRosserT : ∀ {V} {M N P : Term V} → M ↠ N → M ↠ P →
                        Σ[ Q ∈ Term V ] N ↠ Q × P ↠ Q

postulate confluenceT : ∀ {V} {M N : Term V} → M ≃ N →
                        Σ[ Q ∈ Term V ] M ↠ Q × N ↠ Q

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
bot-red' (osr-red (app {c = -bot} {F = out} x)) _ = refl
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
imp-red' {θ = θ} (osr-red (app {c = -imp} (appl {E' = χ'} {F = _ ,, out} χ⇒χ'))) φ≡χ⊃θ = 
  χ' ,p θ ,p subst (λ x → x ↠ χ') (imp-injl φ≡χ⊃θ) (osr-red χ⇒χ') ,p 
  ref ,p (cong (λ x → χ' ⊃ x) (imp-injr φ≡χ⊃θ))
imp-red' {χ = χ} (osr-red (app {c = -imp} (appr (appl {E' = θ'} {F = out} θ⇒θ')))) φ≡χ⊃θ = 
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
\end{code}
