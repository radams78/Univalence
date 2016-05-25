\AgdaHide{
\begin{code}
module PHOPL.Red where
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import PHOPL.Grammar
open import PHOPL.PathSub
\end{code}
}

\begin{frame}[fragile]
\frametitle{The Reduction Relation}
\begin{code}
data R : Reduction where
\end{code}

The `$\beta$-rules':

\begin{align*}
(\lambda x:A.M)N & \rhd M[x:=N] & (\lambda p:\phi.\delta)\epsilon & \rhd \delta[p:=\epsilon] \\
 \reff{\phi}^+ & \rhd \lambda p:\phi.p & \reff{\phi}^- & \rhd \lambda p:\phi.p \\
\univ{\phi}{\psi}{\delta}{\epsilon}^+ & \rhd \delta & \univ{\phi}{\psi}{\delta}{\epsilon}^- & \rhd \epsilon
\end{align*}
\end{frame}

\AgdaHide{
\begin{code}
  βT : ∀ {V} {A} {M} {N} → R {V} -appTerm (ΛT A M ,, N ,, out) (M ⟦ x₀:= N ⟧)
  βR : ∀ {V} {φ} {δ} {ε} → R {V} -appProof (ΛP φ δ ,, ε ,, out) (δ ⟦ x₀:= ε ⟧)
  plus-ref : ∀ {V} {φ} → R {V} -plus (reff φ ,, out) (ΛP φ (var x₀))
  minus-ref : ∀ {V} {φ} → R {V} -minus (reff φ ,, out) (ΛP φ (var x₀))
  plus-univ : ∀ {V} {φ} {ψ} {δ} {ε} → R {V} -plus (univ φ ψ δ ε ,, out) δ 
  minus-univ : ∀ {V} {φ} {ψ} {δ} {ε} → R {V} -minus (univ φ ψ δ ε ,, out) ε
\end{code}
}

\begin{frame}[fragile]
\frametitle{The Reduction Relation}
We make $\mathsf{univ}$ and $\mathsf{ref}$ move out past $\supset^*$ and application:
$$\reff \phi \supset^* \univ{\psi}{\chi}{\delta}{\epsilon}
\rhd \mathsf{univ}_{\phi \supset \psi,\phi \supset \chi}(\lambda p, q . \delta (p q), \lambda p, q . \epsilon (p q))$$
$$\univ{\phi}{\psi}{\delta}{\epsilon} \supset^* \reff{\chi}
\rhd \univ{\phi \supset \chi}{\psi \supset \chi}{\lambda p,q .p (\epsilon q)}{\lambda p,q .p (\delta q)}$$
\begin{gather*}
\univ{\phi}{\psi}{\delta}{\epsilon} \supset^* \univ{\phi'}{\psi'}{\delta'}{\epsilon'} \\
\quad \rhd \univ{\phi \supset \phi'}{\psi \supset \psi'}
{\lambda p,q . \delta' (p (\epsilon q))}{\lambda p, q . \epsilon' (p (\delta q))}
\end{gather*}
$$\reff{\phi} \supset^* \reff{\psi} \rhd \reff{\phi \supset \psi}
\qquad
\reff{M} \reff{N} \rhd \reff{MN}$$
\end{frame}

\AgdaHide{
\begin{code}
  ref⊃*univ : ∀ {V} {φ} {ψ} {χ} {δ} {ε} → R {V} -imp* (reff φ ,, univ ψ χ δ ε ,, out) (univ (φ ⊃ ψ) (φ ⊃ χ) (ΛP (φ ⊃ ψ) (ΛP (φ ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (var x₀))))) (ΛP (φ ⊃ χ) (ΛP (φ ⇑) (appP (ε ⇑ ⇑) (appP (var x₁) (var x₀))))))
  univ⊃*ref : ∀ {V} {φ} {ψ} {χ} {δ} {ε} → R {V} -imp* (univ φ ψ δ ε ,, reff χ ,, out) (univ (φ ⊃ χ) (ψ ⊃ χ) (ΛP (φ ⊃ χ) (ΛP (ψ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀))))) (ΛP (ψ ⊃ χ) (ΛP (φ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀))))))
  univ⊃*univ : ∀ {V} {φ} {φ'} {ψ} {ψ'} {δ} {δ'} {ε} {ε'} →
    R {V} -imp* (univ φ ψ δ ε ,, univ φ' ψ' δ' ε' ,, out)
    (univ (φ ⊃ φ') (ψ ⊃ ψ') (ΛP (φ ⊃ φ') (ΛP (ψ ⇑) (appP (δ' ⇑ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀))))))
      (ΛP (ψ ⊃ ψ') (ΛP (φ ⇑) (appP (ε' ⇑ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀)))))))
  ref⊃*ref : ∀ {V} {φ} {ψ} → R {V} -imp* (reff φ ,, reff ψ ,, out) (reff (φ ⊃ ψ))
\end{code}
}

\begin{frame}[fragile]
\frametitle{The Reduction Relation}
We construct a proof of $M =_{A \rightarrow B} N$, then apply it.  What is the result?
\begin{itemize}[<+->]
\item
$\reff{M} \reff{N} \rhd \reff{MN}$
\item
$(\triplelambda e:x =_A y. P)_{MN}Q \rhd P[x:=M, y:=N, e:=Q]$
\item
If $P \not\equiv \reff{-}$, then $\reff{\lambda x:A.M} P \rhd ???$
\end{itemize}

\only<2>{$\Gamma , x : A , y : A , e : x=_A y ⊢ P : L =_B L', \qquad \Gamma \vdash Q : M =_A N$}

\only<3>{$\Gamma , x : A \vdash M : B, \qquad \Gamma \vdash P : N =_A N'$}
\end{frame}

\mode<all>{\input{PHOPL/PathSub.lagda}}

\begin{frame}[fragile]
\frametitle{The Reduction Relation}
We construct a proof of $M =_{A \rightarrow B} N$, then apply it.  What is the result?
\begin{itemize}
\item
$\reff{M} \reff{N} \rhd \reff{MN}$
\item
$(\triplelambda e:x =_A y. P)_{MN}Q \rhd P[x:=M, y:=N, e:=Q]$
\item
If $P \not\equiv \reff{-}$, then $\reff{\lambda x:A.M}_{N,N'} P \rhd M \{ x := P : N ∼ N' \}$
\end{itemize}
\end{frame}

\AgdaHide{
\begin{code}
  refref : ∀ {V} {M} {N} → R {V} -app* (N ,, N ,, reff M ,, reff N ,, out) (reff (appT M N))
  βE : ∀ {V} {M} {N} {A} {P} {Q} → R {V} -app* (M ,, N ,, λλλ A P ,, Q ,, out) 
    (P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧)
  reflamvar : ∀ {V} {N} {N'} {A} {M} {e} → R {V} -app* (N ,, N' ,, reff (ΛT A M) ,, var e ,, out) (M ⟦⟦ x₀::= (var e) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
  reflam⊃* : ∀ {V} {N} {N'} {A} {M} {P} {Q} → R {V} -app* (N ,, N' ,, reff (ΛT A M) ,, (P ⊃* Q) ,, out) (M ⟦⟦ x₀::= (P ⊃* Q) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
  reflamuniv : ∀ {V} {N} {N'} {A} {M} {φ} {ψ} {δ} {ε} → R {V} -app* (N ,, N' ,, reff (ΛT A M) ,, univ φ ψ δ ε ,, out) (M ⟦⟦ x₀::= (univ φ ψ δ ε) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
  reflamλλλ : ∀ {V} {N} {N'} {A} {M} {B} {P} → R {V} -app* (N ,, N' ,, reff (ΛT A M) ,, λλλ B P ,, out) (M ⟦⟦ x₀::= (λλλ B P) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)

open import Reduction PHOPL R public 

postulate eq-resp-conv : ∀ {V} {M M' N N' : Term V} {A : Type} →
                       M ≃ M' → N ≃ N' → M ≡〈 A 〉 N ≃ M' ≡〈 A 〉 N'

postulate R-creates-rep : creates' replacement

postulate R-respects-replacement : respects' replacement

postulate R-creates-replacement : creates' replacement

postulate R-respects-sub : respects' substitution

red-subl : ∀ {V} {E F : Term (V , -Term)} {G} → E ↠ F → E ⟦ x₀:= G ⟧ ↠ F ⟦ x₀:= G ⟧
red-subl E↠F = respects-red (respects-osr substitution R-respects-sub) E↠F

postulate ⊥SN : ∀ {V} → SN {V} ⊥

postulate ⊃SN : ∀ {V} {φ ψ : Term V} → SN φ → SN ψ → SN (φ ⊃ ψ)

all-SN : ∀ {V} → List (Term V) → Set
all-SN [] = ⊤
all-SN (M ∷ MM) = SN M × all-SN MM
--TODO Use Data.List library
--TODO Delete?

postulate var-APP-SN : ∀ {V} (x : Var V -Term) (MM : List (Term V)) →
                     all-SN MM → SN (APP (var x) MM)
--TODO Move to Reduction library
--TODO Delete?

postulate SN-βexp : ∀ {V} {φ : Term V} {δ : Proof (V , -Proof)} {ε : Proof V} →
                  SN ε → SN (δ ⟦ x₀:= ε ⟧) → SN (appP (ΛP φ δ) ε) 

\end{code}
}

\begin{frame}[fragile]
\frametitle{Confluence}
\begin{theorem}[Local Confluence]
The reduction is locally confluent.
\end{theorem}

\begin{code}
Local-Confluent : ∀ {V} {K} {E F G : Expression V K} →
                  E ⇒ F → E ⇒ G → 
                  Σ[ H ∈ Expression V K ] (F ↠ H × G ↠ H)
\end{code}

\AgdaHide{
\begin{code}
Local-Confluent (redex βT) δ = {!!}
Local-Confluent (redex βR) (redex βR) = _ ,p ref ,p ref
Local-Confluent (redex βR) (app (appl (redex ())))
Local-Confluent (redex βR) (app (appl (app (appl φ⇒φ')))) = _ ,p ref ,p (osr-red (redex βR))
Local-Confluent (redex (βR {δ = δ} {ε = ε})) 
  (app (appl (app (appr (appl {E' = δ'} δ⇒δ'))))) = 
  δ' ⟦ x₀:= ε ⟧ ,p {!red-subl!} ,p osr-red (redex βR)
Local-Confluent (redex βR) (app (appl (app (appr (appr E⇒G))))) = {!!}
Local-Confluent (redex βR) (app (appr E⇒G)) = {!!}
Local-Confluent (redex βE) E⇒G = {!!}
Local-Confluent (redex plus-ref) E⇒G = {!!}
Local-Confluent (redex minus-ref) E⇒G = {!!}
Local-Confluent (redex plus-univ) E⇒G = {!!}
Local-Confluent (redex minus-univ) E⇒G = {!!}
Local-Confluent (redex ref⊃*univ) E⇒G = {!!}
Local-Confluent (redex univ⊃*ref) E⇒G = {!!}
Local-Confluent (redex univ⊃*univ) E⇒G = {!!}
Local-Confluent (redex ref⊃*ref) E⇒G = {!!}
Local-Confluent (redex refref) E⇒G = {!!}
Local-Confluent (redex reflamvar) E⇒G = {!!}
Local-Confluent (redex reflam⊃*) E⇒G = {!!}
Local-Confluent (redex reflamuniv) E⇒G = {!!}
Local-Confluent (redex reflamλλλ) E⇒G = {!!}
Local-Confluent (app E⇒F) E⇒G = {!!}
\end{code}
}

\begin{corollary}
Every strongly normalizing term is confluent, hence has a unique normal form.
\end{corollary}

\begin{code}
Newmans : ∀ {V} {C} {K} {E F G : Subexpression V C K} → 
  SN E → (E ↠ F) → (E ↠ G) →
  Σ[ H ∈ Subexpression V C K ] (F ↠ H × G ↠ H)
\end{code}
\end{frame}

\AgdaHide{
\begin{code}
Newmans = {!!}
\end{code}
}
