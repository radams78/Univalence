\AgdaHide{
\begin{code}
module PHOPL.Red where
open import Data.Unit
open import Data.Product hiding (_,_)
open import Data.List
open import PHOPL.Grammar
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
  βR : ∀ {V} {φ} {δ} {ε} → R {V} -appProof (ΛP φ δ ,, ε ,, out) (δ ⟦ x₀:= ε ⟧)
  βE : ∀ {V} {M} {N} {A} {P} {Q} → R {V} -app* (M ,, N ,, λλλ A P ,, Q ,, out) (P ⟦ x₀:= M • x₀:= (N ⇑) • x₀:= (Q ⇑ ⇑) ⟧)
  plus-ref : ∀ {V} {φ} → R {V} -plus (reff φ ,, out) (ΛP φ (var x₀))
  minus-ref : ∀ {V} {φ} → R {V} -minus (reff φ ,, out) (ΛP φ (var x₀))
  plus-univ : ∀ {V} {φ} {ψ} {δ} {ε} → R {V} -plus (univ φ ψ δ ε ,, out) δ 
  minus-univ : ∀ {V} {φ} {ψ} {δ} {ε} → R {V} -minus (univ φ ψ δ ε ,, out) ε
\end{code}
}

\begin{frame}[fragile]
\frametitle{The Reduction Relation}
We make $\mathsf{univ}$ and $\mathsf{ref}$ move out past $\supset^*$ and application:
\begin{align*}
& \reff \phi \supset^* \univ{\psi}{\chi}{\delta}{\epsilon}
\rhd \mathsf{univ}_{\phi \supset \psi,\phi \supset \chi}(\lambda p, q . \delta (p q), \lambda p, q . \epsilon (p q)) \\
& \univ{\phi}{\psi}{\delta}{\epsilon} \supset^* \reff{\chi}
\rhd \univ{\phi \supset \chi}{\psi \supset \chi}{\lambda p,q .p (\epsilon q)}{\lambda p,q .p (\delta q)}
\\
& \univ{\phi}{\psi}{\delta}{\epsilon} \supset^* \univ{\phi'}{\psi'}{\delta'}{\epsilon'} \\
& \quad \rhd \univ{\phi \supset \phi'}{\psi \supset \psi'}
{\lambda p,q . \delta' (p (\epsilon q))}{\lambda p, q . \epsilon' (p (\delta q))}
\\
& \reff{\phi} \supset^* \reff{\psi} \rhd \reff{\phi \supset \psi}
\qquad
\reff{M} \reff{N} \rhd \reff{MN}
\end{align*}
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

\begin{frame}
\frametitle{The Reduction Relation}
We construct a proof of $M =_{A \rightarrow B} N$, then apply it.  What is the result?
\begin{itemize}[<+->]
\item
$\reff{M} \reff{N} \rhd \reff{MN}$
\item
$(\triplelambda e:x =_A y. P)_{MN}Q \rhd P[x:=M, y:=N, e:=Q]$
\item
$\reff{\lambda x:A.M} P \rhd ???$
\end{itemize}
\end{frame}

\mode<all>{\input{PHOPL/PathSub.lagda}}

\AgdaHide{
\begin{code}
  refref : ∀ {V} {M} {N} → R {V} -app* (N ,, N ,, reff M ,, reff N ,, out) (reff (appT M N))

open import Reduction PHOPL R public renaming (_⇒_ to _⇒R_;_↠_ to _↠R_;_≃_ to _≃R_;redex to redexR;app to appR;appl to applR;appr to apprR;creates' to creates'R;
  respects' to respects'R;respects-osr to respects-osrR;respects-conv to respects-convR;
  osr-conv to osr-convR; sym-conv to sym-convR; trans-conv to trans-convR;osr-red to osr-redR;ref to refR;trans-red to trans-redR;
  respects-red to respects-redR;redex-conv to redex-convR)
--TODO Tidy up

postulate R-creates-rep : creates'R replacement

postulate R-respects-replacement : respects'R replacement

postulate R-creates-replacement : creates'R replacement

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
