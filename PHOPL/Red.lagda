\AgdaHide{
\begin{code}
module PHOPL.Red where
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import PHOPL.Grammar
open import PHOPL.PathSub
open import PHOPL.Rules
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
If $P \not\equiv \reff{-}$, then $\reff{\lambda x:A.M} P \rhd ???$
\end{itemize}
\end{frame}

\mode<all>{\input{PHOPL/PathSub.lagda}}

\begin{frame}
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
  lllred : ∀ {V} {A} {P} {M} {N} {Q} → R {V} -app* (M ,, N ,, λλλ A P ,, Q ,, out) (P ⟦ x₀:= M • x₀:= (N ⇑) • x₀:= (Q ⇑ ⇑) ⟧) --TODO Definition for triple substitution
  reflamvar : ∀ {V} {N} {N'} {A} {M} {e} → R {V} -app* (N ,, N' ,, reff (ΛT A M) ,, var e ,, out) (M ⟦⟦ x₀::= (var e) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
  reflam⊃* : ∀ {V} {N} {N'} {A} {M} {P} {Q} → R {V} -app* (N ,, N' ,, reff (ΛT A M) ,, (P ⊃* Q) ,, out) (M ⟦⟦ x₀::= (P ⊃* Q) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
  reflamuniv : ∀ {V} {N} {N'} {A} {M} {φ} {ψ} {δ} {ε} → R {V} -app* (N ,, N' ,, reff (ΛT A M) ,, univ φ ψ δ ε ,, out) (M ⟦⟦ x₀::= (univ φ ψ δ ε) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
  reflamλλλ : ∀ {V} {N} {N'} {A} {M} {B} {P} → R {V} -app* (N ,, N' ,, reff (ΛT A M) ,, λλλ B P ,, out) (M ⟦⟦ x₀::= (λλλ B P) ∶ x₀:= N ∼ x₀:= N' ⟧⟧)

open import Reduction PHOPL R public renaming (_⇒_ to _⇒R_;_↠_ to _↠R_;_≃_ to _≃R_;redex to redexR;app to appR;appl to applR;appr to apprR;creates' to creates'R;
  respects' to respects'R;respects-osr to respects-osrR;respects-conv to respects-convR;
  osr-conv to osr-convR; sym-conv to sym-convR; trans-conv to trans-convR;osr-red to osr-redR;ref to refR;trans-red to trans-redR;
  respects-red to respects-redR;redex-conv to redex-convR)
--TODO Tidy up

postulate R-creates-rep : creates'R replacement

postulate R-respects-replacement : respects'R replacement

postulate R-creates-replacement : creates'R replacement

postulate R-respects-sub : respects'R substitution

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
\frametitle{Subject Reduction}

\begin{theorem}[Subject Reduction]
Let $E$ be a path (proof, term) and $A$ an equation (term, type).
If $\Gamma \vdash E : A$ and $E \twoheadrightarrow F$ then $\Gamma \vdash F : A$.
\end{theorem}

\AgdaHide{
\begin{code}
postulate Generation-ΛP : ∀ {V} {Γ : Context V} {φ} {δ} {ε} {ψ} →
                       Γ ⊢ appP (ΛP φ δ) ε ∶ ψ →
                       Σ[ χ ∈ Term V ] 
                       (ψ ≃ φ ⊃ χ × Γ ,P φ ⊢ δ ∶ χ ⇑)

postulate Subject-Reduction-R : ∀ {V} {K} {C} 
                              {c : Constructor C} {E : Body V C} {F : Expression V (varKind K)} {Γ} {A} →
                              Γ ⊢ (app c E) ∶ A → R c E F → Γ ⊢ F ∶ A

{-Subject-Reduction-R : ∀ {V} {K} {C} 
  {c : Constructor C} {E : Body V C} {F : Expression V (varKind K)} {Γ} {A} →
  Γ ⊢ (app c E) ∶ A → R c E F → Γ ⊢ F ∶ A
Subject-Reduction-R Γ⊢ΛPφδε∶A βR =
  let (χ ,p A≃φ⊃χ ,p Γ,φ⊢δ∶χ) = Generation-ΛP Γ⊢ΛPφδε∶A in {!!}
Subject-Reduction-R Γ⊢cE∶A βE = {!!}
Subject-Reduction-R Γ⊢cE∶A plus-ref = {!!}
Subject-Reduction-R Γ⊢cE∶A minus-ref = {!!}
Subject-Reduction-R Γ⊢cE∶A plus-univ = {!!}
Subject-Reduction-R Γ⊢cE∶A minus-univ = {!!}
Subject-Reduction-R Γ⊢cE∶A ref⊃*univ = {!!}
Subject-Reduction-R Γ⊢cE∶A univ⊃*ref = {!!}
Subject-Reduction-R Γ⊢cE∶A univ⊃*univ = {!!}
Subject-Reduction-R Γ⊢cE∶A ref⊃*ref = {!!}
Subject-Reduction-R Γ⊢cE∶A refref = {!!}
Subject-Reduction-R Γ⊢cE∶A lllred = {!!}
Subject-Reduction-R Γ⊢cE∶A reflamvar = {!!}
Subject-Reduction-R Γ⊢cE∶A reflam⊃* = {!!}
Subject-Reduction-R Γ⊢cE∶A reflamuniv = {!!}
Subject-Reduction-R Γ⊢cE∶A reflamλλλ = {!!} -}
\end{code}
}

\begin{code}
postulate Subject-Reduction : ∀ {V} {K} {Γ}
                            {E F : Expression V (varKind K)} {A} → 
                            (Γ ⊢ E ∶ A) → (E ↠R F) → (Γ ⊢ F ∶ A)
\end{code}

\begin{theorem}[Local Confluence]
The reduction is locally confluent.
\end{theorem}

\begin{code}
postulate Local-Confluent : ∀ {V} {K} {E F G : Expression V K} →
                  E ⇒R F → E ⇒R G → 
                  Σ[ H ∈ Expression V K ] (F ↠R H × G ↠R H)
\end{code}

\AgdaHide{
\begin{code}
{-Local-Confluent (redexR βR) (redexR βR) = _ ,p refR ,p refR
Local-Confluent (redexR βR) (appR (applR (redexR ())))
Local-Confluent (redexR βR) (appR (applR (appR (applR φ⇒φ')))) = _ ,p refR ,p (osr-redR (redexR βR))
Local-Confluent (redexR (βR {δ = δ} {ε = ε})) 
  (appR (applR (appR (apprR (applR {E' = δ'} δ⇒δ'))))) = 
  δ' ⟦ x₀:= ε ⟧ ,p (respects-redR {f = λ x → x ⟦ x₀:= ε ⟧} (respects-osrR substitution R-respects-sub) {M = δ} {N = δ'} (osr-redR δ⇒δ')) ,p osr-redR (redexR βR)
Local-Confluent (redexR βR) (appR (applR (appR (apprR (apprR E⇒G))))) = {!!}
Local-Confluent (redexR βR) (appR (apprR E⇒G)) = {!!}
Local-Confluent (redexR βE) E⇒G = {!!}
Local-Confluent (redexR plus-ref) E⇒G = {!!}
Local-Confluent (redexR minus-ref) E⇒G = {!!}
Local-Confluent (redexR plus-univ) E⇒G = {!!}
Local-Confluent (redexR minus-univ) E⇒G = {!!}
Local-Confluent (redexR ref⊃*univ) E⇒G = {!!}
Local-Confluent (redexR univ⊃*ref) E⇒G = {!!}
Local-Confluent (redexR univ⊃*univ) E⇒G = {!!}
Local-Confluent (redexR ref⊃*ref) E⇒G = {!!}
Local-Confluent (redexR refref) E⇒G = {!!}
Local-Confluent (redexR lllred) E⇒G = {!!}
Local-Confluent (redexR reflamvar) E⇒G = {!!}
Local-Confluent (redexR reflam⊃*) E⇒G = {!!}
Local-Confluent (redexR reflamuniv) E⇒G = {!!}
Local-Confluent (redexR reflamλλλ) E⇒G = {!!}
Local-Confluent (appR E⇒F) E⇒G = {!!} -}
\end{code}
}

\begin{corollary}
Every strongly normalizing term is confluent, hence has a unique normal form.
\end{corollary}
\end{frame}

