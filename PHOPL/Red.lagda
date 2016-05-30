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

red-subl : ∀ {U} {V} {C} {K} {E F : Subexpression U C K} {σ : Sub U V} → E ↠ F → E ⟦ σ ⟧ ↠ F ⟦ σ ⟧
red-subl E↠F = respects-red (respects-osr substitution R-respects-sub) E↠F

postulate red-subr : ∀ {U} {V} {C} {K} (E : Subexpression U C K) {ρ σ : Sub U V} → _↠s_ substitution ρ σ → E ⟦ ρ ⟧ ↠ E ⟦ σ ⟧

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

\begin{frame}[fragile]
\frametitle{Confluence}
\begin{theorem}[Local Confluence]
The reduction is locally confluent.
\end{theorem}

\begin{code}
Local-Confluent : ∀ {V} {C} {K} {E F G : Subexpression V C K} →
                  E ⇒ F → E ⇒ G → 
                  Σ[ H ∈ Subexpression V C K ] (F ↠ H × G ↠ H)
\end{code}

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

\begin{corollary}
Every strongly normalizing term is confluent, hence has a unique normal form.
\end{corollary}

\begin{code}
postulate Newmans : ∀ {V} {C} {K} {E F G : Subexpression V C K} → 
                  SN E → (E ↠ F) → (E ↠ G) →
                  Σ[ H ∈ Subexpression V C K ] (F ↠ H × G ↠ H)
\end{code}
\end{frame}