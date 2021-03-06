\AgdaHide{
\begin{code}
module PHOPL.MainProp where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Rules
open import PHOPL.PathSub
open import PHOPL.Red
open import PHOPL.Meta
open import PHOPL.Computable
open import PHOPL.SubC
open import PHOPL.KeyRedex

  {!let φ' : MeanTerm φ        φ' = ? in ?!}
\end{code}
}

Our main theorem is as follows.

\begin{theorem}$ $
\label{theorem:mainprop}
\begin{enumerate}
\item
If $\Gamma \vdash t : T$ and $\sigma : \Gamma \Rightarrow \Delta$ is computable, and $\Delta \vald$, then $t[\sigma] \in E_\Delta(T[\sigma])$.

\begin{code}
postulate toPathC : ∀ {U V} {σ : Sub U V} {Γ Δ} → σ ∶ Γ ⇒C Δ → toPath σ ∶ σ ∼ σ ∶ Γ ⇒C Δ

Computable-Sub : ∀ {U V K} (σ : Sub U V) {Γ Δ} 
                 {M : Expression U (varKind K)} {A} →
                 σ ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → E Δ (A ⟦ σ ⟧) (M ⟦ σ ⟧)
\end{code}

\item
\label{computable-path-sub}
If $\Gamma \vdash M : A$, $\tau : \sigma \sim \rho : \Gamma \Rightarrow \Delta$, and $\tau$, $\sigma$
and $\rho$ are all computable, and $\Delta \vald$, then $M \{ \tau : \sigma \sim \rho \} \in E_\Delta(M [ \sigma ] =_A M [ \rho ])$.

\begin{code}
postulate computable-path-substitution : ∀ {U V} (τ : PathSub U V) {σ σ' Γ Δ M A} → 
                                       σ ∶ Γ ⇒C Δ → σ' ∶ Γ ⇒C Δ → τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → 
                                       E Δ (M ⟦ σ ⟧ ≡〈 yt A 〉 M ⟦ σ' ⟧) (M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧) 
\end{code}

\end{enumerate}
\end{theorem}

\begin{proof}
The four parts are proved simultaneously by induction on derivations.

\begin{itemize}
\item
$$ \infer[(x : A \in \Gamma)]{\Gamma \vdash x : A}{\Gamma \vald} $$

We have that $\sigma(x) \in E_\Delta(A)$ and $\tau(x) \in E_\Delta(\rho(x) =_A \sigma(x))$ by hypothesis.
\item
$$ \infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald}$$

We have that $\sigma(p) \in E_\Delta(\phi[\sigma])$ by hypothesis.
\AgdaHide{
\begin{code}
Computable-Sub _ σ∶Γ⇒CΔ (varR x _) _ = σ∶Γ⇒CΔ x
\end{code}
}

\item
$$ \infer{\Gamma \vdash \bot : \Omega}{\Gamma \vald} $$

From Lemma \ref{lm:Ebot}, we have $\bot \in E_\Delta(\Omega)$ and therefore
$\bot\{\} \in E_\Delta(\bot =_\Omega \bot)$.

\AgdaHide{
\begin{code}

Computable-Sub _ _ (⊥R _) validΔ = E-⊥ validΔ
\end{code}
}

\item
$$ \infer{\Gamma \vdash \phi \supset \psi : \Omega}{\Gamma \vdash \phi : \Omega \quad \Gamma \vdash \psi : \Omega} $$

By the induction hypothesis, $\phi[\sigma], \psi[\sigma] \in \SN$, hence $\phi[\sigma] \supset \psi[\sigma] \in \SN$.

Also by the induction hypothesis, we have $\phi[\sigma]\{\} \in E_\Delta(\phi[\sigma] =_\Omega \phi[\sigma])$, and
$\psi[\sigma]\{\} \in E_\Delta(\psi[\sigma] =_\Omega \psi[\sigma])$.  Therefore, $\phi[\sigma]\{\} \supset^* \psi[\sigma]\{\}
\in E_\Delta(\phi[\sigma] \supset \psi[\sigma] =_\Omega \phi[\sigma] \supset \psi[\sigma])$ by Lemma \ref{lm:Esupset}.

\begin{code}
Computable-Sub σ σ∶Γ⇒CΔ (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = 
  ⊃-E (Computable-Sub σ σ∶Γ⇒CΔ Γ⊢φ∶Ω validΔ) (Computable-Sub σ σ∶Γ⇒CΔ Γ⊢ψ∶Ω validΔ)
\end{code}

\item
$$ \infer{\Gamma \vdash M N : B} {\Gamma \vdash M : A \rightarrow B \quad \Gamma \vdash N : A} $$

\begin{enumerate}
\item[1]
We have $M[\sigma] \in E_\Delta(A \rightarrow B)$ and $N[\sigma] \in E_\Delta(A)$, so $M[\sigma] N[\sigma] \in E_\Delta(B)$.

\begin{code}
Computable-Sub σ σ∶Γ⇒CΔ (appR Γ⊢M∶A⇛B Γ⊢N∶A) validΔ = appT-E validΔ (Computable-Sub σ σ∶Γ⇒CΔ Γ⊢M∶A⇛B validΔ) (Computable-Sub σ σ∶Γ⇒CΔ Γ⊢N∶A validΔ)
\end{code}

\item[4]
We have $M\{\tau\} \in E_\Delta(M [ \rho ] =_{A \rightarrow B} M [ \sigma ])$ and $N[\rho], N[\sigma] \in E_\Delta(A)$,
$N \{ \tau \} \in E_\Delta(N[ \rho ] =_A N[\sigma])$ by the induction hypothesis (1) and (4).  Therefore,
$M \{ \tau \}_{N[\rho] N[\sigma]} N \{ \tau \} \in E_\Delta(M[\rho] N[\rho] =_B M[\sigma] N[\sigma])$.

\end{enumerate}

\item
$$\infer{\Gamma \vdash \delta \epsilon : \psi} {\Gamma \vdash \delta : \phi \supset \psi \quad \Gamma \vdash \epsilon : \phi}$$

We have $\delta [ \sigma ] \in E_\Delta(\phi [ \sigma ] \supset \psi [ \sigma ])$ and $\epsilon [ \sigma ] \in E_\Delta(\phi [ \sigma ])$,
hence $\delta [ \sigma ] \epsilon [\sigma] \in E_\Delta(\psi [ \sigma ])$.

\begin{code}
Computable-Sub σ σ∶Γ⇒CΔ (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) validΔ = appP-E 
  (Computable-Sub σ σ∶Γ⇒CΔ Γ⊢δ∶φ⊃ψ validΔ) 
  (Computable-Sub σ σ∶Γ⇒CΔ Γ⊢ε∶φ validΔ) 
\end{code}

\item
$$ \infer{\Gamma \vdash \lambda x:A.M : A \rightarrow B}{\Gamma, x : A \vdash M : B}$$

\begin{enumerate}
\item[1]
\begin{code}
Computable-Sub {U} σ {Γ = Γ} {Δ = Δ} σ∶Γ⇒CΔ (ΛR {A = A} {M} {B} Γ,A⊢M∶B) validΔ = EI
\end{code}
Typability is easy to check.

\begin{code}
  (ΛR (substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed (subC-typed σ∶Γ⇒CΔ)))) (
\end{code}
We must also check the following.
\begin{itemize}
\item
Let $\Theta \supseteq \Delta$ and $N \in E_\Theta(A)$.  We must show that $(\lambda x:A.M[\sigma])N \in E_\Theta(B)$.
\begin{code}
  (λ {W} Θ {ρ} {N} ρ∶Δ⇒RΘ Θ⊢N∶A computeN → 
\end{code}

We have that $(\sigma, x:=N) : (\Gamma, x : A) \rightarrow \Theta$ is computable, 
\begin{code}
  let σN∶ΓA⇒CΘ : extendSub (ρ •RS σ) N ∶ Γ ,T A ⇒C Θ
      σN∶ΓA⇒CΘ = extendSubC (•RSC ρ∶Δ⇒RΘ σ∶Γ⇒CΔ) (EI Θ⊢N∶A computeN) in
\end{code}
and so the induction hypothesis gives
$M[\sigma, x:=N] \in E_\Theta(B)$.
\begin{code}
  let EΘMN : E Θ (ty B) (M ⟦ extendSub (ρ •RS σ) N ⟧)
      EΘMN = Computable-Sub (extendSub (ρ •RS σ) N) σN∶ΓA⇒CΘ Γ,A⊢M∶B (context-validity Θ⊢N∶A) in 
\end{code}
The result follows by Lemma \ref{lm:wte}.\ref{lm:wteT}.
\begin{code}
  E.computable (wteT 
    (weakening {ρ = liftRep _ ρ} {M = M ⟦ liftSub _ σ ⟧} 
      (substitution {σ = liftSub _ σ} {M = M} Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed (subC-typed σ∶Γ⇒CΔ))) 
      (ctxTR (context-validity Θ⊢N∶A)) (liftRep-typed ρ∶Δ⇒RΘ))
    (EI Θ⊢N∶A computeN) 
    (subst (E Θ (ty B)) 
      (let open ≡-Reasoning in 
      begin
        M ⟦ extendSub (ρ •RS σ) N ⟧
      ≡⟨ extendSub-decomp M ⟩
        M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧
      ≡⟨ sub-congl (liftSub-compRS M) ⟩
        M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= N ⟧
      ∎) 
    EΘMN)))
\end{code}
\item
\begin{code}
  ,p 
\end{code}
We must show that $\triplelambda e:x =_A y. M [ \sigma ] \{ x := e : x \sim y \} \equiv
\triplelambda e:x =_A y. M \{ z_1 := \sigma(z_1) \{ \}, \ldots, z_n := \sigma(z_n)\{\}, x := e \} \in E_\Delta(\lambda x:A.M[\sigma] =_{A \rightarrow B} \lambda x:A.M[\sigma])$.

So let $\Theta \supseteq \Delta$ and $N, N' \in E_\Theta(A)$, $P \in E_\Theta(N =_A N')$.
\begin{code}
  (λ {W} Θ {ρ} {N} {N'} {P} ρ∶Δ⇒RΘ Θ⊢P∶N≡N' computeN computeN' computeP → 
  let validΘ : valid Θ
      validΘ = context-validity Θ⊢P∶N≡N' in
  let validΘA : valid (Θ ,T A)
      validΘA = ctxTR validΘ in
  let Θ⊢N∶A : Θ ⊢ N ∶ ty A
      Θ⊢N∶A = equation-validity₁ Θ⊢P∶N≡N' in
  let Θ⊢N'∶A : Θ ⊢ N' ∶ ty A
      Θ⊢N'∶A = equation-validity₂ Θ⊢P∶N≡N' in
\end{code}
Then $(z_1 := \sigma(z_1)\{\}, \ldots, z_n := \sigma(z_n)\{\}, x := P) : (\sigma, x:=N) \sim (\sigma, x:=N') : (\Gamma, x:A) \rightarrow \Theta$
is computable,
\begin{code}
  let ρσC : ρ •RS σ ∶ Γ ⇒C Θ
      ρσC = •RSC ρ∶Δ⇒RΘ σ∶Γ⇒CΔ in
  let ΘA⊢Mρσ∶B : Θ ,T A ⊢ M ⟦ liftSub _ (ρ •RS σ) ⟧ ∶ ty B
      ΘA⊢Mρσ∶B = substitution Γ,A⊢M∶B validΘA (liftSub-typed (subC-typed ρσC)) in
  let pathρσC : toPath (ρ •RS σ) ∶ ρ •RS σ ∼ ρ •RS σ ∶ Γ ⇒C Θ
      pathρσC = toPathC ρσC in
  let σ₁ : Sub (U , -Term) W
      σ₁ = extendSub (ρ •RS σ) N in
  let σ₂ : Sub (U , -Term) W
      σ₂ = extendSub (ρ •RS σ) N' in
  let τ : PathSub (U , -Term) W
      τ = extendPS (toPath (ρ •RS σ)) P in
  let σP∶σN∼σN' : τ ∶ σ₁ ∼ σ₂ ∶ Γ ,T A ⇒C Θ
      σP∶σN∼σN' = extendPSC pathρσC (EI Θ⊢P∶N≡N' computeP) in 
\end{code}
 and so the induction hypothesis gives
\[ M \{ z_i := \sigma(z_i) \{\}, x := P \} \in E_\Theta(M [ \sigma, x:=N] =_B M [\sigma, x:=N']) \enspace . \]
\begin{code}
  let MP∈EΘMN≡MN' : E Θ (M ⟦ σ₁ ⟧ ≡〈 B 〉 M ⟦ σ₂ ⟧) (M ⟦⟦ τ ∶ σ₁ ∼ σ₂ ⟧⟧)
      MP∈EΘMN≡MN' = computable-path-substitution τ (extendSubC ρσC (EI Θ⊢N∶A computeN)) (extendSubC ρσC (EI (equation-validity₂ Θ⊢P∶N≡N') computeN')) (extendPSC pathρσC (EI Θ⊢P∶N≡N' computeP)) Γ,A⊢M∶B validΘ in
\end{code}
that is,
\[ M [ \sigma ] \{ x := P : N \sim N' \} \in E_\Theta(M [ \sigma, x:=N] =_B M [\sigma, x:=N']) \enspace . \]
\begin{code}
  let MP∈EΘMN≡MN'₂ : E Θ (M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧ ≡〈 B 〉 M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= N' ⟧) (M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦⟦ x₀::= P ∶ x₀:= N ∼ x₀:= N' ⟧⟧)
      MP∈EΘMN≡MN'₂ = subst₃ (λ a b c → E Θ (a ≡〈 B 〉 b) c) (extendSub-decomp M) (extendSub-decomp M) (extendPS-decomp {M = M}) MP∈EΘMN≡MN' in 
\end{code}
Therefore, by Lemma \ref{lm:wte}.\ref{lm:wteE'},
\[ \reff{\lambda x:A.M[\sigma]}_{N N'} P \in E_\Theta(M [ \sigma, x:=N] =_B M [\sigma, x:=N']) \]
\begin{code}
  let ΛMP∈EΘMN≡MN' : E Θ (M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧ ≡〈 B 〉 M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= N' ⟧) (app* N N' (reff (ΛT A M ⟦ ρ •RS σ ⟧)) P)
      ΛMP∈EΘMN≡MN' = wteE' ΘA⊢Mρσ∶B (EI Θ⊢N∶A computeN) (EI Θ⊢N'∶A computeN') (EI Θ⊢P∶N≡N' computeP) MP∈EΘMN≡MN'₂ in 
  let ΛMP∈EΘMN≡MN'₂ : E Θ (M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧ ≡〈 B 〉 M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= N' ⟧) (app* N N' (reff (ΛT A M ⟦ σ ⟧ 〈 ρ 〉)) P)
      ΛMP∈EΘMN≡MN'₂ = subst (λ x → E Θ (M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧ ≡〈 B 〉 M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= N' ⟧) (app* N N' (reff (ΛT A x)) P)) (liftSub-compRS M)
        ΛMP∈EΘMN≡MN' in
\end{code}
and so
\[ \reff{\lambda x:A.M[\sigma]}_{N N'} P \in E_\Theta(M [ (\lambda x:A.M[\sigma]) N =_B (\lambda x:A.M [\sigma]) N') \]
by Lemma \ref{lm:conv-compute}.
\begin{code}
  let Mρσt : ∀ t → Θ ⊢ t ∶ ty A → Θ ⊢ M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= t ⟧ ∶ ty B
      Mρσt _ Θ⊢t∶A = substitution ΘA⊢Mρσ∶B validΘ (botsub-typed Θ⊢t∶A) in
  let ΛMρσt : ∀ t → Θ ⊢ t ∶ ty A → Θ ⊢ appT (ΛT A M ⟦ σ ⟧ 〈 ρ 〉) t ∶ ty B
      ΛMρσt _ Θ⊢t∶A = appR (ΛR (subst (λ x → Θ ,T A ⊢ x ∶ ty B) (liftSub-compRS M) ΘA⊢Mρσ∶B)) Θ⊢t∶A in
  let βM : ∀ t → M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= t ⟧ ≃ appT (ΛT A M ⟦ σ ⟧ 〈 ρ 〉) t
      βM t = let open EqReasoning (CONV W -Expression (varKind -Term)) in 
        begin
          M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= t ⟧
        ≈⟨⟨ inc (redex (βR βT)) ⟩⟩
          appT (ΛT A M ⟦ ρ •RS σ ⟧) t
        ≡⟨ cong (λ x → appT (ΛT A x) t) (liftSub-compRS M) ⟩
          appT (ΛT A M ⟦ σ ⟧ 〈 ρ 〉) t
        ∎ in
  conv-computeE (E.computable ΛMP∈EΘMN≡MN'₂) (Mρσt N Θ⊢N∶A) (Mρσt N' Θ⊢N'∶A) (ΛMρσt N Θ⊢N∶A) (ΛMρσt N' Θ⊢N'∶A) 
    (βM N) (βM N')))
\end{code}
\end{itemize}
\item[4]
Let $\Theta \supseteq \Delta$ and $N, N' \in E_\Theta(A)$, $P \in E_\Theta(N =_A N')$.  Then $(\tau, x:=P) : (\rho, x:=N) \sim (\sigma, x:=N') : (\Gamma, x :A) \rightarrow \Delta$ is computable,
and so the induction hypothesis gives
\[ M \{ \tau, x := P \} \in E_\Theta(M[\rho, x:=N] =_B M[\sigma, x:=N']) \enspace . \]
By Lemma \ref{lm:conv-compute},
\[ M \{ \tau, x := P \} \in E_\Theta((\lambda x:A.M[\rho]) N =_B (\lambda x:A.M[\sigma]) N') \]
and so Lemma \ref{lm:wte}.\ref{lm:wteE} gives
\[ (\triplelambda e:x=_A y.M \{ \tau, x:=e \})_{N N'} P \in E_\Theta((\lambda x:A.M[\rho]) N =_B (\lambda x:A.M[\sigma]) N') \]
as required.
\end{enumerate}
\item
$$\infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \supset \psi}{\Gamma, p : \phi \vdash \delta : \psi}$$

\begin{code}
Computable-Sub σ {Γ} σ∶Γ⇒CΔ (ΛPR {δ = δ} {φ = φ} {ψ = ψ} Γ⊢φ∶Ω Γ⊢ψ∶Ω Γ,φ⊢δ∶ψ) validΔ = EI 
  (substitution (ΛPR Γ⊢φ∶Ω Γ⊢ψ∶Ω Γ,φ⊢δ∶ψ) validΔ (subC-typed σ∶Γ⇒CΔ)) 
  (let MeanTermI S φ' φ↠φ' = E-MeanTerm (Computable-Sub σ σ∶Γ⇒CΔ Γ⊢φ∶Ω validΔ) in 
  let MeanTermI T ψ' ψ↠ψ' = E-MeanTerm (Computable-Sub σ σ∶Γ⇒CΔ Γ⊢ψ∶Ω validΔ) in 
  S imp T ,p φ' imp ψ' ,p ⊃-red φ↠φ' ψ↠ψ' ,p 
\end{code}

Let $\Theta \supseteq \Delta$ and $\epsilon \in E_\Theta(\phi[\sigma])$.
\begin{code}
  (λ {W} Θ {ρ} {ε} ρ∶Δ⇒RΘ Θ⊢ε∶φ computeε →
\end{code}
  Then $(\sigma, p:=\epsilon) : (\Gamma, p : \phi) \rightarrow \Theta$
is computable,
\begin{code}
  let validΘ : valid Θ
      validΘ = context-validity Θ⊢ε∶φ in
  let φσρ↠φ'ρ : φ ⟦ σ ⟧ 〈 ρ 〉 ↠ decode-Meaning (nfrep φ' ρ)
      φσρ↠φ'ρ = let open PreorderReasoning (RED W -Expression (varKind -Term)) in begin
              φ ⟦ σ ⟧ 〈 ρ 〉
            ∼⟨ apredr REP R-respects-rep (MeanTerm.red (E-MeanTerm (Computable-Sub σ σ∶Γ⇒CΔ Γ⊢φ∶Ω validΔ))) ⟩
              (decode-Meaning φ') 〈 ρ 〉
            ≈⟨⟨ decode-Meaning-rep φ' {ρ} ⟩⟩
              decode-Meaning (nfrep φ' ρ)
            ∎ in
  let φρσ↠φ'ρ : φ ⟦ ρ •RS σ ⟧ ↠ decode-Meaning (nfrep φ' ρ)
      φρσ↠φ'ρ = subst (λ x → x ↠ decode-Meaning (nfrep φ' ρ)) (Prelims.sym (sub-compRS φ)) φσρ↠φ'ρ in
  let σε∶Γφ⇒CΘ : extendSub (ρ •RS σ) ε ∶ Γ ,P φ ⇒C Θ
      σε∶Γφ⇒CΘ = extendSubC (•RSC ρ∶Δ⇒RΘ σ∶Γ⇒CΔ) (EI 
        (convR Θ⊢ε∶φ (substitution Γ⊢φ∶Ω (context-validity Θ⊢ε∶φ) (•RS-typed ρ∶Δ⇒RΘ (subC-typed σ∶Γ⇒CΔ))) 
          (RSTClose.sym (RT-sub-RST φρσ↠φ'ρ)))
          (S ,p nfrep φ' ρ ,p φρσ↠φ'ρ ,p computeε)) in
\end{code}
 and so the induction hypothesis gives
\[ \delta[\sigma, p:=\epsilon] \in E_\Theta(\psi[\sigma)) \enspace . \]
\begin{code}
  let EΘψδ : E Θ (ψ ⟦ ρ •RS σ ⟧) (δ ⟦ extendSub (ρ •RS σ) ε ⟧)
      EΘψδ = subst (λ x → E Θ x (δ ⟦ extendSub (ρ •RS σ) ε ⟧)) (extendSub-upRep {E = ψ})
        (Computable-Sub (extendSub (ρ •RS σ) ε) σε∶Γφ⇒CΘ Γ,φ⊢δ∶ψ (context-validity Θ⊢ε∶φ)) in
\end{code}
Hence by Lemma \ref{lm:wte}.\ref{lm:wteP}, we have $(\lambda p:\phi[\sigma].\delta[\sigma]) \epsilon \in E_\Theta(\psi[\sigma])$, as required.
\begin{code}
  let ρσ∶Γ⇒Θ : ρ •RS σ ∶ Γ ⇒ Θ
      ρσ∶Γ⇒Θ = •RS-typed ρ∶Δ⇒RΘ (subC-typed σ∶Γ⇒CΔ) in
  let EΘψΛφδ : E Θ (ψ ⟦ ρ •RS σ ⟧) (appP (ΛP φ δ ⟦ σ ⟧ 〈 ρ 〉) ε)
      EΘψΛφδ = wteP 
        (subst₃ (λ x y z → Θ ,P x ⊢ y ∶ z) (sub-compRS φ) (liftSub-compRS δ) (liftSub-upRep ψ) 
          (substitution Γ,φ⊢δ∶ψ (ctxPR (substitution Γ⊢φ∶Ω validΘ ρσ∶Γ⇒Θ)) (liftSub-typed ρσ∶Γ⇒Θ)))
        (EI 
        (convR Θ⊢ε∶φ (weakening (substitution Γ⊢φ∶Ω validΔ (subC-typed σ∶Γ⇒CΔ)) validΘ ρ∶Δ⇒RΘ) (RSTClose.sym (RT-sub-RST φσρ↠φ'ρ)))
        (S ,p nfrep φ' ρ ,p φσρ↠φ'ρ ,p computeε)) (subst (E Θ (ψ ⟦ ρ •RS σ ⟧)) 
        (let open ≡-Reasoning in begin
          δ ⟦ extendSub (ρ •RS σ) ε ⟧
        ≡⟨ extendSub-decomp δ ⟩
          δ ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= ε ⟧
        ≡⟨ sub-congl (liftSub-compRS δ) ⟩
          δ ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= ε ⟧
        ∎) 
        EΘψδ) in 
  let S'' ,p ψ'' ,p ψ↠ψ'' ,p ψ''computable = E.computable EΘψΛφδ in 
  {!conv-computeP {Γ = Θ} {L = ψ''} {M = nfrep ψ' ρ} !}))
\end{code}

\AgdaHide{
\begin{code}
Computable-Sub σ σ∶Γ⇒CΔ (convR Γ⊢M∶A Γ⊢M∶A₁ x) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒CΔ (refR Γ⊢M∶A) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒CΔ (⊃*R Γ⊢M∶A Γ⊢M∶A₁) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒CΔ (univR Γ⊢M∶A Γ⊢M∶A₁) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒CΔ (plusR Γ⊢M∶A) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒CΔ (minusR Γ⊢M∶A) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒CΔ (lllR Γ⊢M∶A) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒CΔ (app*R Γ⊢M∶A Γ⊢M∶A₁ Γ⊢M∶A₂ Γ⊢M∶A₃) validΔ = {!!}
Computable-Sub σ σ∶Γ⇒CΔ (convER Γ⊢M∶A Γ⊢M∶A₁ Γ⊢M∶A₂ M≃M' N≃N') validΔ = {!!}

{- computable-path-substitution τ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (varR x validΓ) validΔ = τ∶σ∼σ' x
computable-path-substitution τ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (appR Γ⊢M∶A⇛B Γ⊢N∶A) validΔ = 
  app*-E 
    (computable-path-substitution τ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢M∶A⇛B validΔ) 
    (computable-path-substitution τ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢N∶A validΔ) 
    (Computable-Sub _ σ∶Γ⇒CΔ Γ⊢N∶A validΔ) 
    (Computable-Sub _ σ'∶Γ⇒CΔ Γ⊢N∶A validΔ)
computable-path-substitution τ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (ΛR Γ⊢M∶A) validΔ = {!!}
computable-path-substitution τ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (⊥R validΓ) validΔ = {!!}
computable-path-substitution τ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (⊃R Γ⊢M∶A Γ⊢M∶A₁) validΔ = {!!} -}

{- Computable-Sub σ σ∶Γ⇒Δ (varR x validΓ) validΔ _ = σ∶Γ⇒Δ x
Computable-Sub {V = V} σ {Δ = Δ} σ∶Γ⇒Δ (appR Γ⊢M∶A⇛B Γ⊢N∶A) validΔ _ = 
  appT-E validΔ (Computable-Sub σ σ∶Γ⇒Δ Γ⊢M∶A⇛B validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢N∶A validΔ)
Computable-Sub σ σ∶Γ⇒Δ (ΛR {M = M} {B} Γ,A⊢M∶B) validΔ = 
  func-E (λ _ Θ ρ N validΘ ρ∶Δ⇒Θ N∈EΘA → 
    let MN∈EΘB = subst (E Θ B) (subrepsub M)
                 (Computable-Sub (x₀:= N •SR liftRep _ ρ • liftSub -Term σ) 
                 (compC (compSRC (botsubC N∈EΘA) 
                        (liftRep-typed ρ∶Δ⇒Θ)) 
                 (liftSubC σ∶Γ⇒Δ)) 
                 Γ,A⊢M∶B validΘ) in
    expand-E MN∈EΘB
      (appR (ΛR (weakening (substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed (subC-typed σ∶Γ⇒Δ))) 
                                                      (ctxTR validΘ) 
                                         (liftRep-typed ρ∶Δ⇒Θ))) 
                (E-typed N∈EΘA)) 
      (βTkr (SNap' {Ops = SUB} R-respects-sub (E-SN B MN∈EΘB))))
Computable-Sub σ σ∶Γ⇒Δ (⊥R _) validΔ = ⊥-E validΔ
Computable-Sub σ σ∶Γ⇒Δ (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = ⊃-E 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢φ∶Ω validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ψ∶Ω validΔ)
Computable-Sub σ σ∶Γ⇒Δ (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) validΔ = appP-EP 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢δ∶φ⊃ψ validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ε∶φ validΔ)
Computable-Sub σ {Γ = Γ} {Δ = Δ} σ∶Γ⇒Δ (ΛPR {δ = δ} {φ} {ψ} Γ⊢φ∶Ω Γ,φ⊢δ∶ψ) validΔ = 
  let Δ⊢Λφδσ∶φ⊃ψ : Δ ⊢ (ΛP φ δ) ⟦ σ ⟧ ∶ φ ⟦ σ ⟧ ⊃ ψ ⟦ σ ⟧
      Δ⊢Λφδσ∶φ⊃ψ = substitution {A = φ ⊃ ψ} (ΛPR Γ⊢φ∶Ω Γ,φ⊢δ∶ψ) validΔ (subC-typed σ∶Γ⇒Δ) in
  func-EP (λ W Θ ρ ε ρ∶Δ⇒Θ ε∈EΔφ → 
    let δε∈EΘψ : EP Θ (ψ ⟦ σ ⟧ 〈 ρ 〉) (δ ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= ε ⟧)
        δε∈EΘψ = subst₂ (EP Θ) (subrepbotsub-up ψ) (subrepsub δ) 
                 (Computable-Sub (x₀:= ε •SR liftRep _ ρ • liftSub _ σ) 
                 (compC (compSRC (botsubCP ε∈EΔφ) 
                        (liftRep-typed ρ∶Δ⇒Θ)) 
                (liftSubC σ∶Γ⇒Δ)) Γ,φ⊢δ∶ψ (context-validity (EP-typed ε∈EΔφ))) in
    expand-EP δε∈EΘψ (appPR (weakening Δ⊢Λφδσ∶φ⊃ψ (context-validity (EP-typed ε∈EΔφ)) ρ∶Δ⇒Θ) (EP-typed ε∈EΔφ)) (βR-exp {!!} (EP-SN ε∈EΔφ) (EP-SN δε∈EΘψ))
      (βPkr (SNrep R-creates-rep (E-SN Ω (Computable-Sub σ σ∶Γ⇒Δ Γ⊢φ∶Ω validΔ))) (EP-SN ε∈EΔφ)))
  Δ⊢Λφδσ∶φ⊃ψ
Computable-Sub σ σ∶Γ⇒Δ (convR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ) validΔ = conv-E (respects-conv (respects-osr SUB R-respects-sub) φ≃ψ) 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢δ∶φ validΔ) (ctxPR (substitution Γ⊢ψ∶Ω validΔ (subC-typed σ∶Γ⇒Δ)))
Computable-Sub σ σ∶Γ⇒Δ (refR Γ⊢M∶A) validΔ = ref-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢M∶A validΔ)
Computable-Sub σ σ∶Γ⇒Δ (⊃*R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = ⊃*-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢φ∶Ω validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ψ∶Ω validΔ)
Computable-Sub σ σ∶Γ⇒Δ (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) validΔ = univ-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢δ∶φ⊃ψ validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢ε∶ψ⊃φ validΔ)
Computable-Sub σ σ∶Γ⇒Δ (plusR Γ⊢P∶φ≡ψ) validΔ = plus-EP (Computable-Sub σ σ∶Γ⇒Δ Γ⊢P∶φ≡ψ validΔ)
Computable-Sub σ σ∶Γ⇒Δ (minusR Γ⊢P∶φ≡ψ) validΔ = minus-EP (Computable-Sub σ σ∶Γ⇒Δ Γ⊢P∶φ≡ψ validΔ)
Computable-Sub σ {Δ = Δ} σ∶Γ⇒Δ (lllR {A = A} {B = B} {M = M} {N = N} {P = P} ΓAAe⊢P∶Mx≡Ny) validΔ = 
   let validΔAA : valid (Δ ,T A ,T A)
       validΔAA = ctxTR (ctxTR validΔ) in
   let ΔAAE⊢P∶Mx≡Ny : addpath Δ A ⊢ P ⟦ liftSub -Path (liftSub -Term (liftSub -Term σ)) ⟧ ∶ appT (M ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT (N ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₁)
       ΔAAE⊢P∶Mx≡Ny = change-type 
                      (substitution ΓAAe⊢P∶Mx≡Ny (valid-addpath validΔ) 
                        (liftSub-typed (liftSub-typed (liftSub-typed (subC-typed σ∶Γ⇒Δ))))) 
                      (cong₂ (λ x y → appT x (var x₂) ≡〈 B 〉 appT y (var x₁)) (liftSub-upRep₃ M) (liftSub-upRep₃ N)) in
   func-EE 
   (lllR ΔAAE⊢P∶Mx≡Ny)
   (λ V Θ L L' Q ρ ρ∶Δ⇒RΘ L∈EΘA L'∈EΘA Q∈EΘL≡L' → 
     let validΘ : valid Θ
         validΘ = context-validity (E.typed L∈EΘA) in
     let liftRepρ∶apΔ⇒RapΘ : liftRep _ (liftRep _ (liftRep _ ρ)) ∶ addpath Δ A ⇒R addpath Θ A
         liftRepρ∶apΔ⇒RapΘ = liftRep-typed (liftRep-typed (liftRep-typed ρ∶Δ⇒RΘ)) in --TODO General lemma
     expand-EE 
       (subst₂ (EE Θ) 
         (cong₂ (λ x y → appT x L ≡〈 B 〉 appT y L') 
           (let open ≡-Reasoning in 
           begin
             M ⇑ ⇑ ⇑ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR liftRep -Path (liftRep -Term (liftRep -Term ρ)) • liftSub -Path (liftSub -Term (liftSub -Term σ)) ⟧
           ≡⟨ sub-comp (M ⇑ ⇑ ⇑) ⟩
             M ⇑ ⇑ ⇑ ⟦ liftSub -Path (liftSub -Term (liftSub -Term σ)) ⟧ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR liftRep -Path (liftRep -Term (liftRep -Term ρ)) ⟧
           ≡⟨ sub-congl (liftSub-upRep₃ M) ⟩
             M ⟦ σ ⟧ ⇑ ⇑ ⇑ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR liftRep -Path (liftRep -Term (liftRep -Term ρ)) ⟧
           ≡⟨ sub-compSR (M ⟦ σ ⟧ ⇑ ⇑ ⇑) ⟩
             M ⟦ σ ⟧ ⇑ ⇑ ⇑ 〈 liftRep -Path (liftRep -Term (liftRep -Term ρ)) 〉 ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧
           ≡⟨ sub-congl (liftRep-upRep₃ (M ⟦ σ ⟧)) ⟩
             M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧
           ≡⟨ botSub-upRep₃ ⟩
             M ⟦ σ ⟧ 〈 ρ 〉
           ∎) 
           (let open ≡-Reasoning in 
           begin
             N ⇑ ⇑ ⇑ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR liftRep -Path (liftRep -Term (liftRep -Term ρ)) • liftSub -Path (liftSub -Term (liftSub -Term σ)) ⟧
           ≡⟨ sub-comp (N ⇑ ⇑ ⇑) ⟩
             N ⇑ ⇑ ⇑ ⟦ liftSub -Path (liftSub -Term (liftSub -Term σ)) ⟧ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR liftRep -Path (liftRep -Term (liftRep -Term ρ)) ⟧
           ≡⟨ sub-congl (liftSub-upRep₃ N) ⟩
             N ⟦ σ ⟧ ⇑ ⇑ ⇑ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR liftRep -Path (liftRep -Term (liftRep -Term ρ)) ⟧
           ≡⟨ sub-compSR (N ⟦ σ ⟧ ⇑ ⇑ ⇑) ⟩
             N ⟦ σ ⟧ ⇑ ⇑ ⇑ 〈 liftRep -Path (liftRep -Term (liftRep -Term ρ)) 〉 ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧
           ≡⟨ sub-congl (liftRep-upRep₃ (N ⟦ σ ⟧)) ⟩
             N ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧
           ≡⟨ botSub-upRep₃ ⟩
             N ⟦ σ ⟧ 〈 ρ 〉
           ∎)) --TODO Common pattern
           (let open ≡-Reasoning in 
           begin
             P ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR liftRep -Path (liftRep -Term (liftRep -Term ρ)) • liftSub -Path (liftSub -Term (liftSub -Term σ)) ⟧
           ≡⟨ sub-comp P ⟩
             P ⟦ liftSub -Path (liftSub -Term (liftSub -Term σ)) ⟧ ⟦ (x₂:= L ,x₁:= L' ,x₀:= Q) •SR liftRep -Path (liftRep -Term (liftRep -Term ρ)) ⟧
           ≡⟨ sub-compSR (P ⟦ liftSub -Path (liftSub -Term (liftSub -Term σ)) ⟧) ⟩
             P ⟦ liftSub -Path (liftSub -Term (liftSub -Term σ)) ⟧ 〈 liftRep -Path (liftRep -Term (liftRep -Term ρ)) 〉 ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧
           ∎) 
         (Computable-Sub 
           ((x₂:= L ,x₁:= L' ,x₀:= Q) •SR 
             liftRep -Path (liftRep -Term (liftRep -Term ρ)) • 
             liftSub -Path (liftSub -Term (liftSub -Term σ))) 
           (compC (compSRC 
                  (botsub₃C L∈EΘA L'∈EΘA Q∈EΘL≡L') 
                  liftRepρ∶apΔ⇒RapΘ)
           (liftSubC (liftSubC (liftSubC σ∶Γ⇒Δ)))) 
           ΓAAe⊢P∶Mx≡Ny 
           validΘ))
       (app*R (E-typed L∈EΘA) (E-typed L'∈EΘA) 
         (lllR (change-type (weakening ΔAAE⊢P∶Mx≡Ny (valid-addpath validΘ) 
           liftRepρ∶apΔ⇒RapΘ) 
         (cong₂ (λ x y → appT x (var x₂) ≡〈 B 〉 appT y (var x₁)) 
           (liftRep-upRep₃ (M ⟦ σ ⟧)) (liftRep-upRep₃ (N ⟦ σ ⟧)))))
         (EE-typed Q∈EΘL≡L')) 
       (βEkr (E-SN L∈EΘA) (E-SN L'∈EΘA) (E-SN Q∈EΘL≡L')))
Computable-Sub σ σ∶Γ⇒Δ (app*R Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') validΔ = 
  app*-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢P∶M≡M' validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢Q∶N≡N' validΔ) 
  (Computable-Sub σ σ∶Γ⇒Δ Γ⊢N∶A validΔ) (Computable-Sub σ σ∶Γ⇒Δ Γ⊢N'∶A validΔ)
Computable-Sub σ σ∶Γ⇒Δ (convER Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') validΔ = 
  conv-EE (Computable-Sub σ σ∶Γ⇒Δ Γ⊢P∶M≡N validΔ) 
    (conv-sub M≃M') (conv-sub N≃N') 
    (substitution Γ⊢M'∶A validΔ (subC-typed σ∶Γ⇒Δ)) (substitution Γ⊢N'∶A validΔ (subC-typed σ∶Γ⇒Δ))
--TODO Common pattern

--TODO Rename
computable-path-substitution U V τ σ σ' Γ Δ .(var x) ._ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (varR x _) _ = 
  τ∶σ∼σ' x
computable-path-substitution U V τ σ σ' Γ Δ .(app -bot out) .(ty Ω) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (⊥R x) validΔ = ref-EE (⊥-E validΔ)
computable-path-substitution U V τ σ σ' Γ Δ _ .(ty Ω) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ = ⊃*-EE 
  (computable-path-substitution U V τ σ σ' Γ Δ _ (ty Ω) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢φ∶Ω validΔ) 
  (computable-path-substitution U V τ σ σ' Γ Δ _ (ty Ω) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢ψ∶Ω validΔ) 
computable-path-substitution U V τ σ σ' Γ Δ _ .(ty B) σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (appR {N = N} {A} {B} Γ⊢M∶A⇒B Γ⊢N∶A) validΔ = 
  app*-EE 
  (computable-path-substitution U V τ σ σ' Γ Δ _ _ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢M∶A⇒B validΔ) 
  (computable-path-substitution U V τ σ σ' Γ Δ _ _ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' Γ⊢N∶A validΔ)
  (Computable-Sub σ (pathsubC-valid₁ {U} {V} {τ} {σ} {σ'} τ∶σ∼σ') Γ⊢N∶A validΔ)
  (Computable-Sub σ' (pathsubC-valid₂ {τ = τ} {σ} {σ = σ'} {Γ} {Δ} τ∶σ∼σ') Γ⊢N∶A validΔ)
computable-path-substitution U V τ σ σ' Γ Δ ._ ._ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (ΛR {A = A} {M = M} {B = B} Γ,A⊢M∶B) validΔ = 
  let validΔA : valid (Δ ,T A)
      validΔA = ctxTR validΔ in
  let validΔAA : valid (Δ ,T A ,T A)
      validΔAA = ctxTR validΔA in
  let validapΔ : valid (addpath Δ A)
      validapΔ = valid-addpath validΔ in
  let σ∶Γ⇒Δ : σ ∶ Γ ⇒ Δ
      σ∶Γ⇒Δ = subC-typed σ∶Γ⇒CΔ in
  let σ'∶Γ⇒Δ : σ' ∶ Γ ⇒ Δ
      σ'∶Γ⇒Δ = subC-typed σ'∶Γ⇒CΔ in
  let σ↑∶ΓA⇒ΔA : liftSub -Term σ ∶ Γ ,T A ⇒ Δ ,T A
      σ↑∶ΓA⇒ΔA = liftSub-typed σ∶Γ⇒Δ in
  let σ'↑∶ΓA⇒ΔA : liftSub -Term σ' ∶ Γ ,T A ⇒ Δ ,T A
      σ'↑∶ΓA⇒ΔA = liftSub-typed σ'∶Γ⇒Δ in
  let ΔA⊢Mσ∶B : Δ ,T A ⊢ M ⟦ liftSub -Term σ ⟧ ∶ ty B
      ΔA⊢Mσ∶B = substitution Γ,A⊢M∶B validΔA σ↑∶ΓA⇒ΔA in
  let ΔA⊢Mσ'∶B : Δ ,T A ⊢ M ⟦ liftSub -Term σ' ⟧ ∶ ty B
      ΔA⊢Mσ'∶B = substitution Γ,A⊢M∶B validΔA σ'↑∶ΓA⇒ΔA in
  let τ↑∶σ↖∼σ'↗ : liftPathSub τ ∶ sub↖ σ ∼ sub↗ σ' ∶ Γ ,T A ⇒ addpath Δ A
      τ↑∶σ↖∼σ'↗ = liftPathSub-typed (pathsubC-typed σ σ' τ∶σ∼σ') validΔ in
  let σ↖∶ΓA⇒apΔ : sub↖ σ ∶ Γ ,T A ⇒ addpath Δ A
      σ↖∶ΓA⇒apΔ = sub↖-typed σ∶Γ⇒Δ in
  let σ'↗∶ΓA⇒apΔ : sub↗ σ' ∶ Γ ,T A ⇒ addpath Δ A
      σ'↗∶ΓA⇒apΔ = sub↗-typed σ'∶Γ⇒Δ in
  let Mτ∶Mσ∼Mσ' : addpath Δ A ⊢ M ⟦⟦ liftPathSub τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ ∶ M ⟦ sub↖ σ ⟧ ≡〈 B 〉 M ⟦ sub↗ σ' ⟧
      Mτ∶Mσ∼Mσ' = path-substitution Γ,A⊢M∶B τ↑∶σ↖∼σ'↗ σ↖∶ΓA⇒apΔ σ'↗∶ΓA⇒apΔ (valid-addpath validΔ) in
  func-EE 
  (lllR (convER Mτ∶Mσ∼Mσ'
    (appR 
      (ΛR (weakening (weakening (weakening ΔA⊢Mσ∶B
                                           validΔAA (liftRep-typed upRep-typed)) 
                                (ctxTR validΔAA) (liftRep-typed upRep-typed)) 
                     (ctxTR validapΔ) (liftRep-typed upRep-typed))) 
      (varR x₂ validapΔ))
    (appR (ΛR (weakening (weakening (weakening ΔA⊢Mσ'∶B
                                               validΔAA (liftRep-typed upRep-typed)) 
                                    (ctxTR validΔAA) (liftRep-typed upRep-typed)) 
                         (ctxTR validapΔ) (liftRep-typed upRep-typed))) 
              (varR x₁ validapΔ)) 
    (sym-conv (osr-conv (redex (subst
                                  (R -appTerm
                                   (ΛT A
                                    ((((M ⟦ liftSub -Term σ ⟧) 〈 liftRep -Term upRep 〉) 〈 liftRep -Term upRep 〉)
                                     〈 liftRep -Term upRep 〉)
                                    ,, var x₂ ,, out))
                                  (sub↖-decomp M) βT)))) 
    (sym-conv (osr-conv (redex (subst
                                  (R -appTerm
                                   (ΛT A
                                    ((((M ⟦ liftSub -Term σ' ⟧) 〈 liftRep -Term upRep 〉) 〈 liftRep -Term upRep
                                      〉)
                                     〈 liftRep -Term upRep 〉)
                                    ,, var x₁ ,, out))
                                  (sub↗-decomp M) βT)))))) 
   (λ W Θ N N' Q ρ ρ∶Δ⇒RΘ N∈EΘA N'∈EΘA Q∈EΘN≡N' → 
   let validΘ : valid Θ
       validΘ = context-validity (E.typed N∈EΘA) in
   let validΘA : valid (Θ ,T A)
       validΘA = ctxTR validΘ in
   let validΘAA : valid (Θ ,T A ,T A)
       validΘAA = ctxTR validΘA in
   let validapΘ : valid (addpath Θ A)
       validapΘ = valid-addpath validΘ in
   let ρ↑∶ΔA⇒ΘA : liftRep -Term ρ ∶ Δ ,T A ⇒R Θ ,T A
       ρ↑∶ΔA⇒ΘA = liftRep-typed ρ∶Δ⇒RΘ in
   let Θ⊢ΛM∶A⇛B : Θ ⊢ ΛT A (M ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term ρ 〉) ∶ ty (A ⇛ B)
       Θ⊢ΛM∶A⇛B = ΛR (weakening ΔA⊢Mσ∶B validΘA ρ↑∶ΔA⇒ΘA) in
   let Θ⊢N∶A : Θ ⊢ N ∶ ty A
       Θ⊢N∶A = E-typed N∈EΘA in
   let Θ⊢N'∶A : Θ ⊢ N' ∶ ty A
       Θ⊢N'∶A = E-typed N'∈EΘA in
   let ΘA⊢Mσ'∶B : Θ ,T A ⊢ M ⟦ liftSub -Term σ' ⟧ 〈 liftRep -Term ρ 〉 ∶ ty B
       ΘA⊢Mσ'∶B = weakening ΔA⊢Mσ'∶B validΘA ρ↑∶ΔA⇒ΘA in
   expand-EE (conv-EE
     (computable-path-substitution (U , -Term) W (extendPS (ρ •RP τ) Q) (extendSub (ρ •RS σ) N) (extendSub (ρ •RS σ') N') (Γ ,T A) Θ M (ty B) 
     (extendSubC (compRSC ρ∶Δ⇒RΘ σ∶Γ⇒CΔ) N∈EΘA) 
     (extendSubC (compRSC ρ∶Δ⇒RΘ σ'∶Γ⇒CΔ) N'∈EΘA) 
     (extendPSC (compRPC {σ = σ} {σ' = σ'} τ∶σ∼σ' ρ∶Δ⇒RΘ) Q∈EΘN≡N') Γ,A⊢M∶B validΘ)
     (sym-conv (osr-conv (redex 
       (subst
          (R -appTerm (ΛT A ((M ⟦ liftSub _ σ ⟧) 〈 liftRep _ ρ 〉) ,, N ,, out)) 
          (let open ≡-Reasoning in 
          begin
            M ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term ρ 〉 ⟦ x₀:= N ⟧
          ≡⟨⟨ sub-congl (sub-compRS M) ⟩⟩
            M ⟦ liftRep -Term ρ •RS liftSub -Term σ ⟧ ⟦ x₀:= N ⟧
          ≡⟨⟨ sub-congl (sub-congr liftSub-compRS M) ⟩⟩
            M ⟦ liftSub -Term (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧
          ≡⟨ extendSub-decomp M ⟩
            M ⟦ extendSub (ρ •RS σ) N ⟧
          ∎)
          βT)))) 
     (sym-conv (osr-conv (redex 
       (subst
          (R -appTerm (ΛT A ((M ⟦ liftSub _ σ' ⟧) 〈 liftRep _ ρ 〉) ,, N' ,, out)) 
          (let open ≡-Reasoning in 
          begin
            M ⟦ liftSub -Term σ' ⟧ 〈 liftRep -Term ρ 〉 ⟦ x₀:= N' ⟧
          ≡⟨⟨ sub-congl (sub-compRS M) ⟩⟩
            M ⟦ liftRep -Term ρ •RS liftSub -Term σ' ⟧ ⟦ x₀:= N' ⟧
          ≡⟨⟨ sub-congl (sub-congr liftSub-compRS M) ⟩⟩
            M ⟦ liftSub -Term (ρ •RS σ') ⟧ ⟦ x₀:= N' ⟧
          ≡⟨ extendSub-decomp M ⟩
            M ⟦ extendSub (ρ •RS σ') N' ⟧
          ∎)
          βT)))) 
     (appR Θ⊢ΛM∶A⇛B Θ⊢N∶A) 
     (appR (ΛR ΘA⊢Mσ'∶B) Θ⊢N'∶A)) 
     (app*R Θ⊢N∶A Θ⊢N'∶A (lllR (convER 
       (weakening Mτ∶Mσ∼Mσ' (valid-addpath validΘ) (liftRep-typed (liftRep-typed (liftRep-typed ρ∶Δ⇒RΘ)))) 
       (appR (weakening (weakening (weakening Θ⊢ΛM∶A⇛B validΘA upRep-typed) validΘAA upRep-typed) validapΘ upRep-typed) 
         (varR x₂ validapΘ)) 
       (appR (ΛR (weakening (weakening (weakening ΘA⊢Mσ'∶B validΘAA (liftRep-typed upRep-typed)) (ctxTR validΘAA) (liftRep-typed upRep-typed)) (ctxTR validapΘ) 
         (liftRep-typed upRep-typed))) (varR x₁ validapΘ)) 
       (sym-conv (subst (_≃_ (appT (ΛT A (M ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term ρ 〉) ⇑ ⇑ ⇑) (var x₂))) 
         (let open ≡-Reasoning in 
         begin
           M ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term ρ 〉 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 ⟦ x₀:= var x₂ ⟧
         ≡⟨⟨ sub-congl (rep-comp₄ (M ⟦ liftSub -Term σ ⟧)) ⟩⟩
           M ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep •R liftRep -Term upRep •R liftRep -Term upRep •R liftRep -Term ρ 〉 ⟦ x₀:= var x₂ ⟧
         ≡⟨⟨ sub-congl (rep-congr liftRep-comp₄ (M ⟦ liftSub -Term σ ⟧)) ⟩⟩
           M ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term (upRep •R upRep •R upRep •R ρ) 〉 ⟦ x₀:= var x₂ ⟧ 
         ≡⟨ sub-congl (rep-congr (liftRep-cong (liftRep-upRep₄' ρ)) (M ⟦ liftSub -Term σ ⟧)) ⟩
           M ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term (liftRep -Path (liftRep -Term (liftRep -Term ρ)) •R upRep •R upRep •R upRep) 〉 ⟦ x₀:= var x₂ ⟧ 
         ≡⟨ sub-congl (rep-congr liftRep-comp₄ (M ⟦ liftSub -Term σ ⟧) ) ⟩
           M ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term (liftRep -Path (liftRep -Term (liftRep -Term ρ))) •R liftRep -Term upRep •R liftRep -Term upRep •R liftRep -Term upRep 〉 ⟦ x₀:= var x₂ ⟧ 
         ≡⟨ sub-congl (rep-comp₄ (M ⟦ liftSub -Term σ ⟧)) ⟩
           M ⟦ liftSub -Term σ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep -Term (liftRep -Path (liftRep -Term (liftRep -Term ρ))) 〉 ⟦ x₀:= var x₂ ⟧
         ≡⟨⟨ compRS-botSub (M ⟦ liftSub -Term σ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉) ⟩⟩
           M ⟦ liftSub -Term σ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= var x₂ ⟧ 〈 liftRep -Path (liftRep -Term (liftRep -Term ρ)) 〉
         ≡⟨ rep-congl (sub↖-decomp M) ⟩
           M ⟦ sub↖ σ ⟧ 〈 liftRep -Path (liftRep -Term (liftRep -Term ρ)) 〉
         ∎) 
         (osr-conv (redex βT)))) 
         (sym-conv (subst (_≃_ (appT (ΛT A (M ⟦ liftSub -Term σ' ⟧ 〈 liftRep -Term ρ 〉) ⇑ ⇑ ⇑) (var x₁))) 
         (let open ≡-Reasoning in 
         begin
           M ⟦ liftSub -Term σ' ⟧ 〈 liftRep -Term ρ 〉 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 ⟦ x₀:= var x₁ ⟧
         ≡⟨⟨ sub-congl (rep-comp₄ (M ⟦ liftSub -Term σ' ⟧)) ⟩⟩
           M ⟦ liftSub -Term σ' ⟧ 〈 liftRep -Term upRep •R liftRep -Term upRep •R liftRep -Term upRep •R liftRep -Term ρ 〉 ⟦ x₀:= var x₁ ⟧
         ≡⟨⟨ sub-congl (rep-congr liftRep-comp₄ (M ⟦ liftSub -Term σ' ⟧)) ⟩⟩
           M ⟦ liftSub -Term σ' ⟧ 〈 liftRep -Term (upRep •R upRep •R upRep •R ρ) 〉 ⟦ x₀:= var x₁ ⟧ 
         ≡⟨ sub-congl (rep-congr (liftRep-cong (liftRep-upRep₄' ρ)) (M ⟦ liftSub -Term σ' ⟧)) ⟩
           M ⟦ liftSub -Term σ' ⟧ 〈 liftRep -Term (liftRep -Path (liftRep -Term (liftRep -Term ρ)) •R upRep •R upRep •R upRep) 〉 ⟦ x₀:= var x₁ ⟧ 
         ≡⟨ sub-congl (rep-congr liftRep-comp₄ (M ⟦ liftSub -Term σ' ⟧)) ⟩
           M ⟦ liftSub -Term σ' ⟧ 〈 liftRep -Term (liftRep -Path (liftRep -Term (liftRep -Term ρ))) •R liftRep -Term upRep •R liftRep -Term upRep •R liftRep -Term upRep 〉 ⟦ x₀:= var x₁ ⟧ 
         ≡⟨ sub-congl (rep-comp₄ (M ⟦ liftSub -Term σ' ⟧)) ⟩
           M ⟦ liftSub -Term σ' ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep -Term (liftRep -Path (liftRep -Term (liftRep -Term ρ))) 〉 ⟦ x₀:= var x₁ ⟧
         ≡⟨⟨ compRS-botSub (M ⟦ liftSub -Term σ' ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉) ⟩⟩
           M ⟦ liftSub -Term σ' ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= var x₁ ⟧ 〈 liftRep -Path (liftRep -Term (liftRep -Term ρ)) 〉
         ≡⟨ rep-congl (sub↗-decomp M) ⟩
           M ⟦ sub↗ σ' ⟧ 〈 liftRep -Path (liftRep -Term (liftRep -Term ρ)) 〉
         ∎) 
         (osr-conv (redex βT)))))) --TODO Duplication
         (EE-typed Q∈EΘN≡N')) 
     (subst (key-redex _) 
     (let open ≡-Reasoning in 
     begin
       M ⟦⟦ liftPathSub τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ 〈 liftRep -Path (liftRep -Term (liftRep -Term ρ)) 〉 ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ≡⟨⟨ sub-congl (pathsub-compRP M) ⟩⟩
       M ⟦⟦ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RP liftPathSub τ ∶ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↖ σ ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↗ σ' ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ≡⟨⟨ sub-congl (pathsub-cong M liftPathSub-compRP sub↖-compRP sub↗-compRP) ⟩⟩
       M ⟦⟦ liftPathSub (ρ •RP τ) ∶ sub↖ (ρ •RS σ) ∼ sub↗ (ρ •RS σ') ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ≡⟨⟨ pathsub-extendPS M ⟩⟩
       M ⟦⟦ extendPS (ρ •RP τ) Q ∶ extendSub (ρ •RS σ) N ∼ extendSub (ρ •RS σ') N' ⟧⟧
     ∎) (βEkr (E-SN N∈EΘA) (E-SN N'∈EΘA) (E-SN Q∈EΘN≡N')))) -}
\end{code}
}

\item
$$ \infer[(\phi \simeq \psi)]{\Gamma \vdash \delta : \psi}{\Gamma \vdash \delta : \phi \quad \Gamma \vdash \psi : \Omega} $$

We have that $\delta[\sigma] \in E_\Gamma(\phi[\sigma])$ by induction hypothesis, and so $\delta[\sigma] \in E_\Gamma(\psi[\sigma])$ by
Lemma \ref{lm:conv-compute}.
\item
$$ \infer[(e : M =_A N \in \Gamma)]{\Gamma \vdash e : M =_A N}{\Gamma \vald} $$

We have $\sigma(e) \in E_\Gamma(M[\sigma] =_A N[\sigma])$ by hypothesis.
\item
$$ \infer{\Gamma \vdash \reff{M} : M =_A M}{\Gamma \vdash M : A} $$

This case holds by Lemma \ref{lm:Eref}.
\item
$$ \infer{\Gamma \vdash P \supset^* Q : \phi \supset \psi =_\Omega \phi' \supset \psi'}{\Gamma \vdash P : \phi =_\Omega \phi' \quad \Gamma \vdash Q : \psi =_\Omega \psi'} $$

This case holds by Lemma \ref{lm:Esupset}.

\item
$$ \infer{\Gamma \vdash \univ{\phi}{\psi}{\delta}{\epsilon} : \phi =_\Omega \psi}{\Gamma \vdash \delta : \phi \supset \psi \quad \Gamma \vdash \epsilon : \psi \supset \phi} $$

This case holds by Lemma \ref{lm:Euniv}.
\item
$$ \infer{\Gamma \vdash P^+ : \phi \supset \psi}{\Gamma \vdash P : \phi =_\Omega \psi} $$

The induction hypothesis gives $P[\sigma] \in E_\Delta(\phi[\sigma] =_\Omega \psi[\sigma])$, and so immediately $P[\sigma]^+ \in E_\Delta(\phi[\sigma] \supset \psi[\sigma])$.
\item
$$ \infer{\Gamma \vdash P^- : \psi \supset \phi}{\Gamma \vdash P : \phi =_\Omega \psi} $$

The induction hypothesis gives $P[\sigma] \in E_\Delta(\phi[\sigma] =_\Omega \psi[\sigma])$, and so immediately $P[\sigma]^- \in E_\Delta(\psi[\sigma] \supset \phi[\sigma])$.
\item
$$ \infer{\Gamma \vdash \triplelambda e : x =_A y . P : M =_{A \rightarrow B} N}
  {\begin{array}{c}
     \Gamma, x : A, y : A, e : x =_A y \vdash P : M x =_B N y \\
     \Gamma \vdash M : A \rightarrow B \quad
\Gamma \vdash N : A \rightarrow B
     \end{array}} $$

Let $\Theta \supseteq \Delta$, $L, L' \in E_\Theta(A)$, and $Q \in E_\Theta(L =_A L')$.  We must show that
\[ (\triplelambda e:x =_A y. P [ \sigma ])_{L L'} Q \in E_\Theta(ML =_B NL') \enspace . \]
We have that $(\sigma, x:=L, y:=L', e:=Q) : (\Gamma, x : A, y : A, e : x =_A y) \rightarrow \Theta$ is computable, and so
the induction hypothesis gives
\[ P [ \sigma, x := L, y := L', e := Q ] \in E_\Theta(ML =_B NL') \enspace . \]
The result follow by Lemma \ref{lm:wte}.\ref{lm:wteE}.
\item
$$ \infer{\Gamma \vdash P_{NN'}Q : MN =_B M' N'}{\Gamma \vdash P : M =_{A \rightarrow B} M' \quad \Gamma \vdash Q : N =_A N' \quad \Gamma \vdash N : A \quad \Gamma \vdash N' : A}$$

The induction hypothesis gives $P[\sigma] \in E_\Delta(M[\sigma] =_{A \rightarrow B} M'[\sigma])$ and $N[\sigma] \in E_\Delta(A)$, $N'[\sigma] \in E_\Delta(A)$, $Q[\sigma] \in E_\Delta(N =_A N')$.
It follows immediately that $(P_{NN'}Q)[\sigma] \in E_\Delta(M[\sigma] N[\sigma] =_B M'[\sigma] N'[\sigma])$.
\item
$$ \infer[(M \simeq M', N \simeq N')]{\Gamma \vdash P : M' =_A N'}{\Gamma \vdash P : M =_A N \quad \Gamma \vdash M' : A \quad \Gamma \vdash N' : A} $$

The induction hypothesis gives $P[\sigma] \in E_\Delta(M[\sigma] =_A N[\sigma])$, hence $P[\sigma] \in E_\Delta(M'[\sigma] =_A N'[\sigma])$ by Lemma
\ref{lm:conv-compute}.
\end{itemize}
\end{proof}

\AgdaHide{
\begin{code}
{-computable-path-substitution .U V τ σ σ' .Γ Δ _ _ σ∶Γ⇒CΔ σ'∶Γ⇒CΔ τ∶σ∼σ' (ΛR {U} {Γ} {A} {M} {B} Γ,A⊢M∶B) validΔ = 
  let validΔAA : valid (Δ ,T A ,T A)
      validΔAA = ctxTR (ctxTR validΔ) in
  let validΔAAE : valid (addpath Δ A)
      validΔAAE = ctxER (varR x₁ validΔAA) (varR x₀ validΔAA) in
  let σ∶Γ⇒Δ = subC-typed σ∶Γ⇒CΔ in
  let σ'∶Γ⇒Δ = subC-typed σ'∶Γ⇒CΔ in
  let sub↖σ-typed : sub↖ σ ∶ Γ ,T A ⇒ addpath Δ A
      sub↖σ-typed = sub↖-typed σ∶Γ⇒Δ in
  let sub↗σ'-typed : sub↗ σ' ∶ Γ ,T A ⇒ addpath Δ A
      sub↗σ'-typed = sub↗-typed σ'∶Γ⇒Δ in
  func-EE (lllR (convER (Path-substitution Γ,A⊢M∶B
                             (liftPathSub-typed (pathsubC-typed {τ = τ} {σ} {σ = σ'} {Γ} {Δ} τ∶σ∼σ')) sub↖σ-typed sub↗σ'-typed
                             validΔAAE)
                             (appR (ΛR (weakening {ρ = liftRep _ upRep}
                                           {M = ((M ⟦ liftSub _ σ ⟧) 〈 liftRep _ upRep 〉) 〈 liftRep _ upRep 〉} 
                                        (weakening {ρ = liftRep _ upRep}
                                           {M = (M ⟦ liftSub _ σ ⟧) 〈 liftRep _ upRep 〉} 
                                        (weakening {ρ = liftRep _ upRep} {M = M ⟦ liftSub _ σ ⟧} 
                                        (substitution {σ = liftSub -Term σ} {M = M} Γ,A⊢M∶B (ctxTR validΔ) 
                                          (liftSub-typed (subC-typed σ∶Γ⇒CΔ))) (ctxTR (ctxTR validΔ)) (liftRep-typed upRep-typed)) 
                                        (ctxTR (ctxTR (ctxTR validΔ))) 
                                        (liftRep-typed upRep-typed)) 
                           (ctxTR (ctxER (varR (↑ x₀) (ctxTR (ctxTR validΔ))) (varR x₀ (ctxTR (ctxTR validΔ))))) 
                           (liftRep-typed upRep-typed))) 
                           (varR x₂ (ctxER ((varR (↑ x₀) (ctxTR (ctxTR validΔ)))) (varR x₀ (ctxTR (ctxTR validΔ))))))  
                              (let stepA : addpath Δ A ,T A ⊢ M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ∶ ty B
                                   stepA = weakening {U = V , -Term , -Term , -Term} {V = V , -Term , -Term , -Path , -Term} {ρ = liftRep _ upRep} {Γ = Δ , ty A , ty A , ty A} {M = M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉} 
                                      (weakening {ρ = liftRep _ upRep} {Γ = Δ , ty A , ty A}
                                         {M = (M ⟦ liftSub _ σ' ⟧) 〈 liftRep _ upRep 〉} 
                                      (weakening {ρ = liftRep _ upRep} {M = M ⟦ liftSub _ σ' ⟧} 
                                      (substitution {σ = liftSub _ σ'} {M = M} 
                                      Γ,A⊢M∶B 
                                      (ctxTR validΔ) 
                                      (liftSub-typed σ'∶Γ⇒Δ))
                                      validΔAA 
                                      (liftRep-typed upRep-typed)) 
                                      (ctxTR validΔAA) 
                                      (liftRep-typed upRep-typed))
                                      (ctxTR validΔAAE)
                                      (liftRep-typed upRep-typed) in
                              let stepB : addpath Δ A ⊢ (ΛT A M) ⟦ σ' ⟧ ⇑ ⇑ ⇑ ∶ ty (A ⇛ B)
                                  stepB = ΛR stepA in
                              let stepC : addpath Δ A ⊢ var x₁ ∶ ty A
                                  stepC = varR x₁ validΔAAE in
                              let stepD : addpath Δ A ⊢ appT ((ΛT A M) ⟦ σ' ⟧ ⇑ ⇑ ⇑) (var x₁) ∶ ty B
                                  stepD = appR stepB stepC in
                              stepD)
                        (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M ⟦ σ ⟧) ⇑ ⇑ ⇑) (var x₂) ⇒ a) (let open ≡-Reasoning in
                           M ⟦ liftSub _ σ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₂) ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉) ⟩⟩
                           M ⟦ liftSub _ σ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₂) •SR liftRep _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ ⟧ 〈 liftRep _ upRep 〉) ⟩⟩
                           M ⟦ liftSub _ σ ⟧ 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₂) •SR liftRep _ upRep •SR liftRep _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ ⟧) ⟩⟩
                           M ⟦ liftSub _ σ ⟧ ⟦ x₀:= (var x₂) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₂) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep • liftSub _ σ ⟧
                         ≡⟨ sub-congr M aux₃ ⟩
                           M ⟦ sub↖ σ ⟧
                           ∎) (redex ?)))) 
                         (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M ⟦ σ' ⟧) ⇑ ⇑ ⇑) (var x₁) ⇒ a) 
                         (let open ≡-Reasoning in
                           M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₁) ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉) ⟩⟩
                           M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₁) •SR liftRep _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ upRep 〉) ⟩⟩
                           M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₁) •SR liftRep _ upRep •SR liftRep _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ' ⟧) ⟩⟩
                           M ⟦ liftSub _ σ' ⟧ ⟦ x₀:= (var x₁) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₁) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep • liftSub _ σ' ⟧
                         ≡⟨ sub-congr M aux₄ ⟩
                           M ⟦ sub↗ σ' ⟧
                           ∎) 
                         (redex ?))))))
    (λ W Θ N N' Q ρ ρ∶Δ⇒Θ N∈EΘA N'∈EΘA Q∈EΘN≡N' → 
    let validΘ : valid Θ
        validΘ = context-validity (E-typed N∈EΘA) in
    let σ₁ : Sub (U , -Term) W
        σ₁ = x₀:= N •SR liftRep -Term ρ • liftSub -Term σ in
    let σ₁∶Γ,A⇒Θ : σ₁ ∶ Γ ,T A ⇒C Θ
        σ₁∶Γ,A⇒Θ = compC (compSRC (botsubC N∈EΘA) (liftRep-typed ρ∶Δ⇒Θ)) (liftSubC σ∶Γ⇒CΔ) in
    let σ₂ : Sub (U , -Term) W
        σ₂ = x₀:= N' •SR liftRep -Term ρ • liftSub -Term σ' in
    let σ₂∶Γ,A⇒Θ : σ₂ ∶ Γ ,T A ⇒C Θ
        σ₂∶Γ,A⇒Θ = compC (compSRC (botsubC N'∈EΘA) (liftRep-typed ρ∶Δ⇒Θ)) (liftSubC σ'∶Γ⇒CΔ) in --REFACTOR Common pattern
    let ρ' = liftRep -Path (liftRep -Term (liftRep -Term ρ)) in
    let step1 : x₀:= N • liftSub -Term (ρ •RS σ) ∼ σ₁
        step1 = sub-trans (comp-congr liftSub-compRS) 
                  (assocRSSR {ρ = x₀:= N} {σ = liftRep -Term ρ} {τ = liftSub -Term σ}) in
    let step2 : x₀:= N' • liftSub -Term (ρ •RS σ') ∼ σ₂
        step2 = sub-trans (comp-congr liftSub-compRS) 
                  (assocRSSR {ρ = x₀:= N'} {σ = liftRep -Term ρ} {τ = liftSub -Term σ'}) in
    let sub-rep-comp : ∀ (σ : Sub U V) (N : Term W) → M ⟦ x₀:= N •SR liftRep _ ρ • liftSub _ σ ⟧ ≡ M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= N ⟧
        sub-rep-comp σ N = let open ≡-Reasoning in
             begin
               M ⟦ x₀:= N •SR liftRep -Term ρ • liftSub -Term σ ⟧
             ≡⟨ sub-comp M ⟩
               M ⟦ liftSub -Term σ ⟧ ⟦ x₀:= N •SR liftRep -Term ρ ⟧
             ≡⟨ sub-compSR (M ⟦ liftSub -Term σ ⟧) ⟩
               M ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term ρ 〉 ⟦ x₀:= N ⟧
             ∎ in
    let ih : EE Θ (M ⟦ σ₁ ⟧ ≡〈 B 〉 M ⟦ σ₂ ⟧) 
                  (M ⟦⟦ extendPS (ρ •RP τ) Q ∶ σ₁ ∼ σ₂ ⟧⟧)
        ih = (computable-path-substitution (U , -Term) W (extendPS (ρ •RP τ) Q) σ₁ σ₂ (Γ ,T A) Θ _ _ σ₁∶Γ,A⇒Θ σ₂∶Γ,A⇒Θ
             (change-ends {σ = x₀:= N' • liftSub -Term (ρ •RS σ')} {σ' = σ₂} (extendPS-typedC (compRP-typedC {ρ = ρ} {τ} {σ} {σ'} τ∶σ∼σ' ρ∶Δ⇒Θ) 
               Q∈EΘN≡N')
                 step1 step2) Γ,A⊢M∶B validΘ) in
    let Δ,A⊢Mσ∶B : Δ ,T A ⊢ M ⟦ liftSub _ σ ⟧ ∶ ty B
        Δ,A⊢Mσ∶B = substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed σ∶Γ⇒Δ) in
    let Δ,A⊢Mσ'∶B : Δ ,T A ⊢ M ⟦ liftSub _ σ' ⟧ ∶ ty B
        Δ,A⊢Mσ'∶B = substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed σ'∶Γ⇒Δ) in
    let Θ,A⊢Mσ∶B : Θ ,T A ⊢ M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ∶ ty B
        Θ,A⊢Mσ∶B = weakening Δ,A⊢Mσ∶B (ctxTR validΘ) (liftRep-typed ρ∶Δ⇒Θ) in
    let Θ,A⊢Mσ'∶B : Θ ,T A ⊢ M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ ρ 〉 ∶ ty B
        Θ,A⊢Mσ'∶B = weakening Δ,A⊢Mσ'∶B (ctxTR validΘ) (liftRep-typed ρ∶Δ⇒Θ) in --TODO Common pattern
    let Θ⊢N∶A : Θ ⊢ N ∶ ty A
        Θ⊢N∶A = E-typed N∈EΘA in
    let Θ⊢N'∶A : Θ ⊢ N' ∶ ty A
        Θ⊢N'∶A = E-typed N'∈EΘA in
        expand-EE (conv-EE 
          (subst (EE Θ (M ⟦ σ₁ ⟧ ≡〈 B 〉 M ⟦ σSR ⟧)) (let open ≡-Reasoning in
          begin
            M ⟦⟦ extendPS (ρ •RP τ) Q ∶ σ₁ ∼
                 σSR ⟧⟧
          ≡⟨⟨ pathsub-cong M ∼∼-refl step1 step2 ⟩⟩
            M ⟦⟦ extendPS (ρ •RP τ) Q ∶ x₀:= N • liftSub -Term (ρ •RS σ) ∼
                 x₀:= N' • liftSub -Term (ρ •RS σ') ⟧⟧
          ≡⟨ pathsub-extendPS M ⟩
            M ⟦⟦ liftPathSub (ρ •RP τ) ∶ sub↖ (ρ •RS σ) ∼ sub↗ (ρ •RS σ') ⟧⟧ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
          ≡⟨ sub-congl (pathsub-cong M liftPathSub-compRP sub↖-comp₁ sub↗-comp₁) ⟩
            M ⟦⟦ ρ' •RP liftPathSub τ ∶ ρ' •RS sub↖ σ ∼ ρ' •RS sub↗ σ' ⟧⟧ ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
          ≡⟨ sub-congl (pathsub-compRP M) ⟩
            (M ⟦⟦ liftPathSub τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧) 〈 ρ' 〉 ⟦ x₀:= N • x₀:= (N' ⇑) • x₀:= (Q ⇑ ⇑) ⟧
          ∎) ih) 
          (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M) ⟦ σ ⟧ 〈 ρ 〉) N ⇒ a) (sym (sub-rep-comp σ N)) (redex ?)))) 
          (sym-conv (osr-conv (subst (λ a → appT ((ΛT A M) ⟦ σ' ⟧ 〈 ρ 〉) N' ⇒ a) (sym (sub-rep-comp σ' N')) (redex ?)))) --REFACTOR Duplication
          (appR (ΛR Θ,A⊢Mσ∶B) Θ⊢N∶A) 
          (appR (ΛR Θ,A⊢Mσ'∶B) (E-typed N'∈EΘA)))
        (let step3 : addpath Δ A ⊢
                         M ⟦⟦ liftPathSub τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧
                         ∶ M ⟦ sub↖ σ ⟧ ≡〈 B 〉 M ⟦ sub↗ σ' ⟧
             step3 = Path-substitution Γ,A⊢M∶B (liftPathSub-typed (pathsubC-typed {τ = τ} {σ} {σ'} {Γ} {Δ} τ∶σ∼σ')) 
                     sub↖σ-typed sub↗σ'-typed validΔAAE in
        let step4 : addpath Θ A ⊢
                    M ⟦⟦ liftPathSub τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ 〈 ρ' 〉
                  ∶ M ⟦ sub↖ σ ⟧ 〈 ρ' 〉 ≡〈 B 〉 M ⟦ sub↗ σ' ⟧ 〈 ρ' 〉
            step4 = weakening step3 
                    (ctxER (varR x₁ (ctxTR (ctxTR validΘ)))
                    (varR x₀ (ctxTR (ctxTR validΘ))))
                    (liftRep-typed (liftRep-typed (liftRep-typed ρ∶Δ⇒Θ))) in
        let step5 : ∀ σ x → σ ∶ Γ ⇒ Δ → typeof x (addpath Θ A) ≡ ty A → addpath Θ A ⊢
                    appT ((ΛT A M) ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x) ∶ ty B
            step5 σ x σ∶Γ⇒Θ x∶A∈ΘA = appR 
                           (ΛR (subst (λ a → addpath Θ A ,T A ⊢ a ∶ ty B) 
                           (trans (sub-compRS M) (trans (rep-comp (M ⟦ liftSub _ σ ⟧))
                           (trans (rep-comp (M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉)) 
                             (rep-comp (M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 〈 liftRep _ upRep 〉)))))
                         (substitution {σ = liftRep _ upRep •R liftRep _ upRep •R liftRep _ upRep •R liftRep _ ρ •RS liftSub _ σ} Γ,A⊢M∶B 
                         (ctxTR (ctxER (varR x₁ (ctxTR (ctxTR validΘ))) (varR x₀ (ctxTR (ctxTR validΘ)))))
                         (compRS-typed
                            {ρ = liftRep _ upRep •R liftRep _ upRep •R liftRep _ upRep •R liftRep _ ρ}
                            {σ = liftSub _ σ} 
                            (compR-typed {ρ = liftRep _ upRep •R liftRep _ upRep •R liftRep _ upRep}
                              {σ = liftRep _ ρ}
                              (compR-typed {ρ = liftRep _ upRep •R liftRep _ upRep} {σ = liftRep _ upRep}
                                (compR-typed {ρ = liftRep _ upRep} {σ = liftRep _ upRep} (liftRep-typed upRep-typed) (liftRep-typed upRep-typed)) (liftRep-typed upRep-typed)) 
                            (liftRep-typed ρ∶Δ⇒Θ))
                         (liftSub-typed σ∶Γ⇒Θ)))))
                         (change-type (varR x (ctxER (varR x₁ (ctxTR (ctxTR validΘ))) (varR x₀ (ctxTR (ctxTR validΘ))))) x∶A∈ΘA) in --TODO Extract last line as lemma
             let step6 : addpath Θ A ⊢
                         M ⟦⟦ liftPathSub τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧ 〈 ρ' 〉
                         ∶ appT ((ΛT A M) ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT ((ΛT A M) ⟦ σ' ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑) (var x₁)
                 step6 = convER step4 (step5 σ x₂ σ∶Γ⇒Δ refl) (step5 σ' x₁ σ'∶Γ⇒Δ refl)
                         (subst (λ a → a ≃ appT (((ΛT A M ⟦ σ ⟧) 〈 ρ 〉) ⇑ ⇑ ⇑) (var x₂)) 
                         (let open ≡-Reasoning in
                           M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₂) ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉) ⟩⟩
                           M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₂) •SR liftRep _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 〈 liftRep _ upRep 〉) ⟩⟩
                           M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₂) •SR liftRep _ upRep •SR liftRep _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉) ⟩⟩
                           M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= (var x₂) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ ⟧) ⟩⟩
                           M ⟦ liftSub _ σ ⟧ ⟦ x₀:= (var x₂) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ ρ ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₂) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ ρ • liftSub _ σ ⟧
                         ≡⟨ sub-congr M aux ⟩
                           M ⟦ liftRep _ (liftRep _ (liftRep _ ρ)) •RS sub↖ σ ⟧
                         ≡⟨ sub-compRS M ⟩ 
                           M ⟦ sub↖ σ ⟧ 〈 liftRep _ (liftRep _ (liftRep _ ρ)) 〉
                           ∎)
                           (sym-conv (osr-conv (redex ?)))) 
                         (subst (λ a → a ≃ appT (((ΛT A M ⟦ σ' ⟧) 〈 ρ 〉) ⇑ ⇑ ⇑) (var x₁)) 
                           (let open ≡-Reasoning in 
                           M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ ρ 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₁) ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ ρ 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉) ⟩⟩
                           M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ ρ 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₁) •SR liftRep _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ ρ 〉 〈 liftRep _ upRep 〉) ⟩⟩
                           M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ ρ 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₁) •SR liftRep _ upRep •SR liftRep _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ ρ 〉) ⟩⟩
                           M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= (var x₁) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep ⟧
                         ≡⟨⟨ sub-compSR (M ⟦ liftSub _ σ' ⟧) ⟩⟩
                           M ⟦ liftSub _ σ' ⟧ ⟦ x₀:= (var x₁) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ ρ ⟧
                         ≡⟨⟨ sub-comp M ⟩⟩
                           M ⟦ x₀:= (var x₁) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ ρ • liftSub _ σ' ⟧
                         ≡⟨ sub-congr M aux₂ ⟩
                           M ⟦ liftRep _ (liftRep _ (liftRep _ ρ)) •RS sub↗ σ' ⟧
                         ≡⟨ sub-compRS M ⟩ 
                           M ⟦ sub↗ σ' ⟧ 〈 liftRep _ (liftRep _ (liftRep _ ρ)) 〉
                           ∎)
                           (sym-conv (osr-conv (redex ?)))) in
      app*R (E-typed N∈EΘA) (E-typed N'∈EΘA) 
      (lllR step6) (EE-typed Q∈EΘN≡N'))
      ?) where
    aux : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} → 
        x₀:= (var x₂) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ ρ • liftSub _ σ ∼ liftRep _ (liftRep _ (liftRep _ ρ)) •RS sub↖ σ
    aux x₀ = refl
    aux {ρ = ρ} {σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₂) •SR liftRep -Term upRep •SR liftRep -Term upRep •SR
       liftRep -Term upRep
       •SR liftRep -Term ρ ⟧
      ≡⟨ sub-compSR (σ _ x ⇑) ⟩
        σ _ x ⇑ 〈 liftRep _ ρ 〉 ⟦ x₀:= (var x₂) •SR liftRep -Term upRep •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⟦ x₀:= (var x₂) •SR liftRep -Term upRep •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₂) •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x 〈 ρ 〉)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⟦ x₀:= (var x₂) •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₂) •SR liftRep -Term upRep ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x 〈 ρ 〉 ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) •SR liftRep -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ 〈 liftRep -Term upRep 〉 ⟦ x₀:= (var x₂) ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) ⟧
      ≡⟨ botsub-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑
      ≡⟨⟨ liftRep-upRep₃ (σ _ x) ⟩⟩
        σ _ x ⇑ ⇑ ⇑ 〈 liftRep _ (liftRep _ (liftRep _ ρ)) 〉
      ∎
    aux₂ : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} → 
        x₀:= (var x₁) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ ρ • liftSub _ σ ∼ liftRep _ (liftRep _ (liftRep _ ρ)) •RS sub↗ σ
    aux₂ x₀ = refl
    aux₂ {ρ = ρ} {σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₁) •SR liftRep -Term upRep •SR liftRep -Term upRep •SR
       liftRep -Term upRep
       •SR liftRep -Term ρ ⟧
      ≡⟨ sub-compSR (σ _ x ⇑) ⟩
        σ _ x ⇑ 〈 liftRep _ ρ 〉 ⟦ x₀:= (var x₁) •SR liftRep -Term upRep •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⟦ x₀:= (var x₁) •SR liftRep -Term upRep •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₁) •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x 〈 ρ 〉)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⟦ x₀:= (var x₁) •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₁) •SR liftRep -Term upRep ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x 〈 ρ 〉 ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) •SR liftRep -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ 〈 liftRep -Term upRep 〉 ⟦ x₀:= (var x₁) ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑)) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) ⟧
      ≡⟨ botsub-upRep (σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑) ⟩
        σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑
      ≡⟨⟨ liftRep-upRep₃ (σ _ x) ⟩⟩
        σ _ x ⇑ ⇑ ⇑ 〈 liftRep _ (liftRep _ (liftRep _ ρ)) 〉
      ∎
    aux₃ : ∀ {U} {V} {σ : Sub U V} → 
        x₀:= (var x₂) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep • liftSub _ σ ∼ sub↖ σ
    aux₃ x₀ = refl
    aux₃ {σ = σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₂) •SR liftRep -Term upRep •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x ⇑) ⟩
        σ _ x ⇑ 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₂) •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x)) ⟩
        σ _ x ⇑ ⇑ ⟦ x₀:= (var x₂) •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₂) •SR liftRep -Term upRep ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x  ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) •SR liftRep -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑ 〈 liftRep -Term upRep 〉 ⟦ x₀:= (var x₂) ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x  ⇑ ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₂) ⟧
      ≡⟨ botsub-upRep (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑
      ∎
    aux₄ : ∀ {U} {V} {σ : Sub U V} → 
        x₀:= (var x₁) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep • liftSub _ σ ∼ sub↗ σ
    aux₄ x₀ = refl
    aux₄ {σ = σ} (↑ x) = let open ≡-Reasoning in 
      begin
        σ _ x ⇑ ⟦ x₀:= (var x₁) •SR liftRep -Term upRep •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑) ⟩
        σ _ x  ⇑ 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₁) •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x )) ⟩
        σ _ x  ⇑ ⇑ ⟦ x₀:= (var x₁) •SR liftRep -Term upRep •SR liftRep -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ 〈 liftRep _ upRep 〉 ⟦ x₀:= (var x₁) •SR liftRep -Term upRep ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x  ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) •SR liftRep -Term upRep ⟧
      ≡⟨ sub-compSR (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑ 〈 liftRep -Term upRep 〉 ⟦ x₀:= (var x₁) ⟧
      ≡⟨ sub-congl (liftRep-upRep (σ _ x  ⇑ ⇑)) ⟩
        σ _ x  ⇑ ⇑ ⇑ ⇑ ⟦ x₀:= (var x₁) ⟧
      ≡⟨ botsub-upRep (σ _ x  ⇑ ⇑ ⇑) ⟩
        σ _ x  ⇑ ⇑ ⇑
      ∎ -}
\end{code}
}

\begin{corollary}[Soundness]
If $\Gamma \vdash t : T$ then $t \in E_\Gamma(T)$.
\end{corollary}

\begin{proof}
We apply the theorem with $\sigma$ the identity substitution.  The identity substitution is computable
by Lemmas \ref{lm:varcompute1} and \ref{lm:varcompute2}.
\end{proof}

\begin{corollary}[Strong Normalization]
\label{cor:SN}
Every well-typed term, proof and path is strongly normalizing.
\end{corollary}

%<*Strong-Normalization>
\begin{code}
postulate all-Ectxt : ∀ {V} {Γ : Context V} → valid Γ → Ectxt Γ

postulate Strong-Normalization : ∀ V K (Γ : Context V) 
                               (M : Expression V (varKind K)) A → Γ ⊢ M ∶ A → SN M
\end{code}
%</Strong-Normalization>

\AgdaHide{
\begin{code}
--Strong-Normalization V K Γ M A Γ⊢M∶A = E-SN
--  (subst (E Γ _) sub-idSub
--  (Computable-Sub (idSub V) (idSubC (context-validity Γ⊢M∶A) (all-Ectxt (context-validity Γ⊢M∶A))) Γ⊢M∶A (context-validity Γ⊢M∶A)))
\end{code}
}

\begin{corollary}[Canonicity]
\label{cor:canon}
If $\vdash s : T$, then there is a unique canonical object $t$ of $T$ such that $s \twoheadrightarrow t$.
\end{corollary}

\begin{corollary}[Consistency]
There is no proof $\delta$ such that $\vdash \delta : \bot$.
\end{corollary}

\AgdaHide{
\begin{code}
postulate Consistency' : ∀ {M : Proof ∅} → SN M → 〈〉 ⊢ M ∶ ⊥ → Empty
-- Consistency' (SNI M SNM) ⊢M∶⊥ = {!!}
\end{code}
}

%<*Consistency>
\begin{code}
postulate Consistency : ∀ {M : Proof ∅} → 〈〉 ⊢ M ∶ ⊥ → Empty
\end{code}
%</Consistency>

\AgdaHide{
\begin{code}
-- Consistency = {!!}
\end{code}
}

