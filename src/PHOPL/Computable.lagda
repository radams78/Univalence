\AgdaHide{
\begin{code}
module PHOPL.Computable where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.PathSub
open import PHOPL.Red
open import PHOPL.SN
open import PHOPL.Rules
open import PHOPL.Meta
open import PHOPL.KeyRedex
open import PHOPL.Neutral
\end{code}
}

We define a model of the type theory with types as sets of terms.  For every type (proposition, equation) $A$ in context $\Gamma$, define
the set of \emph{computable} terms (proofs, paths) $E_\Gamma(A)$.

\begin{definition}[Computable Expressions]
\begin{align*}
E_\Gamma(\Omega) \eqdef & \{ M \mid \Gamma \vdash M : \Omega, M \in \SN \} \\
E_\Gamma(A \rightarrow B) \eqdef & \{ M \mid \Gamma \vdash M : A \rightarrow B, \\
& \quad \forall (\Delta \supseteq \Gamma) (N \in E_\Delta(A)). MN \in E_\Delta(B), \\
& \quad \forall (\Delta \supseteq \Gamma) (N, N' \in E_\Delta(A)) (P \in E_\Delta(N =_A N')). \\
& \quad \quad \reff{M}_{N N'} P \in E_\Gamma(MN =_B MN') \} \\
\\
E_\Gamma(\bot) & \eqdef \{ \delta \mid \Gamma \vdash \delta : \bot, \delta \in \SN \} \\
E_\Gamma(\phi \supset \psi) & \eqdef \{ \delta \mid \Gamma \vdash \delta : \phi \supset \psi, \\
& \forall (\Delta \supseteq \Gamma)(\epsilon \in E_\Delta(\phi)). \delta \epsilon \in E_\Gamma(\psi) \} \\
E_\Gamma(\phi) & \eqdef \{ \delta \mid \Gamma \vdash \delta : \phi, \delta \in \SN \} \\
& \qquad (\phi \text{ neutral}) \\
E_\Gamma(\phi) & \eqdef E_\Gamma(nf(\phi)) \\
& \qquad (\phi \mbox{ a normalizable term of type $\Omega$}) \\
\\
E_\Gamma(\phi =_\Omega \psi) & \eqdef \{ P \mid \Gamma \vdash P : \phi =_\Omega \psi, \\
& P^+ \in E_\Gamma(\phi \supset \psi), P^- \in E_\Gamma(\psi \supset \phi) \} \\
\\
E_\Gamma(M =_{A \rightarrow B} M') & \eqdef \{ P \mid \Gamma \vdash P : M =_{A \rightarrow B} M', \\
& \forall (\Delta \supseteq \Gamma) (N, N' \in E_\Delta(A)) (Q \in E_\Delta(N =_A N')). \\
& P_{NN'}Q \in E_\Delta(MN =_B M'N') \}
\end{align*}
\end{definition}

\AgdaHide{
\begin{code}
data Shape : Set where
  neutral : Shape
  bot : Shape
  imp : Shape → Shape → Shape

data Leaves (V : Alphabet) : Shape → Set where
  neutral : Neutral V → Leaves V neutral
  bot : Leaves V bot
  imp : ∀ {S} {T} → Leaves V S → Leaves V T → Leaves V (imp S T)

lrep : ∀ {U} {V} {S} → Rep U V → Leaves U S → Leaves V S
lrep ρ (neutral N) = neutral (nrep ρ N)
lrep ρ bot = bot
lrep ρ (imp φ ψ) = imp (lrep ρ φ) (lrep ρ ψ)

decode-Prop : ∀ {V} {S} → Leaves V S → Term V
decode-Prop (neutral N) = decode-Neutral N
decode-Prop bot = ⊥
decode-Prop (imp φ ψ) = decode-Prop φ ⊃ decode-Prop ψ

leaves-red : ∀ {V} {S} {L : Leaves V S} {φ : Term V} →
  decode-Prop L ↠ φ →
  Σ[ L' ∈ Leaves V S ] decode-Prop L' ≡ φ
leaves-red {S = neutral} {L = neutral N} L↠φ = 
  let (N ,p N≡φ) = neutral-red {N = N} L↠φ in neutral N ,p N≡φ
leaves-red {S = bot} {L = bot} L↠φ = bot ,p sym (bot-red L↠φ)
leaves-red {S = imp S T} {L = imp φ ψ} φ⊃ψ↠χ = 
  let (φ' ,p ψ' ,p φ↠φ' ,p ψ↠ψ' ,p χ≡φ'⊃ψ') = imp-red φ⊃ψ↠χ in 
  let (L₁ ,p L₁≡φ') = leaves-red {L = φ} φ↠φ' in 
  let (L₂ ,p L₂≡ψ') = leaves-red {L = ψ} ψ↠ψ' in 
  (imp L₁ L₂) ,p (trans (cong₂ _⊃_ L₁≡φ' L₂≡ψ') (sym χ≡φ'⊃ψ'))

computeP : ∀ {V} {S} → Context V → Leaves V S → Proof V → Set
computeP {S = neutral} Γ (neutral _) δ = SN δ
computeP {S = bot} Γ bot δ = SN δ
computeP {S = imp S T} Γ (imp φ ψ) δ = 
  ∀ {W} (Δ : Context W) {ρ} {ε}
  (ρ∶Γ⇒RΔ : ρ ∶ Γ ⇒R Δ) (Δ⊢ε∶φ : Δ ⊢ ε ∶ (decode-Prop (lrep ρ φ)))
  (computeε : computeP {S = S} Δ (lrep ρ φ) ε) → 
  computeP {S = T} Δ (lrep ρ ψ) (appP (δ 〈 ρ 〉) ε)

computeT : ∀ {V} → Context V → Type → Term V → Set
computeE : ∀ {V} → Context V → Term V → Type → Term V → Path V → Set

computeT Γ Ω M = SN M
computeT Γ (A ⇛ B) M = 
  (∀ {W} (Δ : Context W) {ρ} {N} (ρ∶Γ⇒Δ : ρ ∶ Γ ⇒R Δ) (Δ⊢N∶A : Δ ⊢ N ∶ ty A) (computeN : computeT Δ A N) →
    computeT Δ B (appT (M 〈 ρ 〉) N)) ×
  (∀ {W} (Δ : Context W) {ρ} {N} {N'} {P} 
    (ρ∶Γ⇒Δ : ρ ∶ Γ ⇒R Δ) (Δ⊢P∶N≡N' : Δ ⊢ P ∶ N ≡〈 A 〉 N') 
    (computeN : computeT Δ A N) (computeN' : computeT Δ A N') (computeP : computeE Δ N A N' P) →
    computeE Δ (appT (M 〈 ρ 〉) N) B (appT (M 〈 ρ 〉) N') (M 〈 ρ 〉 ⋆[ P ∶ N ∼ N' ]))

computeE {V} Γ M Ω N P = Σ[ S ∈ Shape ] Σ[ T ∈ Shape ] Σ[ L ∈ Leaves V S ] Σ[ L' ∈ Leaves V T ] M ↠ decode-Prop L × N ↠ decode-Prop L' × computeP Γ (imp L L') (plus P) × computeP Γ (imp L' L) (minus P)
computeE Γ M (A ⇛ B) M' P =
  ∀ {W} (Δ : Context W) {ρ} {N} {N'} {Q} (ρ∶Γ⇒RΔ : ρ ∶ Γ ⇒R Δ) (Δ⊢Q∶N≡N' : Δ ⊢ Q ∶ N ≡〈 A 〉 N')
  (computeQ : computeE Δ N A N' Q) → computeE Δ (appT (M 〈 ρ 〉) N) B (appT (M' 〈 ρ 〉)  N') 
    (app* N N' (P 〈 ρ 〉) Q)

postulate compute-SN : ∀ {V} {Γ : Context V} {A} {δ} → computeT Γ A δ → valid Γ → SN δ

postulate decode-rep : ∀ {U} {V} {S} (L : Leaves U S) {ρ : Rep U V} →
                     decode-Prop (lrep ρ L) ≡ decode-Prop L 〈 ρ 〉

postulate conv-computeP : ∀ {V} {Γ : Context V} {S} {L M : Leaves V S} {δ} →
                        computeP Γ L δ → decode-Prop L ≃ decode-Prop M →
                        Γ ⊢ decode-Prop M ∶ ty Ω → computeP Γ M δ

conv-computeE : ∀ {V} {Γ : Context V} {M} {M'} {A} {N} {N'} {P} →
  computeE Γ M A N P → 
  Γ ⊢ M ∶ ty A → Γ ⊢ N ∶ ty A → Γ ⊢ M' ∶ ty A → Γ ⊢ N' ∶ ty A → M ≃ M' → N ≃ N' →
  computeE Γ M' A N' P
conv-computeE {Γ = Γ} {M = M} {M' = M'} {A = Ω} {N' = N'} {P} (S ,p T ,p φ ,p ψ ,p M↠φ ,p N↠ψ ,p computeP+ ,p computeP-) 
  Γ⊢M∶A Γ⊢N∶A Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N' = 
    let (Q ,p φ↠Q ,p M'↠Q) = confluenceT (trans-conv (sym-conv (red-conv M↠φ)) M≃M') in
    let (φ' ,p φ'≡Q) = leaves-red {L = φ} φ↠Q in
    let (R ,p ψ↠R ,p N'↠R) = confluenceT (trans-conv (sym-conv (red-conv N↠ψ)) N≃N') in
    let (ψ' ,p ψ'≡R) = leaves-red {L = ψ} ψ↠R in
    S ,p T ,p φ' ,p ψ' ,p subst (_↠_ M') (sym φ'≡Q) M'↠Q ,p 
    subst (_↠_ N') (sym ψ'≡R) N'↠R ,p 
    (λ Δ {ρ} {ε} ρ∶Γ⇒RΔ Δ⊢ε∶φ'ρ computeε → 
      let step1 : Δ ⊢ decode-Prop (lrep ρ φ) ∶ ty Ω
          step1 = subst (λ x → Δ ⊢ x ∶ ty Ω) 
            (sym (decode-rep φ)) 
            (weakening 
              (Subject-Reduction 
                Γ⊢M∶A M↠φ) (context-validity Δ⊢ε∶φ'ρ) ρ∶Γ⇒RΔ) in
      let step1a : decode-Prop (lrep ρ φ') ≃ decode-Prop (lrep ρ φ)
          step1a = subst₂ _≃_ (sym (trans (decode-rep φ') (rep-congl φ'≡Q))) (sym (decode-rep φ)) (conv-rep {M = Q} {N = decode-Prop φ} 
            (sym-conv (red-conv φ↠Q))) in 
      let step2 : Δ ⊢ ε ∶ decode-Prop (lrep ρ φ)
          step2 = convR Δ⊢ε∶φ'ρ step1 step1a in
      let step3 : computeP Δ (lrep ρ φ) ε
          step3 = conv-computeP {L = lrep ρ φ'} {M = lrep ρ φ} computeε step1a step1 in
      let step4 : computeP Δ (lrep ρ ψ) (appP (plus P 〈 ρ 〉) ε)
          step4 = computeP+ Δ ρ∶Γ⇒RΔ step2 step3 in 
      let step5 : decode-Prop (lrep ρ ψ') ≃ decode-Prop (lrep ρ ψ)
          step5 = subst₂ _≃_ (sym (trans (decode-rep ψ') (rep-congl ψ'≡R))) (sym (decode-rep ψ)) (conv-rep {M = R} {N = decode-Prop ψ} 
            (sym-conv (red-conv ψ↠R))) in
      let step6 : Δ ⊢ decode-Prop (lrep ρ ψ') ∶ ty Ω
          step6 = subst (λ x → Δ ⊢ x ∶ ty Ω) (sym (decode-rep ψ')) 
                (weakening 
                  (subst (λ x → Γ ⊢ x ∶ ty Ω) (sym ψ'≡R) 
                  (Subject-Reduction Γ⊢N'∶A N'↠R)) 
                (context-validity Δ⊢ε∶φ'ρ) 
                ρ∶Γ⇒RΔ) in
      conv-computeP {L = lrep ρ ψ} {M = lrep ρ ψ'} step4 (sym-conv step5) step6) ,p 
    (    (λ Δ {ρ} {ε} ρ∶Γ⇒RΔ Δ⊢ε∶ψ'ρ computeε → 
      let step1 : Δ ⊢ decode-Prop (lrep ρ ψ) ∶ ty Ω
          step1 = subst (λ x → Δ ⊢ x ∶ ty Ω) 
            (sym (decode-rep ψ)) 
            (weakening 
              (Subject-Reduction 
                Γ⊢N∶A N↠ψ) (context-validity Δ⊢ε∶ψ'ρ) ρ∶Γ⇒RΔ) in
      let step1a : decode-Prop (lrep ρ ψ') ≃ decode-Prop (lrep ρ ψ)
          step1a = subst₂ _≃_ (sym (trans (decode-rep ψ') (rep-congl ψ'≡R))) (sym (decode-rep ψ)) (conv-rep {M = R} {N = decode-Prop ψ} 
            (sym-conv (red-conv ψ↠R))) in 
      let step2 : Δ ⊢ ε ∶ decode-Prop (lrep ρ ψ)
          step2 = convR Δ⊢ε∶ψ'ρ step1 step1a in
      let step3 : computeP Δ (lrep ρ ψ) ε
          step3 = conv-computeP {L = lrep ρ ψ'} {M = lrep ρ ψ} computeε step1a step1 in
      let step4 : computeP Δ (lrep ρ φ) (appP (minus P 〈 ρ 〉) ε)
          step4 = computeP- Δ ρ∶Γ⇒RΔ step2 step3 in 
      let step5 : decode-Prop (lrep ρ φ') ≃ decode-Prop (lrep ρ φ)
          step5 = subst₂ _≃_ (sym (trans (decode-rep φ') (rep-congl φ'≡Q))) (sym (decode-rep φ)) (conv-rep {M = Q} {N = decode-Prop φ} 
            (sym-conv (red-conv φ↠Q))) in
      let step6 : Δ ⊢ decode-Prop (lrep ρ φ') ∶ ty Ω
          step6 = subst (λ x → Δ ⊢ x ∶ ty Ω) (sym (decode-rep φ')) 
                (weakening 
                  (subst (λ x → Γ ⊢ x ∶ ty Ω) (sym φ'≡Q) 
                  (Subject-Reduction Γ⊢M'∶A M'↠Q)) 
                (context-validity Δ⊢ε∶ψ'ρ) 
                ρ∶Γ⇒RΔ) in
      conv-computeP {L = lrep ρ φ} {M = lrep ρ φ'} step4 (sym-conv step5) step6))
conv-computeE {A = A ⇛ B} computeP Γ⊢M∶A Γ⊢N∶A Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N' Δ ρ∶Γ⇒RΔ Δ⊢Q∶N≡N' computeQ = 
  conv-computeE {A = B} 
  (computeP Δ ρ∶Γ⇒RΔ Δ⊢Q∶N≡N' computeQ) 
    (appR (weakening Γ⊢M∶A (context-validity Δ⊢Q∶N≡N') ρ∶Γ⇒RΔ) 
      (Equation-Validity₁ Δ⊢Q∶N≡N')) 
    (appR (weakening Γ⊢N∶A (context-validity Δ⊢Q∶N≡N') ρ∶Γ⇒RΔ) 
      (Equation-Validity₂ Δ⊢Q∶N≡N'))
    (appR (weakening Γ⊢M'∶A (context-validity Δ⊢Q∶N≡N') ρ∶Γ⇒RΔ) (Equation-Validity₁ Δ⊢Q∶N≡N')) 
    (appR (weakening Γ⊢N'∶A (context-validity Δ⊢Q∶N≡N') ρ∶Γ⇒RΔ) (Equation-Validity₂ Δ⊢Q∶N≡N')) 
    (appT-convl (conv-rep M≃M')) (appT-convl (conv-rep N≃N'))
--TODO Common pattern

postulate expand-computeE : ∀ {V} {Γ : Context V} {M} {A} {N} {P} {Q} →
                          computeE Γ M A N Q → Γ ⊢ P ∶ M ≡〈 A 〉 N → key-redex P Q → computeE Γ M A N P

postulate expand-computeT : ∀ {V} {Γ : Context V} {A} {M} {N} → computeT Γ A N → Γ ⊢ M ∶ ty A → SN M → key-redex M N → computeT Γ A M
{- expand-computeT {A = Ω} computeψ _ SNM φ▷ψ = SNM
expand-computeT {A = A ⇛ B} {M} {M'} (computeM'app ,p computeM'eq) Γ⊢M∶A⇛B SNM M▷M' = 
  (λ Δ {ρ} {N} ρ∶Γ⇒Δ Δ⊢N∶A computeN → 
    let computeM'N : computeT Δ B (appT (M' 〈 ρ 〉) N)
        computeM'N = computeM'app Δ ρ∶Γ⇒Δ Δ⊢N∶A computeN in
    let validΔ : valid Δ
        validΔ = context-validity Δ⊢N∶A in
    expand-computeT computeM'N 
    (appR (weakening Γ⊢M∶A⇛B validΔ ρ∶Γ⇒Δ) Δ⊢N∶A)
    (expand-lemma (SNrep R-creates-rep SNM) 
         (key-redex-rep M▷M') (compute-SN computeM'N validΔ))
         (appTkr (key-redex-rep M▷M'))) ,p 
  (λ Δ {ρ} {N} {N'} ρ∶Γ⇒Δ Δ⊢P∶N≡N' computeN computeN' computeP₁ → 
    let validΔ : valid Δ
        validΔ = context-validity Δ⊢P∶N≡N' in
    let Γ⊢M'∶A⇛B : Γ ⊢ M' ∶ ty (A ⇛ B)
        Γ⊢M'∶A⇛B = Subject-Reduction Γ⊢M∶A⇛B (key-redex-red M▷M') in
    let Δ⊢M'ρ∶A⇛B : Δ ⊢ M' 〈 ρ 〉 ∶ ty (A ⇛ B)
        Δ⊢M'ρ∶A⇛B = weakening Γ⊢M'∶A⇛B validΔ ρ∶Γ⇒Δ in
    let Δ⊢Mρ∶A⇛B : Δ ⊢ M 〈 ρ 〉 ∶ ty (A ⇛ B)
        Δ⊢Mρ∶A⇛B = weakening Γ⊢M∶A⇛B validΔ ρ∶Γ⇒Δ in
    let Δ⊢N∶A : Δ ⊢ N ∶ ty A
        Δ⊢N∶A = Equation-Validity₁ Δ⊢P∶N≡N' in
    let Δ⊢N'∶A : Δ ⊢ N' ∶ ty A
        Δ⊢N'∶A = Equation-Validity₂ Δ⊢P∶N≡N' in
    let M'ρX≃MρX : ∀ X → appT (M' 〈 ρ 〉) X ≃ appT (M 〈 ρ 〉) X
        M'ρX≃MρX = λ _ → sym-conv (appT-convl (red-conv (red-rep (key-redex-red M▷M')))) in
    expand-computeE 
      (conv-computeE 
        (computeM'eq Δ ρ∶Γ⇒Δ Δ⊢P∶N≡N' computeN computeN' computeP₁) 
        (appR Δ⊢M'ρ∶A⇛B Δ⊢N∶A) 
        (appR Δ⊢M'ρ∶A⇛B Δ⊢N'∶A)
        (appR Δ⊢Mρ∶A⇛B Δ⊢N∶A) 
        (appR Δ⊢Mρ∶A⇛B Δ⊢N'∶A)
        (M'ρX≃MρX N) (M'ρX≃MρX N'))
      (⋆-typed Δ⊢Mρ∶A⇛B Δ⊢P∶N≡N') 
      (key-redex-⋆ (key-redex-rep M▷M'))) -}

compute : ∀ {V} {K} → Context V → Expression V (parent K) → Expression V (varKind K) → Set
compute {K = -Term} Γ (app (-ty A) out) M = computeT Γ A M
compute {V} {K = -Proof} Γ φ δ = Σ[ S ∈ Shape ] Σ[ L ∈ Leaves V S ] φ ↠ decode-Prop L × computeP Γ L δ
compute {K = -Path} Γ (app (-eq A) (M ,, N ,, out)) P = computeE Γ M A N P

postulate expand-computeP : ∀ {V} {Γ : Context V} {S} {L : Leaves V S} {δ ε} →
                          computeP Γ L ε → Γ ⊢ δ ∶ decode-Prop L → key-redex δ ε → computeP Γ L δ

record E' {V} {K} (Γ : Context V) (A : Expression V (parent K)) (E : Expression V (varKind K)) : Set where
  constructor E'I
  field
    typed : Γ ⊢ E ∶ A
    computable : compute Γ A E

--TODO Inline the following?
E : ∀ {V} → Context V → Type → Term V → Set
E Γ A M = E' Γ (ty A) M

EP : ∀ {V} → Context V → Term V → Proof V → Set
EP Γ φ δ = E' Γ φ δ

EE : ∀ {V} → Context V → Equation V → Path V → Set
EE Γ E P = E' Γ E P

E'-typed : ∀ {V} {K} {Γ : Context V} {A} {M : Expression V (varKind K)} → 
           E' Γ A M → Γ ⊢ M ∶ A
E'-typed = E'.typed

postulate func-E : ∀ {U} {Γ : Context U} {M : Term U} {A} {B} →
                   (∀ V Δ (ρ : Rep U V) (N : Term V) → valid Δ → ρ ∶ Γ ⇒R Δ → E Δ A N → E Δ B (appT (M 〈 ρ 〉) N)) →
                   E Γ (A ⇛ B) M
\end{code}
}

\begin{lm}$ $
\label{lm:conv-compute}
\begin{enumerate}
\item
If $\delta \in E_\Gamma(\phi)$, $\Gamma \vdash \psi : \Omega$ and $\phi \simeq_\beta \psi$, then $\delta \in E_\Gamma(\psi)$.
\item
If $P \in E_\Gamma(M =_A N)$, $\Gamma \vdash M' : A$, $\Gamma \vdash N' : A$, $M \simeq_\beta M'$ and $N \simeq_\beta N'$,
then $P \in E_\Gamma(M' =_A N')$.
\end{enumerate}
\end{lm}

\begin{proof}
From the definition of $E_\Gamma(T)$ and confluence.
\end{proof}

\begin{lm}
\label{lm:Eref}
If $M \in E_\Gamma(A)$ then $\reff{M} \in E_\Gamma(M =_A M)$.
\end{lm}

\begin{proof}
The proof is by induction on the type $A$.

If $A \equiv \Omega$: we have $\Gamma \vdash M : A$, hence $\Gamma \vdash \reff{M} : M =_A M$.  Also,
$M \in \SN$, so $\reff{M} \in \SN$.

If $A \equiv B \rightarrow C$: again we have $\Gamma \vdash \reff{M} : M =_A M$.  Now, let $N, N' \in E_\Gamma(B)$
and $P \in E_\Gamma(N =_B N')$.  Then $\reff{M}_{N N'} P \in E_\Gamma(MN =_C MN')$ as required.
\end{proof}

\begin{lm}
\label{lm:Ered}
If $\reff{M}_{N_1 N_2} \reff{N} \in E_\Gamma(L =_A L')$ then $\reff{MN} \in E_\Gamma(L =_A L')$.
\end{lm}

\begin{proof}
We prove the following stronger statement:

If $\reff{M}_{N_1 N_2} \reff{N}_{K_1 K_1'} P_1 \cdots_{K_n K_n'} P_n \in E_\Gamma(L =_A L')$ then \\
$\reff{MN}_{K_1 K_1'} P_1 \cdots_{K_n K_n'} P_n \in E_\Gamma(L =_A L')$.

The proof is by induction on the type $A$.

If $A \equiv \Omega$: we have $\Gamma \vdash \reff{M}_{N_1 N_2} \reff{N} \vec{P} : L =_A L'$, hence $\Gamma \vdash \reff{MN} \vec{P} : L =_A L'$
using Generation.  Also, $\reff{M}_{N_1 N_2} \reff{N} \vec{P} \in \SN$ hence $\reff{MN} \vec{P} \in \SN$ by Lemma \ref{lm:SNrefapp}.

If $A \equiv B \rightarrow C$: we have $\Gamma \vdash \reff{MN} \vec{P} : L =_A L'$ as before.  Now, let $K_{n+1}, K_{n+1}' \in E_\Gamma(B)$
and $P_{n+1} \in E_\Gamma(K_{n+1} =_B K_{n+1}')$.  Then we have
\begin{align*}
\reff{M}_{N_1 N_2} \reff{N} \vec{P}_{K_{n+1} K_{n+1}l} P_{n+1} & \in E_\Gamma(LK_{n+1} =_C L'K_{n+1}') \\
\therefore \reff{MN} \vec{P}_{K_{n+1} K_{n+1}'} P_{n+1} & \in E_\Gamma(LK_{n+1} =_C L'K_{n+1}')
\end{align*}
by the induction hypothesis, as required.
\end{proof}

\begin{lm}
\label{lm:Egen}
If $\reff{M} \in E_\Gamma(N =_A N')$ then $M \in E_\Gamma(A)$ and $M \simeq_\beta N \simeq_\beta N'$.
\end{lm}

\begin{proof}
The proof is by induction on the type $A$.

If $A \equiv \Omega$: we have $\reff{M} \in \SN$, hence $M \in \SN$.  Also, we have $\Gamma \vdash M : A$ and $M \simeq_\beta N \simeq_\beta N'$
by Generation.

If $A \equiv B \rightarrow C$: we have $\Gamma \vdash M : A$ and $M \simeq_\beta N \simeq_\beta N'$ by Generation again.  Now, let $L \in E_\Gamma(B)$.
Then $\reff{L} \in E_\Gamma(L =_B L)$ by Lemma \ref{lm:Eref}, and so $\reff{M}_{LL} \reff{L} \in E_\Gamma(NL =_C N'L)$.  Therefore,
$\reff{ML} \in E_\Gamma(NL =_C N'L)$ by Lemma \ref{lm:Ered}.  Hence $ML \in E_\Gamma(C)$ by the induction hypothesis, as required.

Now let $L, L' \in E_\Gamma(B)$ and $P \in E_\Gamma(L =_B L')$.  Then similarly $ML, ML' \in E_\Gamma(C)$, and also $\reff{M}_{L L'} P \in E_\Gamma(NL =_C N'L')$.  Hence $\reff{M}_{L L'} P \in E_\Gamma(ML =_C ML')$
by Lemma \ref{lm:conv-compute}, as required.
\end{proof}

\begin{lm}
\label{lm:LM0}
Let $\Gamma, x : A \vdash M : B$ and let $N \in E_\Gamma(A)$.  If $\reff{M[x:=N]} \in E_\Gamma(L =_B L')$, then
$\reff{(\lambda x:A.M)N} \in E_\Gamma(L =_B L')$.
\end{lm}

\begin{proof}
We prove the following stronger statement:

Suppose $\Gamma, x : A \vdash M : B_1 \rightarrow \cdots \rightarrow B_m \rightarrow C_1 \rightarrow \cdots \rightarrow C_n \rightarrow D$.
Let $N \in E_\Gamma(A)$, $N_i \in E_\Gamma(B_i)$, $L_j, L_j' \in E_\Gamma(C_j)$ and $P_j \in E_\Gamma(L_j =_{C_j} L_j')$ for all $i$, $j$.
If $\reff{(M[x:=N] N_1 \cdots N_m}_{L_1 L_1'} (P_1)_{L_2 L_2'} \cdots_{L_n L_n'} P_n \in E_\Gamma(L =_{D} L')$,
then $\reff{((\lambda x:A.M)N N_1 \cdots N_m}_{L_1 L_1'} (P_1)_{L_2 L_2'} \cdots_{L_n L_n'} P_n \in E_\Gamma(L =_{D} L')$.

The proof is by induction on the type $D$.

If $D \equiv \Omega$: it is easy to verify that \\
$\Gamma \vdash (\lambda x:A.M)N N_1 \cdots N_m)_{L_1 L_1'} (P_1)_{L_2 L_2'} \cdots_{L_n L_n'} P_n : L =_{\Omega} L'$ using
Generation.  Lemma \ref{lm:SN}.\ref{lm:SN2} gives that $(\lambda x:A.M)N N_1 \cdots N_m)_{L_1 L_1'} (P_1)_{L_2 L_2'} \cdots_{L_n L_n'} P_n \in \SN$.

If $D \equiv C_{n+1} \rightarrow E$: let $L_{n+1}, L_{n+1}' \in E_\Gamma(C_{n+1})$ and $P_{n+1} \in E_{\Gamma}(L_{n+1} =_{C_{n+1}} L_{n+1}')$.  Then
\begin{align*}
\reff{(M[x:=N] \vec{N}} \vec{P}_{L_{n+1} L_{n+1}'} P_{n+1} & \in E_\Gamma(L L_{n+1} =_{E} L' L_{n+1}') \\
\therefore \reff{((\lambda x:A.M)N \vec{N}} \vec{P}_{L_{n+1} L_{n+1}'} P_{n+1} & \in E_\Gamma(L L_{n+1} =_{E} L' L_{n+1}')
\end{align*}
by the induction hypothesis, as required.
\end{proof}

\begin{lm}
Let $\Gamma, x : A \vdash M : B$ and let $N \in E_\Gamma(A)$.  If $M[x:=N] \in E_\Gamma(B)$ then $(\lambda x:A.M)N \in E_\Gamma(B)$.
\end{lm}

\begin{proof}
We prove the following stronger statement:

Suppose $\Gamma, x : A \vdash M : B_1 \rightarrow \cdots \rightarrow B_n \rightarrow C$.  Let $N \in E_\Gamma(A)$ and $N_i \in E_\Gamma(B_i)$.  If
$M[x:=N]N_1 \cdots N_n \in E_\Gamma(C)$ then $(\lambda x:A.M)NN_1 \cdots N_n \in E_\Gamma(C)$.

The proof is by induction on the type $C$.

If $C \equiv \Omega$: it is easy to verify that $\Gamma \vdash (\lambda x:A.M)NN_1 \cdots N_n : \Omega$.  Lemma \ref{lm:SN}.\ref{lm:SN1}
gives that $(\lambda x:A.M)NN_1 \cdots N_n \in \SN$.

If $C \equiv B_{n+1} \rightarrow D$: let $N_{n+1} \in E_{\Gamma}(B_{n+1})$.  Then
\begin{align*}
M[x:=N]\vec{N} N_{n+1} & \in E_\Gamma(C) \\
\therefore (\lambda x:A.M)N \vec{N} N_{n+1} & \in E_\Gamma(C)
\end{align*}
by the induction hypothesis, as required.

Now let $N_{n+1}, N_{n+1}' \in E_\Gamma(B_{n+1})$ and $P \in E_\Gamma(N_{n+1} =_{B_{n+1}} N_{n+1}')$.  Then
\begin{align*}
\lefteqn{\reff{M[x:=N]\vec{N}}_{N_{n+1} N_{n+1}'} P} \\
\quad & \in E_\Gamma(M[x:=N] \vec{N} N_{n+1} =_C M[x:=N] \vec{N} N_{n+1}') \\
\lefteqn{\therefore \reff{(\lambda x:A.M)N \vec{N}}_{N_{n+1} N_{n+1}'} P} \\
 & \in E_\Gamma(M[x:=N] \vec{N} N_{n+1} =_C M[x:=N] \vec{N} N_{n+1}')
\end{align*}
by the proof of Lemma \ref{lm:LM0}
\begin{align*}
\lefteqn{\therefore \reff{(\lambda x:A.M)N \vec{N}}_{N_{n+1} N_{n+1}'} P} \\
\quad & \in E_\Gamma((\lambda x:A.M)N \vec{N} N_{n+1} =_C (\lambda x:A.M)N \vec{N} N_{n+1}')
\end{align*}
by Lemma \ref{lm:conv-compute}.
\end{proof}

\begin{lm}
Let $\Gamma, x : A \vdash M : B$.  Let $N, N_1, N_2 \in E_\Gamma(A)$, and $N \simeq_\beta N_1 \simeq_\beta N_2$.  If $M[x:=N] \in E_\Gamma(B)$,
then $\reff{\lambda x:A.M}_{N_1 N_2} \reff{N} \in E_\Gamma((\lambda x:A.M)N_1 =_B (\lambda x:A.M) N_2)$.
\end{lm}

\begin{proof}
We prove the following stronger statement.

Suppose $\Gamma, x : A \vdash M : B_1 \rightarrow \cdots \rightarrow B_n \rightarrow C$ and $N, N_1, N_2 \in E_\Gamma(A)$,
$L_i, L_i' \in E_\Gamma(B_i)$ and $P_i \in E_\Gamma(L_i =_{B_i} L_i')$ for all $i$.  If $M[x:=N] \in E_\Gamma(B_1 \rightarrow \cdots \rightarrow B_n \rightarrow C)$,
then $\reff{\lambda x:A.M}_{N_1 N_2} \reff{N}_{L_1 L_1'} P_1 \cdots_{L_n L_n'} P_n \in E_\Gamma((\lambda x:A.M) N_1 L_1 \cdots L_n =_C (\lambda x:A.M) N_2 L_1' \cdots L_n')$.

The proof is by induction on the type $C$.

If $C \equiv \Omega$: it is easy to verify that \\ $\Gamma \vdash \reff{\lambda x:A.M}_{N_1 N_2} \reff{N}_{L_1 L_1'} P_1 \cdots_{L_n L_n'} P_n : (\lambda x:A.M) N_1 L_1 \cdots L_n =_C (\lambda x:A.M) N_2 L_1' \cdots L_n'$.  Lemma \ref{lm:SN}.\ref{lm:SN4} gives that \\
$\reff{\lambda x:A.M}_{N_1 N_2} \reff{N}_{L_1 L_1'} P_1 \cdots_{L_n L_n'} P_n \in \SN$.

If $C \equiv B_{n+1} \rightarrow D$: let $L_{n+1}, L_{n+1}' \in E_\Gamma(B_{n+1})$ and $P_{n+1} \in E_\Gamma(L_{n+1} =_{B_{n+1}} L_{n+1}')$.  Then
\begin{align*}
\lefteqn{\reff{\lambda x:A.M}_{N_1 N_2} \reff{N}_{L_1 L_1'} P_1 \cdots_{L_n L_n'} (P_n)_{L_{n+1} L_{n+1}'} P_{n+1}} \\
\quad &\in E_\Gamma((\lambda x:A.M) N_1 L_1 \cdots L_n L_{n+1} =_C (\lambda x:A.M) N_2 L_1' \cdots L_n'
L_{n+1}')
\end{align*}
by the induction hypothesis, as required.
\end{proof}

\begin{lm}
Let $\Gamma, x : A \vdash M : B$.  Let $N, N' \in E_\Gamma(A)$, $P \in E_\Gamma(N =_A N')$, and suppose:
\begin{enumerate}
\item
$M\{x:=P:N \sim N'\} \in E_\Gamma(M[x:=N] =_B M[x:=N'])$
\item
for all $L \in E_\Gamma(A)$, we have $M[x:=L] \in E_\Gamma(B)$.
\end{enumerate}
Then $\reff{\lambda x:A.M}_{N N'} P \in E_\Gamma((\lambda x:A.M)N =_B (\lambda x:A.M) N')$.
\end{lm}

\begin{proof}
We prove the following stronger statement.

Let $\Gamma, x : A \vdash M : B_1 \rightarrow \cdots \rightarrow B_n \rightarrow C$.  Let $N, N' \in E_\Gamma(A)$; $P \in E_\Gamma(N =_A N')$; $L_i, L_i' \in E_\Gamma(B_i)$ and $Q_i \in E_\Gamma(L_i =_{B_i} L_i')$ for all $i$.  Suppose:
\begin{enumerate}
\item
$M\{x:=P:N \sim N'\}_{L_1 L_1'} Q_1 \cdots_{L_n L_n'} Q_n \in E_\Gamma(M[x:=N]L_1 \cdots L_n =_C
M[x:=N']L_1'\cdots L_n'$
\item
for all $L \in E_\Gamma(A)$, we have $M[x:=L] \in E_\Gamma(B_1 \rightarrow \cdots \rightarrow B_n \rightarrow C)$.
\end{enumerate}
Then $\reff{\lambda x:A.M}_{N N'} P_{L_1 L_1'} Q_1 \cdots_{L_n L_n'} Q_n \in
E_\Gamma((\lambda x:A.M) N L_1 \cdots L_n =_C (\lambda x:A.M) N' L_1' \cdots L_n')$.

The proof is by induction on the type $C$.

If $C \equiv \Omega$: it is easy to verify that $\Gamma \vdash \reff{\lambda x:A.M}_{N N'} P \vec{Q} : (\lambda x:A.M)N \vec{L} =_\Omega (\lambda x:A.M) N' \vec{L'}$.  It remains to show that $\reff{\lambda x:A.M}_{N N'} P \vec{Q} \in \SN$.

If $P$ does not have the form $\reff{-}$, this follows from Lemma \ref{lm:SN}.\ref{lm:SN3}.  If $P \equiv \reff{L}$, then we have $L \in E_\Gamma(A)$ and so $\reff{M[x:=L]} \vec{Q} \in \SN$ by hypothesis.  Therefore, $\reff{\lambda x:A.M}_{N N'} \reff{L} \vec{Q} \in \SN$ by Lemma \ref{lm:SN}.\ref{lm:SN4}.

If $C \equiv B_{n+1} \rightarrow D$: let $L_{n+1}, L_{n+1}' \in E_\Gamma(B_{n+1})$ and $Q_{n+1} \in E_\Gamma(L =_{B_{n+1}} L')$.  Then
\begin{align*}
\lefteqn{M\{x:=P:N \sim N'\} \vec{Q}_{L_{n+1} L_{n+1}'} Q_{n+1}} \\
\quad & \in E_\Gamma(M[x:=N]\vec{L} L_{n+1} =_D M[x:=N'] \vec{L'} L_{n+1}')
\end{align*}
and so the induction hypothesis gives
\begin{align*}
\lefteqn{\reff{\lambda x:A.M}_{N N'} P \vec{Q}_{L_{n+1} L'_{n+1}} Q_{n+1}} \\
\quad & \in E_\Gamma((\lambda x:A.M) N \vec{L} L_{n+1} =_D (\lambda x:A.M) N' \vec{L'} L_{n+1}')
\end{align*}
as required.
\end{proof}

\begin{code}
postulate conv-E' : ∀ {V} {K} {Γ} {A} {B} {M : Expression V (varKind K)} →
                  A ≃ B → E' Γ A M → valid (_,_ {K = K} Γ B) → E' Γ B M
\end{code}

\AgdaHide{
\begin{code}
postulate E'-SN : ∀ {V} {K} {Γ} {A} {M : Expression V (varKind K)} → E' Γ A M → SN M
\end{code}
}

\begin{lm}
\label{lm:var-compute}
Variables are computable.  That is, if $x : T \in \Gamma$ and $\Gamma \vald$, then $x \in E_\Gamma(T)$.
\end{lm}

\begin{code}
postulate var-E' : ∀ {V} {K} {x : Var V K} {Γ : Context V} → E' Γ (typeof x Γ) (var x)
\end{code}

\AgdaHide{
\begin{code}
postulate ⊥-E : ∀ {V} {Γ : Context V} → valid Γ → E' Γ (ty Ω) ⊥

postulate ⊃-E : ∀ {V} {Γ : Context V} {φ} {ψ} → E Γ Ω φ → E Γ Ω ψ → E Γ Ω (φ ⊃ ψ)

postulate appT-E : ∀ {V} {Γ : Context V} {M N : Term V} {A} {B} →
                 valid Γ → E Γ (A ⇛ B) M → E Γ A N → E Γ B (appT M N)

E-typed : ∀ {V} {Γ : Context V} {A} {M} → E Γ A M → Γ ⊢ M ∶ ty A
E-typed = E'-typed

E-SN : ∀ {V} {Γ : Context V} A {M} → E Γ A M → SN M
E-SN _ = E'-SN
--TODO Inline

postulate appP-EP : ∀ {V} {Γ : Context V} {δ ε : Proof V} {φ} {ψ} →
                  EP Γ (φ ⊃ ψ) δ → EP Γ φ ε → EP Γ ψ (appP δ ε)
postulate plus-EP : ∀ {V} {Γ : Context V} {P : Path V} {φ ψ : Term V} →
                  EE Γ (φ ≡〈 Ω 〉 ψ) P → EP Γ (φ ⊃ ψ) (plus P)
postulate minus-EP : ∀ {V} {Γ : Context V} {P : Path V} {φ ψ : Term V} →
                   EE Γ (φ ≡〈 Ω 〉 ψ) P → EP Γ (ψ ⊃ φ) (minus P)

postulate func-EP : ∀ {U} {Γ : Context U} {δ : Proof U} {φ} {ψ} →
                  (∀ V Δ (ρ : Rep U V) (ε : Proof V) → ρ ∶ Γ ⇒R Δ → EP Δ (φ 〈 ρ 〉) ε → EP Δ (ψ 〈 ρ 〉) (appP (δ 〈 ρ 〉) ε)) → 
                  Γ ⊢ δ ∶ φ ⊃ ψ → EP Γ (φ ⊃ ψ) δ

conv-EP : ∀ {V} {Γ : Context V} {φ ψ : Term V} {δ : Proof V} →
          φ ≃ ψ → EP Γ φ δ → Γ ⊢ ψ ∶ ty Ω → EP Γ ψ δ
conv-EP φ≃ψ δ∈EΓφ Γ⊢ψ∶Ω = conv-E' φ≃ψ δ∈EΓφ (ctxPR Γ⊢ψ∶Ω)

EP-typed : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} →
         EP Γ φ δ → Γ ⊢ δ ∶ φ
EP-typed = E'-typed

EP-SN : ∀ {V} {Γ : Context V} {δ} {φ} → EP Γ φ δ → SN δ
EP-SN = E'-SN

postulate ref-EE : ∀ {V} {Γ : Context V} {M : Term V} {A : Type} → E Γ A M → EE Γ (M ≡〈 A 〉 M) (reff M)
postulate ⊃*-EE : ∀ {V} {Γ : Context V} {φ φ' ψ ψ' : Term V} {P Q : Path V} →
                  EE Γ (φ ≡〈 Ω 〉 φ') P → EE Γ (ψ ≡〈 Ω 〉 ψ') Q → EE Γ (φ ⊃ ψ ≡〈 Ω 〉 φ' ⊃ ψ') (P ⊃* Q)
postulate univ-EE : ∀ {V} {Γ : Context V} {φ ψ : Term V} {δ ε : Proof V} →
                  EP Γ (φ ⊃ ψ) δ → EP Γ (ψ ⊃ φ) ε → EE Γ (φ ≡〈 Ω 〉 ψ) (univ φ ψ δ ε)
postulate app*-EE : ∀ {V} {Γ : Context V} {M} {M'} {N} {N'} {A} {B} {P} {Q} →
                  EE Γ (M ≡〈 A ⇛ B 〉 M') P → EE Γ (N ≡〈 A 〉 N') Q →
                  E Γ A N → E Γ A N' →
                  EE Γ (appT M N ≡〈 B 〉 appT M' N') (app* N N' P Q)

postulate func-EE : ∀ {U} {Γ : Context U} {A} {B} {M} {M'} {P} →
                  Γ ⊢ P ∶ M ≡〈 A ⇛ B 〉 M' →
                  (∀ V (Δ : Context V) (N N' : Term V) Q ρ → ρ ∶ Γ ⇒R Δ → 
                  E Δ A N → E Δ A N' → EE Δ (N ≡〈 A 〉 N') Q →
                  EE Δ (appT (M 〈 ρ 〉) N ≡〈 B 〉 appT (M' 〈 ρ 〉) N') (app* N N' (P 〈 ρ 〉) Q)) →
                  EE Γ (M ≡〈 A ⇛ B 〉 M') P

conv-EE : ∀ {V} {Γ : Context V} {M} {N} {M'} {N'} {A} {P} →
          EE Γ (M ≡〈 A 〉 N) P → M ≃ M' → N ≃ N' → Γ ⊢ M' ∶ ty A → Γ ⊢ N' ∶ ty A → 
          EE Γ (M' ≡〈 A 〉 N') P
conv-EE P∈EΓM≡N M≃M' N≃N' Γ⊢M'∶A Γ⊢N'∶A = 
  conv-E' (eq-resp-conv  M≃M' N≃N') P∈EΓM≡N (ctxER Γ⊢M'∶A Γ⊢N'∶A)

EE-typed : ∀ {V} {Γ : Context V} {E} {P} → EE Γ E P → Γ ⊢ P ∶ E
EE-typed = E'-typed

EE-SN : ∀ {V} {Γ : Context V} E {P} → EE Γ E P → SN P
EE-SN _ = E'-SN

{-
postulate Neutral-computeE : ∀ {V} {Γ : Context V} {M} {A} {N} {P : NeutralP V} →
                           Γ ⊢ decode P ∶ M ≡〈 A 〉 N → computeE Γ M A N (decode P)

postulate NF : ∀ {V} {Γ} {φ : Term V} → Γ ⊢ φ ∶ ty Ω → closed-prop

postulate red-NF : ∀ {V} {Γ} {φ : Term V} (Γ⊢φ∶Ω : Γ ⊢ φ ∶ ty Ω) → φ ↠ cp2term (NF Γ⊢φ∶Ω)

postulate closed-rep : ∀ {U} {V} {ρ : Rep U V} (A : closed-prop) → (cp2term A) 〈 ρ 〉 ≡ cp2term A

postulate red-conv : ∀ {V} {C} {K} {E F : Subexpression V C K} → E ↠ F → E ≃ F

postulate confluent : ∀ {V} {φ : Term V} {ψ ψ' : closed-prop} → φ ↠ cp2term ψ → φ ↠ cp2term ψ' → ψ ≡ ψ'

func-EP {δ = δ} {φ = φ} {ψ = ψ} hyp Γ⊢δ∶φ⊃ψ = let Γ⊢φ⊃ψ∶Ω = Prop-Validity Γ⊢δ∶φ⊃ψ in
                      let Γ⊢φ∶Ω = ⊃-gen₁ Γ⊢φ⊃ψ∶Ω in
                      let Γ⊢ψ∶Ω = ⊃-gen₂ Γ⊢φ⊃ψ∶Ω in
                      let φ' = NF Γ⊢φ∶Ω in
                      Γ⊢δ∶φ⊃ψ ,p NF Γ⊢φ∶Ω ⊃C NF Γ⊢ψ∶Ω ,p 
                      trans-red (respects-red {f = λ x → x ⊃ ψ} (λ x → app (appl x)) (red-NF Γ⊢φ∶Ω)) 
                                (respects-red {f = λ x → cp2term (NF Γ⊢φ∶Ω) ⊃ x} (λ x → app (appr (appl x))) (red-NF Γ⊢ψ∶Ω)) ,p  --TODO Extract lemma for reduction
                      (λ W Δ ρ ε ρ∶Γ⇒Δ Δ⊢ε∶φ computeε →
                      let φρ↠φ' : φ 〈 ρ 〉 ↠ cp2term φ'
                          φρ↠φ' = subst (λ x → (φ 〈 ρ 〉) ↠ x) (closed-rep φ') (respects-red (respects-osr replacement β-respects-rep) (red-NF Γ⊢φ∶Ω)) in
                      let ε∈EΔψ = hyp W Δ ρ ε (context-validity Δ⊢ε∶φ) ρ∶Γ⇒Δ        
                                  ((convR Δ⊢ε∶φ (weakening Γ⊢φ∶Ω (context-validity Δ⊢ε∶φ) ρ∶Γ⇒Δ) (sym-conv (red-conv φρ↠φ')) ) ,p φ' ,p φρ↠φ' ,p computeε ) in 
                      let ψ' = proj₁ (proj₂ ε∈EΔψ) in 
                      let ψρ↠ψ' : ψ 〈 ρ 〉 ↠ cp2term ψ'
                          ψρ↠ψ' = proj₁ (proj₂ (proj₂ ε∈EΔψ)) in 
                      subst (λ a → compute Δ a (appP (δ 〈 ρ 〉) ε)) (confluent ψρ↠ψ' 
                        (subst (λ x → (ψ 〈 ρ 〉) ↠ x) (closed-rep (NF Γ⊢ψ∶Ω)) (respects-red (respects-osr replacement β-respects-rep) (red-NF Γ⊢ψ∶Ω)))) 
                        (proj₂ (proj₂ (proj₂ ε∈EΔψ))))

  plus-univ : ∀ {V} {φ ψ : Term V} {δ ε} → key-redex (plus (univ φ ψ δ ε)) δ
  minus-univ : ∀ {V} {φ ψ : Term V} {δ ε} → key-redex (minus (univ φ ψ δ ε)) ε
  imp*-plus : ∀ {V} {P Q : Path V} {δ ε} → key-redex (appP (appP (plus (P ⊃* Q)) δ) ε) (appP (plus Q) (appP δ (appP (minus P) ε)))
  imp*-minus : ∀ {V} {P Q : Path V} {δ ε} → key-redex (appP (appP (minus (P ⊃* Q)) δ) ε) (appP (minus Q) (appP δ (appP (plus P) ε)))
  appPkr : ∀ {V} {δ ε χ : Proof V} → key-redex δ ε → key-redex (appP δ χ) (appP ε χ)
  pluskr : ∀ {V} {P Q : Path V} → key-redex P Q → key-redex (plus P) (plus Q)
  minuskr : ∀ {V} {P Q : Path V} → key-redex P Q → key-redex (minus P) (minus Q)
  app*kr : ∀ {V} {N N' : Term V} {P} {P'} {Q} → key-redex P P' → key-redex (app* N N' P Q) (app* N N' P' Q)
  plus-ref : ∀ {V} {φ : Term V} {δ} → key-redex (appP (plus (reff φ)) δ) δ
  minus-ref : ∀ {V} {φ : Term V} {δ} → key-redex (appP (minus (reff φ)) δ) δ
  app*-ref : ∀ {V} {M N N' : Term V} {Q} → key-redex (app* N N' (reff M) Q) (M ⋆[ Q ∶ N ∼ N' ])

postulate key-redex-SN : ∀ {V} {K} {E F : Expression V K} → key-redex E F → SN F → SN E

postulate key-redex-rep : ∀ {U} {V} {K} {ρ : Rep U V} {E F : Expression U K} → key-redex E F → key-redex (E 〈 ρ 〉) (F 〈 ρ 〉)

postulate ref-compute : ∀ {V} {Γ : Context V} {M : Term V} {A : Type} → E Γ A M → computeE Γ M A M (reff M)

postulate Neutral-E : ∀ {V} {Γ : Context V} {A} {M} → Neutral M → Γ ⊢ M ∶ ty A → E Γ A M

var-E' : ∀ {V} {A} (Γ : Context V) (x : Var V -Term) → 
  valid Γ → typeof x Γ ≡ ty A → E Γ A (var x)
var-E : ∀ {V} (Γ : Context V) (x : Var V -Term) → 
        valid Γ → E Γ (typeof' x Γ) (var x)
computeE-SN : ∀ {V} {Γ : Context V} {M} {N} {A} {P} → computeE Γ M A N P → valid Γ → SN P

computeE-SN {A = Ω} {P} (P+∈EΓM⊃N ,p _) _ = 
  let SNplusP : SN (plus P)
      SNplusP = EP-SN P+∈EΓM⊃N 
  in SNsubbodyl (SNsubexp SNplusP)
computeE-SN {V} {Γ} {A = A ⇛ B} {P} computeP validΓ =
  let x₀∈EΓ,AA : E (Γ ,T A) A (var x₀)
      x₀∈EΓ,AA = var-E' {A = A} (Γ ,T A) x₀ (ctxTR validΓ) refl in
  let SNapp*xxPref : SN (app* (var x₀) (var x₀) (P ⇑) (reff (var x₀)))
      SNapp*xxPref = computeE-SN {A = B} (computeP (V , -Term) (Γ ,T A ) upRep 
          (var x₀) (var x₀) (app -ref (var x₀ ,, out)) upRep-typed 
          (refR (varR x₀ (ctxTR validΓ)) )
          x₀∈EΓ,AA x₀∈EΓ,AA (ref-compute x₀∈EΓ,AA)) 
          (ctxTR validΓ)
  in SNap' {Ops = replacement} {σ = upRep} R-respects-replacement (SNsubbodyl (SNsubbodyr (SNsubbodyr (SNsubexp SNapp*xxPref))))


E-SN (Ω) = EΩ.sn
E-SN {V} {Γ} (A ⇛ B) {M} (Γ⊢M∶A⇛B ,p computeM ,p computeMpath) =
  let SNMx : SN (appT (M ⇑) (var x₀))
      SNMx = E-SN B 
             (computeM (V , -Term) (Γ ,T A) upRep (var x₀) upRep-typed 
             (var-E' {A = A} (Γ ,T A) x₀ (ctxTR (context-validity Γ⊢M∶A⇛B)) refl)) 
  in SNap' {Ops = replacement} {σ = upRep} R-respects-replacement (SNsubbodyl (SNsubexp SNMx)) 

{- Neutral-E {A = Ω} neutralM Γ⊢M∶A = record { 
  typed = Γ⊢M∶A ; 
  sn = Neutral-SN neutralM }
Neutral-E {A = A ⇛ B} {M} neutralM Γ⊢M∶A⇛B = 
  Γ⊢M∶A⇛B ,p 
  (λ W Δ ρ N ρ∶Γ⇒Δ N∈EΔA → Neutral-E {A = B} (app (Neutral-rep M ρ neutralM) (E-SN A N∈EΔA)) 
    (appR (weakening Γ⊢M∶A⇛B (context-validity (E-typed N∈EΔA)) ρ∶Γ⇒Δ) (E-typed N∈EΔA))) ,p 
  (λ W Δ ρ N N' P ρ∶Γ⇒Δ N∈EΔA N'∈EΔA computeP Δ⊢P∶N≡N' → 
    let validΔ = context-validity (E-typed N∈EΔA) in
    Neutral-computeE (Neutral-⋆ (Neutral-rep M ρ neutralM) (computeE-SN computeP validΔ) (E-SN A N∈EΔA) (E-SN A N'∈EΔA)) 
    (⋆-typed (weakening Γ⊢M∶A⇛B validΔ ρ∶Γ⇒Δ) Δ⊢P∶N≡N')) -}

var-E' {A = A} Γ x validΓ x∶A∈Γ = Neutral-E (var x) (change-type (varR x validΓ) x∶A∈Γ)

var-E Γ x validΓ = var-E' {A = typeof' x Γ} Γ x validΓ typeof-typeof'

⊥-E validΓ = record { typed = ⊥R validΓ ; sn = ⊥SN }

⊃-E φ∈EΓΩ ψ∈EΓΩ = record { typed = ⊃R (E-typed φ∈EΓΩ) (E-typed ψ∈EΓΩ) ; 
  sn = ⊃SN (E-SN Ω φ∈EΓΩ) (E-SN Ω ψ∈EΓΩ) }

appT-E {V} {Γ} {M} {N} {A} {B} validΓ (Γ⊢M∶A⇛B ,p computeM ,p computeMpath) N∈EΓA = 
  subst (λ a → E Γ B (appT a N)) rep-idOp (computeM V Γ (idRep V) N idRep-typed N∈EΓA)

postulate cp-typed : ∀ {V} {Γ : Context V} A → valid Γ → Γ ⊢ cp2term A ∶ ty Ω

postulate ⊃-not-⊥ : ∀ {V} {φ ψ : Term V} → φ ⊃ ψ ↠ ⊥ → Empty

postulate ⊃-inj₁ : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ↠ φ' ⊃ ψ' → φ ↠ φ'

postulate ⊃-inj₂ : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ↠ φ' ⊃ ψ' → ψ ↠ ψ'

postulate confluent₂ : ∀ {V} {φ ψ : Term V} {χ : closed-prop} → φ ≃ ψ → φ ↠ cp2term χ → ψ ↠ cp2term χ

appP-EP (_ ,p ⊥C ,p φ⊃ψ↠⊥ ,p _) _ = ⊥-elim (⊃-not-⊥ φ⊃ψ↠⊥)
appP-EP {V} {Γ} {ε = ε} {φ} {ψ = ψ} (Γ⊢δ∶φ⊃ψ ,p (φ' ⊃C ψ') ,p φ⊃ψ↠φ'⊃ψ' ,p computeδ) (Γ⊢ε∶φ ,p φ'' ,p φ↠φ'' ,p computeε) = 
  (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) ,p ψ' ,p ⊃-inj₂ φ⊃ψ↠φ'⊃ψ' ,p 
  subst (λ x → compute Γ ψ' (appP x ε)) rep-idOp 
  (computeδ V Γ (idRep V) ε idRep-typed 
    (convR Γ⊢ε∶φ (cp-typed φ' (context-validity Γ⊢ε∶φ)) (red-conv (⊃-inj₁ φ⊃ψ↠φ'⊃ψ')))
  (subst (λ x → compute Γ x ε) (confluent φ↠φ'' (⊃-inj₁ φ⊃ψ↠φ'⊃ψ')) computeε))

conv-EP φ≃ψ (Γ⊢δ∶φ ,p φ' ,p φ↠φ' ,p computeδ) Γ⊢ψ∶Ω = convR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ ,p φ' ,p confluent₂ {χ = φ'} φ≃ψ φ↠φ' ,p computeδ


postulate rep-EP : ∀ {U} {V} {Γ} {Δ} {ρ : Rep U V} {φ} {δ} →
                 EP Γ φ δ → ρ ∶ Γ ⇒R Δ → EP Δ (φ 〈 ρ 〉) (δ 〈 ρ 〉)

univ-EE {V} {Γ} {φ} {ψ} {δ} {ε} δ∈EΓφ⊃ψ ε∈EΓψ⊃φ = 
  let Γ⊢univ∶φ≡ψ : Γ ⊢ univ φ ψ δ ε ∶ φ ≡〈 Ω 〉 ψ
      Γ⊢univ∶φ≡ψ = (univR (EP-typed δ∈EΓφ⊃ψ) (EP-typed ε∈EΓψ⊃φ)) in
      (Γ⊢univ∶φ≡ψ ,p 
      expand-EP δ∈EΓφ⊃ψ (plusR Γ⊢univ∶φ≡ψ) plus-univ ,p 
      expand-EP ε∈EΓψ⊃φ (minusR Γ⊢univ∶φ≡ψ) minus-univ)

postulate rep-EE : ∀ {U} {V} {Γ} {Δ} {ρ : Rep U V} {E} {P} →
                 EE Γ E P → ρ ∶ Γ ⇒R Δ → EE Δ (E 〈 ρ 〉) (P 〈 ρ 〉)

imp*-EE {Γ = Γ} {φ} {φ'} {ψ = ψ} {ψ'} {P} {Q = Q} P∈EΓφ≡φ' Q∈EΓψ≡ψ' = (⊃*R (EE-typed P∈EΓφ≡φ') (EE-typed Q∈EΓψ≡ψ')) ,p 
  func-EP (λ V Δ ρ ε validΔ ρ∶Γ⇒RΔ ε∈EΔφ⊃ψ →
    let Pρ : EE Δ (φ 〈 ρ 〉 ≡〈 Ω 〉 φ' 〈 ρ 〉) (P 〈 ρ 〉)
        Pρ = rep-EE P∈EΓφ≡φ' ρ∶Γ⇒RΔ in
    let Qρ : EE Δ (ψ 〈 ρ 〉 ≡〈 Ω 〉 ψ' 〈 ρ 〉) (Q 〈 ρ 〉)
        Qρ = rep-EE Q∈EΓψ≡ψ' ρ∶Γ⇒RΔ in
    func-EP (λ W Θ σ χ validΘ σ∶Δ⇒RΘ χ∈EΘφ' → 
    let Pρσ : EE Θ (φ 〈 ρ 〉 〈 σ 〉 ≡〈 Ω 〉 φ' 〈 ρ 〉 〈 σ 〉) (P 〈 ρ 〉 〈 σ 〉)
        Pρσ = rep-EE Pρ σ∶Δ⇒RΘ in
    let Pρσ- : EP Θ (φ' 〈 ρ 〉 〈 σ 〉 ⊃ φ 〈 ρ 〉 〈 σ 〉) (minus (P 〈 ρ 〉 〈 σ 〉))
        Pρσ- = minus-EP Pρσ in
    let Qρσ : EE Θ (ψ 〈 ρ 〉 〈 σ 〉 ≡〈 Ω 〉 ψ' 〈 ρ 〉 〈 σ 〉) (Q 〈 ρ 〉 〈 σ 〉)
        Qρσ = rep-EE Qρ σ∶Δ⇒RΘ in
    let Qρσ+ : EP Θ (ψ 〈 ρ 〉 〈 σ 〉 ⊃ ψ' 〈 ρ 〉 〈 σ 〉) (plus (Q 〈 ρ 〉 〈 σ 〉))
        Qρσ+ = plus-EP Qρσ in
    let εσ : EP Θ (φ 〈 ρ 〉 〈 σ 〉 ⊃ ψ 〈 ρ 〉 〈 σ 〉) (ε 〈 σ 〉)
        εσ = rep-EP ε∈EΔφ⊃ψ σ∶Δ⇒RΘ in
    expand-EP 
    (appP-EP Qρσ+ (appP-EP εσ (appP-EP Pρσ- χ∈EΘφ')))
    (appPR (appPR (plusR (⊃*R (EE-typed Pρσ) (EE-typed Qρσ))) (EP-typed εσ)) (EP-typed χ∈EΘφ')) 
    imp*-plus) 
    (appPR (plusR (⊃*R (EE-typed Pρ) (EE-typed Qρ))) (EP-typed ε∈EΔφ⊃ψ))) 
  (plusR (⊃*R (EE-typed P∈EΓφ≡φ') (EE-typed Q∈EΓψ≡ψ'))) ,p 
  func-EP (λ V Δ ρ ε validΔ ρ∶Γ⇒RΔ ε∈EΔφ'⊃ψ' →
    let Pρ : EE Δ (φ 〈 ρ 〉 ≡〈 Ω 〉 φ' 〈 ρ 〉) (P 〈 ρ 〉)
        Pρ = rep-EE P∈EΓφ≡φ' ρ∶Γ⇒RΔ in
    let Qρ : EE Δ (ψ 〈 ρ 〉 ≡〈 Ω 〉 ψ' 〈 ρ 〉) (Q 〈 ρ 〉)
        Qρ = rep-EE Q∈EΓψ≡ψ' ρ∶Γ⇒RΔ in
    func-EP (λ W Θ σ χ validΘ σ∶Δ⇒RΘ χ∈EΘφ' → 
      let Pρσ : EE Θ (φ 〈 ρ 〉 〈 σ 〉 ≡〈 Ω 〉 φ' 〈 ρ 〉 〈 σ 〉) (P 〈 ρ 〉 〈 σ 〉)
          Pρσ = rep-EE Pρ σ∶Δ⇒RΘ in
      let Pρσ+ : EP Θ (φ 〈 ρ 〉 〈 σ 〉 ⊃ φ' 〈 ρ 〉 〈 σ 〉) (plus (P 〈 ρ 〉 〈 σ 〉))
          Pρσ+ = plus-EP Pρσ in
      let Qρσ : EE Θ (ψ 〈 ρ 〉 〈 σ 〉 ≡〈 Ω 〉 ψ' 〈 ρ 〉 〈 σ 〉) (Q 〈 ρ 〉 〈 σ 〉)
          Qρσ = rep-EE Qρ σ∶Δ⇒RΘ in
      let Qρσ- : EP Θ (ψ' 〈 ρ 〉 〈 σ 〉 ⊃ ψ 〈 ρ 〉 〈 σ 〉) (minus (Q 〈 ρ 〉 〈 σ 〉))
          Qρσ- = minus-EP Qρσ in
      let εσ : EP Θ (φ' 〈 ρ 〉 〈 σ 〉 ⊃ ψ' 〈 ρ 〉 〈 σ 〉) (ε 〈 σ 〉)
          εσ = rep-EP ε∈EΔφ'⊃ψ' σ∶Δ⇒RΘ in 
      expand-EP 
        (appP-EP Qρσ- (appP-EP εσ (appP-EP Pρσ+ χ∈EΘφ'))) 
          (appPR (appPR (minusR (⊃*R (EE-typed Pρσ) (EE-typed Qρσ))) (EP-typed εσ)) (EP-typed χ∈EΘφ')) 
        imp*-minus)
    (appPR (minusR (⊃*R (EE-typed Pρ) (EE-typed Qρ))) (EP-typed ε∈EΔφ'⊃ψ'))) 
  (minusR (⊃*R (EE-typed P∈EΓφ≡φ') (EE-typed Q∈EΓψ≡ψ')))

app*-EE {V} {Γ} {M} {M'} {N} {N'} {A} {B} {P} {Q} (Γ⊢P∶M≡M' ,p computeP) (Γ⊢Q∶N≡N' ,p computeQ) N∈EΓA N'∈EΓA = (app*R (E-typed N∈EΓA) (E-typed N'∈EΓA) Γ⊢P∶M≡M' Γ⊢Q∶N≡N') ,p 
  subst₃
    (λ a b c →
       computeE Γ (appT a N) B (appT b N') (app* N N' c Q))
    rep-idOp rep-idOp rep-idOp 
    (computeP V Γ (idRep V) N N' Q idRep-typed Γ⊢Q∶N≡N' 
      N∈EΓA N'∈EΓA computeQ)

func-EE {U} {Γ} {A} {B} {M} {M'} {P} Γ⊢P∶M≡M' hyp = Γ⊢P∶M≡M' ,p (λ W Δ ρ N N' Q ρ∶Γ⇒Δ Δ⊢Q∶N≡N' N∈EΔA N'∈EΔA computeQ → 
  proj₂ (hyp W Δ N N' Q ρ ρ∶Γ⇒Δ N∈EΔA N'∈EΔA (Δ⊢Q∶N≡N' ,p computeQ)))

ref-EE {V} {Γ} {M} {A} M∈EΓA = refR (E-typed M∈EΓA) ,p ref-compute M∈EΓA

expand-EE {V} {Γ} {A} {M} {N} {P} {Q} (Γ⊢Q∶M≡N ,p computeQ) Γ⊢P∶M≡N P▷Q = Γ⊢P∶M≡N ,p expand-computeE computeQ Γ⊢P∶M≡N P▷Q

postulate ⊃-respects-conv : ∀ {V} {φ} {φ'} {ψ} {ψ' : Term V} → φ ≃ φ' → ψ ≃ ψ' →
                          φ ⊃ ψ ≃ φ' ⊃ ψ'

postulate appT-respects-convl : ∀ {V} {M M' N : Term V} → M ≃ M' → appT M N ≃ appT M' N

conv-computeE : ∀ {V} {Γ : Context V} {M} {M'} {N} {N'} {A} {P} →
             computeE Γ M A N P → M ≃ M' → N ≃ N' → 
             Γ ⊢ M' ∶ ty A  → Γ ⊢ N' ∶ ty A  →
             computeE Γ M' A N' P
conv-computeE {M = M} {A = Ω} 
  (EPΓM⊃NP+ ,p EPΓN⊃MP-) M≃M' N≃N' Γ⊢M'∶Ω Γ⊢N'∶Ω = 
  (conv-EP (⊃-respects-conv M≃M' N≃N')
    EPΓM⊃NP+ (⊃R Γ⊢M'∶Ω Γ⊢N'∶Ω)) ,p 
  conv-EP (⊃-respects-conv N≃N' M≃M') EPΓN⊃MP- (⊃R Γ⊢N'∶Ω Γ⊢M'∶Ω)
conv-computeE {M = M} {M'} {N} {N'} {A = A ⇛ B} computeP M≃M' N≃N' Γ⊢M'∶A⇛B Γ⊢N'∶A⇛B =
  λ W Δ ρ L L' Q ρ∶Γ⇒RΔ Δ⊢Q∶L≡L' L∈EΔA L'∈EΔA computeQ → conv-computeE {A = B} 
  (computeP W Δ ρ L L' Q ρ∶Γ⇒RΔ Δ⊢Q∶L≡L' L∈EΔA L'∈EΔA computeQ) 
  (appT-respects-convl (respects-conv (respects-osr replacement β-respects-rep) M≃M')) 
  (appT-respects-convl (respects-conv (respects-osr replacement β-respects-rep) N≃N')) 
  (appR (weakening Γ⊢M'∶A⇛B (context-validity Δ⊢Q∶L≡L') ρ∶Γ⇒RΔ) (E-typed {W} {Γ = Δ} {A = A} {L} L∈EΔA)) 
  (appR (weakening Γ⊢N'∶A⇛B (context-validity Δ⊢Q∶L≡L') ρ∶Γ⇒RΔ) (E-typed L'∈EΔA)) 
--REFACTOR Duplication

conv-EE (Γ⊢P∶M≡N ,p computeP) M≃M' N≃N' Γ⊢M'∶A Γ⊢N'∶A = convER Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N' ,p conv-computeE computeP M≃M' N≃N' Γ⊢M'∶A Γ⊢N'∶A
--REFACTOR Duplication                      
                 
EE-SN (app (-eq _) (_ ,, _ ,, out)) (Γ⊢P∶E ,p computeP) = computeE-SN computeP (context-validity Γ⊢P∶E) -}
\end{code}
}
