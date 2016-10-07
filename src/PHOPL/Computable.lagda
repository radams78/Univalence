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
open import PHOPL.KeyRedex2
\end{code}

\section{Computable Expressions}

We define a model of the type theory with types as sets of terms.  For every type (proposition, equation) $T$ in context $\Gamma$, define
the set of \emph{computable} terms (proofs, paths) $E_\Gamma(T)$.

\begin{definition}[Neutral]
A term is \emph{neutral} iff it has the form $x M_1 \cdots M_n$, where each $M_i$ is in normal form.
\end{definition}

\begin{code}
postulate Nf : Alphabet → Set

data Neutral (V : Alphabet) : Set where
  var : Var V -Term → Neutral V
  app : Neutral V → Nf V → Neutral V
\end{code}

\AgdaHide{
\begin{code}
postulate nrep : ∀ {U V} → Rep U V → Neutral U → Neutral V

postulate decode-Neutral : ∀ {V} → Neutral V → Term V

postulate neutral-red : ∀ {V} {N : Neutral V} {M} → decode-Neutral N ↠ M →
                      Σ[ N' ∈ Neutral V ] decode-Neutral N' ≡ M
\end{code}
}

Note that (using Generation) a normal form of type $\Omega$ is either $\bot$, or a neutral term, or $\phi \supset \psi$ where $\phi$ and $\psi$ are normal forms of type $\Omega$.

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
\end{code}
}

\newcommand{\ldot}{\, . \,}
\begin{definition}[Computable Expressions]
\label{df:computable}
\begin{align*}
E_\Gamma(\chi) \eqdef \{ \delta \mid & \Gamma \vdash \delta : \chi \text{ and } \delta \in \SN \} \\
& \qquad (\chi \text{ is neutral or } \bot) \\
E_\Gamma(\phi \supset \psi) \eqdef \{ \delta \mid & \Gamma \vdash \delta : \phi \supset \psi\text{ and } \\
& \forall \Delta \supseteq \Gamma \ldot \forall \epsilon \in E_\Delta(\phi)\ldot \delta \epsilon \in E_\Gamma(\psi) \} \\
& \qquad (\phi , \psi \text{ normal forms}) \\
E_\Gamma(\phi) \eqdef \{ \delta \mid & \Gamma \vdash \delta : \phi\text{ and } \delta \in \SN \} \\
& \qquad (\phi \text{ neutral}) \\
E_\Gamma(\phi) \eqdef \{ \delta \mid & \Gamma \vdash \delta : \phi\text{ and } \delta \in E_\Gamma(\nf{\phi}) \} \\
& \qquad (\phi \text{ a weakly normalizable term}) \\
\\
E_\Gamma(\Omega) \eqdef \{ M \mid & \Gamma \vdash M : \Omega\text{ and } M \in \SN\text{ and } \\
& M \{\} \in E_\Gamma(M =_\Omega M) \} \\
E_\Gamma(A \rightarrow B) \eqdef \{ M \mid & \Gamma \vdash M : A \rightarrow B\text{ and } \\
& \forall \Delta \supseteq \Gamma\ldot \forall N \in E_\Delta(A)\ldot MN \in E_\Delta(B)\text{ and } \\
& M \{\} \in E_\Gamma(M =_{A \rightarrow B} M) \} \\
\\
E_\Gamma(\phi =_\Omega \psi) \eqdef \{ P \mid & \Gamma \vdash P : \phi =_\Omega \psi\text{ and } \\
& P^+ \in E_\Gamma(\phi \supset \psi)\text{ and } P^- \in E_\Gamma(\psi \supset \phi) \} \\
& \qquad (\phi , \psi \text{ weakly normalizable terms}) \\
\\
E_\Gamma(M =_{A \rightarrow B} M') \eqdef \{ P \mid & \Gamma \vdash P : M =_{A \rightarrow B} M'\text{ and } \\
& \forall \Delta \supseteq \Gamma\ldot \forall N, N' \in E_\Delta(A)\ldot \forall Q \in E_\Delta(N =_A N')\ldot \\
& P_{NN'}Q \in E_\Delta(MN =_B M'N') \}
\end{align*}
\end{definition}

\AgdaHide{
\begin{code}
Enf : ∀ {V} {S} → Context V → Leaves V S → Proof V → Set
Enf {S = neutral} Γ (neutral φ) δ = Γ ⊢ δ ∶ decode-Neutral φ × SN δ
Enf {S = bot} Γ bot δ = Γ ⊢ δ ∶ ⊥ × SN δ
Enf {S = imp S T} Γ (imp φ ψ) δ = Γ ⊢ δ ∶ decode-Prop φ ⊃ decode-Prop ψ ×
  ∀ {W} (Δ : Context W) {ρ} {ε}
  (ρ∶Γ⇒RΔ : ρ ∶ Γ ⇒R Δ) (Δ⊢ε∶φ : Δ ⊢ ε ∶ (decode-Prop (lrep ρ φ)))
  (computeε : Enf {S = S} Δ (lrep ρ φ) ε) → 
  Enf {S = T} Δ (lrep ρ ψ) (appP (δ 〈 ρ 〉) ε)

EP : ∀ {V} → Context V → Term V → Proof V → Set
EP {V} Γ φ δ = Σ[ S ∈ Shape ] Σ[ L ∈ Leaves V S ] φ ↠ decode-Prop L × Enf Γ L δ

ET : ∀ {V} → Context V → Type → Term V → Set
EE : ∀ {V} → Context V → Term V → Type → Term V → Path V → Set

ET Γ Ω M = SN M
ET Γ (A ⇛ B) M = 
  (∀ {W} (Δ : Context W) {ρ} {N} (ρ∶Γ⇒Δ : ρ ∶ Γ ⇒R Δ) (Δ⊢N∶A : Δ ⊢ N ∶ ty A) (computeN : ET Δ A N) →
    ET Δ B (appT (M 〈 ρ 〉) N)) ×
  (∀ {W} (Δ : Context W) {ρ} {N} {N'} {P} 
    (ρ∶Γ⇒Δ : ρ ∶ Γ ⇒R Δ) (Δ⊢P∶N≡N' : Δ ⊢ P ∶ N ≡〈 A 〉 N') 
    (computeN : ET Δ A N) (computeN' : ET Δ A N') (computeP : EE Δ N A N' P) →
    EE Δ (appT (M 〈 ρ 〉) N) B (appT (M 〈 ρ 〉) N') (M 〈 ρ 〉 ⋆[ P ∶ N ∼ N' ]))

EE {V} Γ M Ω N P = Σ[ S ∈ Shape ] Σ[ T ∈ Shape ] Σ[ L ∈ Leaves V S ] Σ[ L' ∈ Leaves V T ] M ↠ decode-Prop L × N ↠ decode-Prop L' × Enf Γ (imp L L') (plus P) × Enf Γ (imp L' L) (minus P)
EE Γ M (A ⇛ B) M' P =
  ∀ {W} (Δ : Context W) {ρ} {N} {N'} {Q} (ρ∶Γ⇒RΔ : ρ ∶ Γ ⇒R Δ) (Δ⊢Q∶N≡N' : Δ ⊢ Q ∶ N ≡〈 A 〉 N')
  (computeQ : EE Δ N A N' Q) → EE Δ (appT (M 〈 ρ 〉) N) B (appT (M' 〈 ρ 〉)  N') 
    (app* N N' (P 〈 ρ 〉) Q)
\end{code}
}

If $\phi$ is a term that is not weakly normalizable, then $E_\Gamma(\phi)$ is undefined.  Similarly, $E_\Gamma(\phi =_\Omega \psi)$ is undefined if $\phi$ and $\psi$ are
not both weakly normalizable.

Note that each $E_\Gamma(T)$ is closed under reduction, and that, if $\Gamma \subseteq \Delta$, then $E_\Gamma(T) \subseteq E_\Delta(T)$.  Note also that, if $M \in E_\Gamma(A)$,
then $M \{\} \in E_\Gamma(M =_A M)$.  

\AgdaHide{
\begin{code}

Enf-red : ∀ {V S Γ} {L : Leaves V S} {δ ε} → Enf Γ L δ → δ ⇒ ε → Enf Γ L ε
Enf-red {L = neutral _} (Γ⊢δ∶φ ,p δSN) δ⇒ε = 
  Subject-Reduction Γ⊢δ∶φ (osr-red δ⇒ε) ,p 
  SNred δSN (osr-red δ⇒ε)
Enf-red {L = bot} (Γ⊢δ∶⊥ ,p SNδ) δ⇒ε = (Subject-Reduction Γ⊢δ∶⊥ (osr-red δ⇒ε)) ,p (SNred SNδ (osr-red δ⇒ε)) -- TODO Refactor Subject-Reduction o osr-red
Enf-red {L = imp φ ψ} {δ} {ε} (Γ⊢δ∶φ⊃ψ ,p computeδ) δ⇒ε = (Subject-Reduction Γ⊢δ∶φ⊃ψ (osr-red δ⇒ε)) ,p 
  (λ Δ {ρ} {θ} ρ∶Γ⇒RΔ Δ⊢θ∶φ computeε → subst (λ χ → Enf Δ χ (appP (ε 〈 ρ 〉) θ)) {!!} (computeδ Δ {ρ} {θ} ρ∶Γ⇒RΔ Δ⊢θ∶φ))

{- postulate compute-SN : ∀ {V} {Γ : Context V} {A} {δ} → ET Γ A δ → valid Γ → SN δ

postulate decode-rep : ∀ {U} {V} {S} (L : Leaves U S) {ρ : Rep U V} →
                     decode-Prop (lrep ρ L) ≡ decode-Prop L 〈 ρ 〉

postulate conv-Enf : ∀ {V} {Γ : Context V} {S} {L M : Leaves V S} {δ} →
                        Enf Γ L δ → decode-Prop L ≃ decode-Prop M →
                        Γ ⊢ decode-Prop M ∶ ty Ω → Enf Γ M δ

{- conv-EE : ∀ {V} {Γ : Context V} {M} {M'} {A} {N} {N'} {P} →
  EE Γ M A N P → 
  Γ ⊢ M ∶ ty A → Γ ⊢ N ∶ ty A → Γ ⊢ M' ∶ ty A → Γ ⊢ N' ∶ ty A → M ≃ M' → N ≃ N' →
  EE Γ M' A N' P
conv-EE {Γ = Γ} {M = M} {M' = M'} {A = Ω} {N' = N'} {P} (S ,p T ,p φ ,p ψ ,p M↠φ ,p N↠ψ ,p Enf+ ,p Enf-) 
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
      let step3 : Enf Δ (lrep ρ φ) ε
          step3 = conv-Enf {L = lrep ρ φ'} {M = lrep ρ φ} computeε step1a step1 in
      let step4 : Enf Δ (lrep ρ ψ) (appP (plus P 〈 ρ 〉) ε)
          step4 = Enf+ Δ ρ∶Γ⇒RΔ step2 step3 in 
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
      conv-Enf {L = lrep ρ ψ} {M = lrep ρ ψ'} step4 (sym-conv step5) step6) ,p 
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
      let step3 : Enf Δ (lrep ρ ψ) ε
          step3 = conv-Enf {L = lrep ρ ψ'} {M = lrep ρ ψ} computeε step1a step1 in
      let step4 : Enf Δ (lrep ρ φ) (appP (minus P 〈 ρ 〉) ε)
          step4 = Enf- Δ ρ∶Γ⇒RΔ step2 step3 in 
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
      conv-Enf {L = lrep ρ φ} {M = lrep ρ φ'} step4 (sym-conv step5) step6))
conv-EE {A = A ⇛ B} Enf Γ⊢M∶A Γ⊢N∶A Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N' Δ ρ∶Γ⇒RΔ Δ⊢Q∶N≡N' computeQ = 
  conv-EE {A = B} 
  (Enf Δ ρ∶Γ⇒RΔ Δ⊢Q∶N≡N' computeQ) 
    (appR (weakening Γ⊢M∶A (context-validity Δ⊢Q∶N≡N') ρ∶Γ⇒RΔ) 
      (Equation-Validity₁ Δ⊢Q∶N≡N')) 
    (appR (weakening Γ⊢N∶A (context-validity Δ⊢Q∶N≡N') ρ∶Γ⇒RΔ) 
      (Equation-Validity₂ Δ⊢Q∶N≡N'))
    (appR (weakening Γ⊢M'∶A (context-validity Δ⊢Q∶N≡N') ρ∶Γ⇒RΔ) (Equation-Validity₁ Δ⊢Q∶N≡N')) 
    (appR (weakening Γ⊢N'∶A (context-validity Δ⊢Q∶N≡N') ρ∶Γ⇒RΔ) (Equation-Validity₂ Δ⊢Q∶N≡N')) 
    (appT-convl (conv-rep M≃M')) (appT-convl (conv-rep N≃N')) -}
--TODO Common pattern

{- expand-ET {A = Ω} computeψ _ SNM φ▷ψ = SNM
expand-ET {A = A ⇛ B} {M} {M'} (computeM'app ,p computeM'eq) Γ⊢M∶A⇛B SNM M▷M' = 
  (λ Δ {ρ} {N} ρ∶Γ⇒Δ Δ⊢N∶A computeN → 
    let computeM'N : ET Δ B (appT (M' 〈 ρ 〉) N)
        computeM'N = computeM'app Δ ρ∶Γ⇒Δ Δ⊢N∶A computeN in
    let validΔ : valid Δ
        validΔ = context-validity Δ⊢N∶A in
    expand-ET computeM'N 
    (appR (weakening Γ⊢M∶A⇛B validΔ ρ∶Γ⇒Δ) Δ⊢N∶A)
    (expand-lemma (SNrep R-creates-rep SNM) 
         (key-redex-rep M▷M') (compute-SN computeM'N validΔ))
         (appTkr (key-redex-rep M▷M'))) ,p 
  (λ Δ {ρ} {N} {N'} ρ∶Γ⇒Δ Δ⊢P∶N≡N' computeN computeN' Enf₁ → 
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
    expand-EE 
      (conv-EE 
        (computeM'eq Δ ρ∶Γ⇒Δ Δ⊢P∶N≡N' computeN computeN' Enf₁) 
        (appR Δ⊢M'ρ∶A⇛B Δ⊢N∶A) 
        (appR Δ⊢M'ρ∶A⇛B Δ⊢N'∶A)
        (appR Δ⊢Mρ∶A⇛B Δ⊢N∶A) 
        (appR Δ⊢Mρ∶A⇛B Δ⊢N'∶A)
        (M'ρX≃MρX N) (M'ρX≃MρX N'))
      (⋆-typed Δ⊢Mρ∶A⇛B Δ⊢P∶N≡N') 
      (key-redex-⋆ (key-redex-rep M▷M'))) -}

compute : ∀ {V} {K} → Context V → Expression V (parent K) → Expression V (varKind K) → Set
compute {K = -Term} Γ (app (-ty A) out) M = ET Γ A M
compute {V} {K = -Proof} Γ φ δ = Σ[ S ∈ Shape ] Σ[ L ∈ Leaves V S ] φ ↠ decode-Prop L × Enf Γ L δ
compute {K = -Path} Γ (app (-eq A) (M ∷ N ∷ [])) P = EE Γ M A N P

record E' {V} {K} (Γ : Context V) (A : Expression V (parent K)) (E : Expression V (varKind K)) : Set where
  constructor E'I
  field
    typed : Γ ⊢ E ∶ A
    computable : compute Γ A E

--TODO Inline the following?
E : ∀ {V} → Context V → Type → Term V → Set
E Γ A M = E' Γ (ty A) M

E'-typed : ∀ {V} {K} {Γ : Context V} {A} {M : Expression V (varKind K)} → 
           E' Γ A M → Γ ⊢ M ∶ A
E'-typed = E'.typed

postulate func-E : ∀ {U} {Γ : Context U} {M : Term U} {A} {B} →
                   (∀ V Δ (ρ : Rep U V) (N : Term V) → valid Δ → ρ ∶ Γ ⇒R Δ → E Δ A N → E Δ B (appT (M 〈 ρ 〉) N)) →
                   E Γ (A ⇛ B) M
\end{code}
}

\begin{code}
postulate conv-E' : ∀ {V} {K} {Γ} {A} {B} {M : Expression V (varKind K)} →
                  A ≃ B → E' Γ A M → valid (_,_ {K = K} Γ B) → E' Γ B M
\end{code}

\AgdaHide{
\begin{code}
postulate E'-SN : ∀ {V} {K} {Γ} {A} {M : Expression V (varKind K)} → E' Γ A M → SN M
\end{code}
}

\begin{code}
postulate var-E' : ∀ {V} {K} {x : Var V K} {Γ : Context V} → E' Γ (typeof x Γ) (var x)
\end{code}

\AgdaHide{
\begin{code}
postulate ⊥-E : ∀ {V} {Γ : Context V} → valid Γ → E' Γ (ty Ω) ⊥

postulate ⊃-E : ∀ {V} {Γ : Context V} {φ} {ψ} → E Γ Ω φ → E Γ Ω ψ → E Γ Ω (φ ⊃ ψ)

E-typed : ∀ {V} {Γ : Context V} {A} {M} → E Γ A M → Γ ⊢ M ∶ ty A
E-typed = E'-typed

E-SN : ∀ {V} {Γ : Context V} A {M} → E Γ A M → SN M
E-SN _ = E'-SN
--TODO Inline

appT-E : ∀ {V} {Γ : Context V} {M N : Term V} {A} {B} →
         valid Γ → E Γ (A ⇛ B) M → E Γ A N → E Γ B (appT M N)
appT-E {V} {Γ} {M} {N} {A} {B} validΓ (E'I Γ⊢M∶A⇛B (Mcompute ,p Mcompute-eq)) (E'I Γ⊢N∶A Ncompute) = 
  E'I (appR Γ⊢M∶A⇛B Γ⊢N∶A) (subst (λ x → ET Γ B (appT x N)) rep-idRep (Mcompute Γ idRep-typed Γ⊢N∶A Ncompute))

postulate appP-EP : ∀ {V} {Γ : Context V} {δ ε : Proof V} {φ} {ψ} →
                  EP Γ (φ ⊃ ψ) δ → EP Γ φ ε → EP Γ ψ (appP δ ε)
postulate plus-EP : ∀ {V} {Γ : Context V} {P : Path V} {φ ψ : Term V} →
                  EE Γ φ Ω ψ P → EP Γ (φ ⊃ ψ) (plus P)
postulate minus-EP : ∀ {V} {Γ : Context V} {P : Path V} {φ ψ : Term V} →
                   EE Γ φ Ω ψ P → EP Γ (ψ ⊃ φ) (minus P)

postulate func-EP : ∀ {U} {Γ : Context U} {δ : Proof U} {φ} {ψ} →
                  (∀ V Δ (ρ : Rep U V) (ε : Proof V) → ρ ∶ Γ ⇒R Δ → EP Δ (φ 〈 ρ 〉) ε → EP Δ (ψ 〈 ρ 〉) (appP (δ 〈 ρ 〉) ε)) → 
                  Γ ⊢ δ ∶ φ ⊃ ψ → EP Γ (φ ⊃ ψ) δ

conv-EP : ∀ {V} {Γ : Context V} {φ ψ : Term V} {δ : Proof V} →
          φ ≃ ψ → EP Γ φ δ → Γ ⊢ ψ ∶ ty Ω → EP Γ ψ δ
conv-EP φ≃ψ δ∈EΓφ Γ⊢ψ∶Ω = {!!}

EP-typed : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} →
         EP Γ φ δ → Γ ⊢ δ ∶ φ
EP-typed = {!!}

EP-SN : ∀ {V} {Γ : Context V} {δ} {φ} → EP Γ φ δ → SN δ
EP-SN = {!!}

postulate ref-EE : ∀ {V} {Γ : Context V} {M : Term V} {A : Type} → E Γ A M → EE Γ M A M (reff M)
postulate ⊃*-EE : ∀ {V} {Γ : Context V} {φ φ' ψ ψ' : Term V} {P Q : Path V} →
                  EE Γ φ Ω φ' P → EE Γ ψ Ω ψ' Q → EE Γ (φ ⊃ ψ) Ω (φ' ⊃ ψ') (P ⊃* Q)
postulate univ-EE : ∀ {V} {Γ : Context V} {φ ψ : Term V} {δ ε : Proof V} →
                  EP Γ (φ ⊃ ψ) δ → EP Γ (ψ ⊃ φ) ε → EE Γ φ Ω ψ (univ φ ψ δ ε)
postulate app*-EE : ∀ {V} {Γ : Context V} {M} {M'} {N} {N'} {A} {B} {P} {Q} →
                  EE Γ M (A ⇛ B) M' P → EE Γ N A N' Q →
                  E Γ A N → E Γ A N' →
                  EE Γ (appT M N) B (appT M' N') (app* N N' P Q)

postulate func-EE : ∀ {U} {Γ : Context U} {A} {B} {M} {M'} {P} →
                  Γ ⊢ P ∶ M ≡〈 A ⇛ B 〉 M' →
                  (∀ V (Δ : Context V) (N N' : Term V) Q ρ → ρ ∶ Γ ⇒R Δ → 
                  E Δ A N → E Δ A N' → EE Δ N A N' Q →
                  EE Δ (appT (M 〈 ρ 〉) N) B (appT (M' 〈 ρ 〉) N') (app* N N' (P 〈 ρ 〉) Q)) →
                  EE Γ M (A ⇛ B) M' P -}

{-
postulate Neutral-EE : ∀ {V} {Γ : Context V} {M} {A} {N} {P : NeutralP V} →
                           Γ ⊢ decode P ∶ M ≡〈 A 〉 N → EE Γ M A N (decode P)

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

postulate ref-compute : ∀ {V} {Γ : Context V} {M : Term V} {A : Type} → E Γ A M → EE Γ M A M (reff M)

postulate Neutral-E : ∀ {V} {Γ : Context V} {A} {M} → Neutral M → Γ ⊢ M ∶ ty A → E Γ A M

var-E' : ∀ {V} {A} (Γ : Context V) (x : Var V -Term) → 
  valid Γ → typeof x Γ ≡ ty A → E Γ A (var x)
var-E : ∀ {V} (Γ : Context V) (x : Var V -Term) → 
        valid Γ → E Γ (typeof' x Γ) (var x)
EE-SN : ∀ {V} {Γ : Context V} {M} {N} {A} {P} → EE Γ M A N P → valid Γ → SN P

EE-SN {A = Ω} {P} (P+∈EΓM⊃N ,p _) _ = 
  let SNplusP : SN (plus P)
      SNplusP = EP-SN P+∈EΓM⊃N 
  in SNsubbodyl (SNsubexp SNplusP)
EE-SN {V} {Γ} {A = A ⇛ B} {P} Enf validΓ =
  let x₀∈EΓ,AA : E (Γ ,T A) A (var x₀)
      x₀∈EΓ,AA = var-E' {A = A} (Γ ,T A) x₀ (ctxTR validΓ) refl in
  let SNapp*xxPref : SN (app* (var x₀) (var x₀) (P ⇑) (reff (var x₀)))
      SNapp*xxPref = EE-SN {A = B} (Enf (V , -Term) (Γ ,T A ) upRep 
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
  (λ W Δ ρ N N' P ρ∶Γ⇒Δ N∈EΔA N'∈EΔA Enf Δ⊢P∶N≡N' → 
    let validΔ = context-validity (E-typed N∈EΔA) in
    Neutral-EE (Neutral-⋆ (Neutral-rep M ρ neutralM) (EE-SN Enf validΔ) (E-SN A N∈EΔA) (E-SN A N'∈EΔA)) 
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

app*-EE {V} {Γ} {M} {M'} {N} {N'} {A} {B} {P} {Q} (Γ⊢P∶M≡M' ,p Enf) (Γ⊢Q∶N≡N' ,p computeQ) N∈EΓA N'∈EΓA = (app*R (E-typed N∈EΓA) (E-typed N'∈EΓA) Γ⊢P∶M≡M' Γ⊢Q∶N≡N') ,p 
  subst₃
    (λ a b c →
       EE Γ (appT a N) B (appT b N') (app* N N' c Q))
    rep-idOp rep-idOp rep-idOp 
    (Enf V Γ (idRep V) N N' Q idRep-typed Γ⊢Q∶N≡N' 
      N∈EΓA N'∈EΓA computeQ)

func-EE {U} {Γ} {A} {B} {M} {M'} {P} Γ⊢P∶M≡M' hyp = Γ⊢P∶M≡M' ,p (λ W Δ ρ N N' Q ρ∶Γ⇒Δ Δ⊢Q∶N≡N' N∈EΔA N'∈EΔA computeQ → 
  proj₂ (hyp W Δ N N' Q ρ ρ∶Γ⇒Δ N∈EΔA N'∈EΔA (Δ⊢Q∶N≡N' ,p computeQ)))

ref-EE {V} {Γ} {M} {A} M∈EΓA = refR (E-typed M∈EΓA) ,p ref-compute M∈EΓA

expand-EE {V} {Γ} {A} {M} {N} {P} {Q} (Γ⊢Q∶M≡N ,p computeQ) Γ⊢P∶M≡N P▷Q = Γ⊢P∶M≡N ,p expand-EE computeQ Γ⊢P∶M≡N P▷Q

postulate ⊃-respects-conv : ∀ {V} {φ} {φ'} {ψ} {ψ' : Term V} → φ ≃ φ' → ψ ≃ ψ' →
                          φ ⊃ ψ ≃ φ' ⊃ ψ'

postulate appT-respects-convl : ∀ {V} {M M' N : Term V} → M ≃ M' → appT M N ≃ appT M' N

conv-EE : ∀ {V} {Γ : Context V} {M} {M'} {N} {N'} {A} {P} →
             EE Γ M A N P → M ≃ M' → N ≃ N' → 
             Γ ⊢ M' ∶ ty A  → Γ ⊢ N' ∶ ty A  →
             EE Γ M' A N' P
conv-EE {M = M} {A = Ω} 
  (EPΓM⊃NP+ ,p EPΓN⊃MP-) M≃M' N≃N' Γ⊢M'∶Ω Γ⊢N'∶Ω = 
  (conv-EP (⊃-respects-conv M≃M' N≃N')
    EPΓM⊃NP+ (⊃R Γ⊢M'∶Ω Γ⊢N'∶Ω)) ,p 
  conv-EP (⊃-respects-conv N≃N' M≃M') EPΓN⊃MP- (⊃R Γ⊢N'∶Ω Γ⊢M'∶Ω)
conv-EE {M = M} {M'} {N} {N'} {A = A ⇛ B} Enf M≃M' N≃N' Γ⊢M'∶A⇛B Γ⊢N'∶A⇛B =
  λ W Δ ρ L L' Q ρ∶Γ⇒RΔ Δ⊢Q∶L≡L' L∈EΔA L'∈EΔA computeQ → conv-EE {A = B} 
  (Enf W Δ ρ L L' Q ρ∶Γ⇒RΔ Δ⊢Q∶L≡L' L∈EΔA L'∈EΔA computeQ) 
  (appT-respects-convl (respects-conv (respects-osr replacement β-respects-rep) M≃M')) 
  (appT-respects-convl (respects-conv (respects-osr replacement β-respects-rep) N≃N')) 
  (appR (weakening Γ⊢M'∶A⇛B (context-validity Δ⊢Q∶L≡L') ρ∶Γ⇒RΔ) (E-typed {W} {Γ = Δ} {A = A} {L} L∈EΔA)) 
  (appR (weakening Γ⊢N'∶A⇛B (context-validity Δ⊢Q∶L≡L') ρ∶Γ⇒RΔ) (E-typed L'∈EΔA)) 
--REFACTOR Duplication

conv-EE (Γ⊢P∶M≡N ,p Enf) M≃M' N≃N' Γ⊢M'∶A Γ⊢N'∶A = convER Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N' ,p conv-EE Enf M≃M' N≃N' Γ⊢M'∶A Γ⊢N'∶A
--REFACTOR Duplication                      
                 
EE-SN (app (-eq _) (_ ,, _ ,, out)) (Γ⊢P∶E ,p Enf) = EE-SN Enf (context-validity Γ⊢P∶E) -}
\end{code}
}

