\AgdaHide{
\begin{code}
module PHOPL.Computable where
import Relation.Binary.PreorderReasoning
open import Data.Empty renaming (⊥ to Empty)
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Data.List hiding (all)
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.PathSub
open import PHOPL.Red
open import PHOPL.Red.Confluent
open import PHOPL.Rules
open import PHOPL.Meta
\end{code}
}

\section{Computable Expressions}

We define a model of the type theory with types as sets of terms.  For every type (proposition, equation) $T$ in context $\Gamma$, define
the set of \emph{computable} terms (proofs, paths) $E_\Gamma(T)$.

\input{PHOPL/Computable/Meaning}
\AgdaHide{
\begin{code}
open import PHOPL.Computable.Meaning public
\end{code}
}

\newcommand{\ldot}{\, . \,}
\begin{definition}[Computable Expressions]
\label{df:computable}
\begin{align*}
E_\Gamma(\chi) \eqdef \{ \delta \mid & \Gamma \vdash \delta : \chi\text{ and } \delta \in \SN \} \\
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

If $\phi$ is a term that is not weakly normalizable, then $E_\Gamma(\phi)$ is undefined.  Similarly, $E_\Gamma(\phi =_\Omega \psi)$ is undefined if $\phi$ and $\psi$ are
not both weakly normalizable.

The Agda code for this definition is shown in Figure \ref{fig:compute}

\begin{figure}
\begin{code}
computeP : ∀ {V S} → Context V → Meaning V S → Proof V → Set
computeP Γ (nf₀ _) δ = SN δ
computeP Γ (φ imp ψ) δ = 
  ∀ {W} (Δ : Context W) {ρ} {ε}
  (ρ∶Γ⇒RΔ : ρ ∶ Γ ⇒R Δ) (Δ⊢ε∶φ : Δ ⊢ ε ∶ (decode-Meaning (nfrep φ ρ)))
  (computeε : computeP Δ (nfrep φ ρ) ε) → 
  computeP Δ (nfrep ψ ρ) (appP (δ 〈 ρ 〉) ε)

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

computeE {V} Γ M Ω N P = Σ[ S ∈ MeaningShape ] Σ[ φ ∈ Meaning V S ] Σ[ ψ ∈ Meaning V S ] M ↠ decode-Meaning φ × N ↠ decode-Meaning ψ × computeP Γ (φ imp ψ) (plus P) × computeP Γ (ψ imp φ) (minus P)
computeE Γ M (A ⇛ B) M' P =
  ∀ {W} (Δ : Context W) {ρ} {N} {N'} {Q} (ρ∶Γ⇒RΔ : ρ ∶ Γ ⇒R Δ) (Δ⊢Q∶N≡N' : Δ ⊢ Q ∶ N ≡〈 A 〉 N')
  (computeN : computeT Δ A N) (computeN' : computeT Δ A N') (computeQ : computeE Δ N A N' Q) → computeE Δ (appT (M 〈 ρ 〉) N) B (appT (M' 〈 ρ 〉)  N') 
    (app* N N' (P 〈 ρ 〉) Q)

compute : ∀ {V} {K} → Context V → Expression V (parent K) → Expression V (varKind K) → Set
compute {K = -Term} Γ (app (-ty A) out) M = computeT Γ A M
compute {V} {K = -Proof} Γ φ δ = Σ[ S ∈ MeaningShape ] Σ[ ψ ∈ Meaning V S ] φ ↠ decode-Meaning ψ × computeP Γ ψ δ
compute {K = -Path} Γ (app (-eq A) (M ∷ N ∷ [])) P = computeE Γ M A N P

record E {V} {K} (Γ : Context V) (A : Expression V (parent K)) (M : Expression V (varKind K)) : Set where
  constructor EI
  field
    typed : Γ ⊢ M ∶ A
    computable : compute Γ A M

allE : ∀ {V} (Γ : Context V) {SS} → ListMeaning V SS → List (Proof V) → Set
allE {V} Γ {SS} φφ pp = all (λ {φ} {(φ , δ) → E Γ (decode-Meaning φ) δ}) SS (zip φφ pp)
\end{code}
\caption{Agda definition of the computable expressions}
\label{fig:compute}
\end{figure}

\begin{lemma}
Every strongly normalizable term is weakly normalizable.
\end{lemma}

%TODO Agda

\begin{lemma}
If $M, N \in E_\Gamma(A)$ then $E_\Gamma(M =_A N)$ is defined.
\end{lemma}

\begin{proof}
The proof is by induction on $A$.

If $M, N \in E_\Gamma(\Omega)$ then $M$ and $N$ are strongly nomalizable, hence weakly normalizable, hence $E_\Gamma(M =_A N)$ is defined.

If $M, M' \in E_\Gamma(A \rightarrow B)$, then let $\Delta \supseteq \Gamma$ and $N, N' \in E_\Gamma(A)$.  We have that $MN, M'N' \in E_\Gamma(B)$,
and so $E_\Delta(N =_A N')$ and $E_\Delta(MN =_B M'N')$ are both defined by the induction hypothesis.
\end{proof}

%TODO Agda

Note that, if $\Gamma \subseteq \Delta$, then $E_\Gamma(T) \subseteq E_\Delta(T)$.  Note also that, if $M \in E_\Gamma(A)$,
then $M \{\} \in E_\Gamma(M =_A M)$. %TODO Agda

\AgdaHide{
\begin{code}
postulate computeP-rep : ∀ {U V S Γ Δ} {ρ : Rep U V} {L : Meaning U S} {δ} →
                       computeP Γ L δ → ρ ∶ Γ ⇒R Δ → computeP Δ (nfrep L ρ) (δ 〈 ρ 〉)
{- computeP-rep {S = neutral} {L = neutral _} computeδ _ = SNrep R-creates-rep computeδ
computeP-rep {S = bot} {L = bot} computeδ ρ∶Γ⇒RΔ = SNrep R-creates-rep computeδ
computeP-rep {S = imp S T} {ρ = ρ} {L = imp φ ψ} {δ} computeδ ρ∶Γ⇒RΔ Θ {ρ'} {ε} ρ'∶Δ⇒RΘ Θ⊢ε∶φ computeε = 
  subst₂ (computeP Θ) (let open ≡-Reasoning in 
  begin
    nfrep ψ (ρ' •R ρ)
  ≡⟨ nfrep-comp ⟩
    nfrep (nfrep ψ ρ) ρ'
  ∎) 
  (cong (λ x → appP x ε) (rep-comp δ)) 
  (computeδ Θ (compR-typed ρ'∶Δ⇒RΘ ρ∶Γ⇒RΔ) 
    (change-type Θ⊢ε∶φ 
      (cong decode-Prop {x = nfrep (nfrep φ ρ) ρ'} (Prelims.sym nfrep-comp))) 
    (subst (λ x → computeP Θ x ε) {x = nfrep (nfrep φ ρ) ρ'} (Prelims.sym nfrep-comp) computeε)) -}

postulate compute-rep : ∀ {U V Γ Δ} {ρ : Rep U V} {K} {A : Expression U (parent K)} {M : Expression U (varKind K)} → 
                      E Γ A M → ρ ∶ Γ ⇒R Δ → valid Δ → compute Δ (A 〈 ρ 〉) (M 〈 ρ 〉)
{- compute-rep {V = V} {ρ = ρ} {K = -Proof} {φ} {M} (EI typed (S ,p L ,p φ↠L ,p computeM)) ρ∶Γ⇒RΔ validΔ = S ,p nfrep L ρ ,p 
  red-decode-rep L φ↠L ,p
  computeP-rep {ρ = ρ} {L} {δ = M} computeM ρ∶Γ⇒RΔ
compute-rep {K = -Term} {app (-ty Ω) []} (EI _ SNM) _ _ = SNrep R-creates-rep SNM
compute-rep {K = -Term} {app (-ty (φ ⇛ ψ)) []} {δ} (EI Γ⊢δ∶φ⊃ψ (δapp ,p δeq)) ρ∶Γ⇒RΔ validΔ = (λ {W} Θ {ρ'} {ε} ρ'∶Δ⇒RΘ Θ⊢ε∶φ computeε → 
  subst (computeT Θ ψ) (cong (λ x → appT x ε) (rep-comp δ)) (δapp Θ (compR-typed ρ'∶Δ⇒RΘ ρ∶Γ⇒RΔ) Θ⊢ε∶φ computeε)) ,p 
  (λ Θ {ρ'} {ε} {ε'} {P} ρ'∶Δ⇒RΘ Θ⊢P∶ε≡ε' computeε computeε' computeP → subst
    (λ a → computeE Θ (appT a ε) ψ (appT a ε') (a ⋆[ P ∶ ε ∼ ε' ]))
    (rep-comp δ) 
    (δeq Θ (compR-typed ρ'∶Δ⇒RΘ ρ∶Γ⇒RΔ) Θ⊢P∶ε≡ε' computeε computeε' computeP))
compute-rep {V = V} {ρ = ρ} {K = -Path} {app (-eq Ω) (φ ∷ ψ ∷ [])} {P} (EI Γ⊢P∶φ≡ψ (S ,p S' ,p L ,p L' ,p φ↠L ,p ψ↠L' ,p computeP+ ,p computeP- )) ρ∶Γ⇒RΔ validΔ = 
  S ,p S' ,p nfrep L ρ ,p nfrep L' ρ ,p 
  red-decode-rep L φ↠L ,p
  red-decode-rep L' ψ↠L' ,p 
  (λ Θ {ρ'} {ε} ρ'∶Δ⇒RΘ Θ⊢ε∶Lρρ' computeε → subst₂ (λ a b → computeP Θ a (appP (plus b) ε)) {nfrep L' (ρ' •R ρ)}
                                              {nfrep (nfrep L' ρ) ρ'} {P 〈 ρ' •R ρ 〉} {(P 〈 ρ 〉) 〈 ρ' 〉} 
  nfrep-comp (rep-comp P) (computeP+ Θ (compR-typed ρ'∶Δ⇒RΘ ρ∶Γ⇒RΔ) 
    (change-type Θ⊢ε∶Lρρ' (cong decode-Prop {nfrep (nfrep L ρ) ρ'} {nfrep L (ρ' •R ρ)} (Prelims.sym nfrep-comp))) 
    (subst (λ a → computeP Θ a ε) {nfrep (nfrep L ρ) ρ'}
       {nfrep L (ρ' •R ρ)} (Prelims.sym nfrep-comp) computeε))) ,p 
  (λ Θ {ρ'} {ε} ρ'∶Δ⇒RΘ Θ⊢ε∶L'ρρ' computeε → subst₂ (λ a b → computeP Θ a (appP (minus b) ε)) {nfrep L (ρ' •R ρ)}
                                              {nfrep (nfrep L ρ) ρ'} {P 〈 ρ' •R ρ 〉} {(P 〈 ρ 〉) 〈 ρ' 〉} 
  nfrep-comp (rep-comp P) (computeP- Θ (compR-typed ρ'∶Δ⇒RΘ ρ∶Γ⇒RΔ) 
    (change-type Θ⊢ε∶L'ρρ' (cong decode-Prop {nfrep (nfrep L' ρ) ρ'} {nfrep L' (ρ' •R ρ)} (Prelims.sym nfrep-comp))) 
    (subst (λ a → computeP Θ a ε) {nfrep (nfrep L' ρ) ρ'}
       {nfrep L' (ρ' •R ρ)} (Prelims.sym nfrep-comp) computeε)))
--TODO Tidy up this proof
compute-rep {K = -Path} {app (-eq (A ⇛ B)) (F ∷ G ∷ [])} {P} (EI Γ⊢P∶F≡G computeP) ρ∶Γ⇒RΔ validΔ Θ {ρ'} {N} {N'} {Q} ρ'∶Δ⇒RΘ Θ⊢Q∶N≡N' computeN computeN' computeQ = 
  subst₃
    (λ a b c → computeE Θ (appT a N) B (appT b N') (app* N N' c Q)) 
    (rep-comp F) (rep-comp G) (rep-comp P) 
    (computeP Θ (compR-typed ρ'∶Δ⇒RΘ ρ∶Γ⇒RΔ) Θ⊢Q∶N≡N' computeN computeN' computeQ) -}
\end{code}
}

\begin{code}
postulate E-rep : ∀ {U V Γ Δ} {ρ : Rep U V} {K} {A : Expression U (parent K)} {M : Expression U (varKind K)} → 
                E Γ A M → ρ ∶ Γ ⇒R Δ → valid Δ → E Δ (A 〈 ρ 〉) (M 〈 ρ 〉)
\end{code}

\AgdaHide{
\begin{code}
--E-rep (EI Γ⊢M∶A computeM) ρ∶Γ⇒RΔ validΔ = EI (weakening Γ⊢M∶A validΔ ρ∶Γ⇒RΔ) (compute-rep (EI Γ⊢M∶A computeM) ρ∶Γ⇒RΔ validΔ)
\end{code}
}

\begin{lemma}
\label{lm:varcompute1}
Let $\phi$ be a weakly normalizable term.
\begin{enumerate}
\item
If $\Gamma \vald$, $φ$ is weakly normalizable and $p : \phi \in \Gamma$ then $p \in E_\Gamma(\phi)$.

\begin{code}
var-EP : ∀ {V S} {L : Meaning V S} {Γ : Context V} {p : Var V -Proof} → 
         valid Γ → typeof p Γ ↠ decode-Meaning L → E Γ (typeof p Γ) (var p)

postulate E-varP : ∀ {V} {Γ : Context V} {p : Var V -Proof} → valid Γ → E Γ (ty Ω) (typeof p Γ) → E Γ (typeof p Γ) (var p)
\end{code}

\item
$E_\Gamma(\phi) \subseteq \SN$.

\begin{code}
E-SNP : ∀ {V} {Γ : Context V} {φ : Term V} {δ : Proof V} → E Γ φ δ → SN δ
\end{code}
\end{enumerate}
\end{lemma}

\begin{proof}
The two parts are proved simultaneously by induction on $\nf{\phi}$.
\AgdaHide{
\begin{code}
postulate var-computeP : ∀ {V S} {Γ : Context V} {L : Meaning V S} {p : Var V -Proof} → computeP Γ L (var p)
postulate computeP-SN : ∀ {V S} {Γ : Context V} (L : Meaning V S) {δ : Proof V} → computeP Γ L δ → valid Γ → SN δ

--var-computeP = {!!}
--computeP-SN = {!!}
\end{code}
}

Let $\nf{\phi} \equiv \psi_1 \supset \cdots \supset \psi_n \supset \chi$,
where $\chi$ is either $\bot$ or a neutral term.  
\begin{enumerate}
\item
Let $\Delta \supseteq \Gamma$ and $\epsilon_i \in E_\Delta(\psi_i)$ for
each $i$.
We must show that
\[ p \epsilon_1 \cdots \epsilon_n \in E_\Delta(\chi) \]
\begin{code}
computeP-wd : ∀ {V S T Γ} {φ : Meaning V S} {ψ : Meaning V T} {δ} → computeP Γ φ δ → decode-Meaning φ ≡ decode-Meaning ψ → computeP Γ ψ δ
computeP-wd {S = nf₀} {nf₀} {φ = nf₀ _} {nf₀ _} computeδ _ = computeδ
computeP-wd {S = nf₀} {_ imp _} {φ = nf₀ (neutral (app _ _))} {_ imp _} _ ()
computeP-wd {S = nf₀} {_ imp _} {φ = nf₀ bot} {_ imp _} _ ()
computeP-wd {S = S imp S₁} {nf₀} {φ = _ imp _} {nf₀ (neutral (app _ _))}_ ()
computeP-wd {S = S imp S₁} {nf₀} {φ = _ imp _} {nf₀ bot} _ ()
computeP-wd {S = S imp S'} {T imp T'} {φ = φ imp ψ} {φ' imp ψ'} computeδ φ≡ψ Δ {ρ} ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε = 
  let φ'ρ≡φρ : decode-Meaning (nfrep φ' ρ) ≡ decode-Meaning (nfrep φ ρ)
      φ'ρ≡φρ = let open ≡-Reasoning in
        begin
          decode-Meaning (nfrep φ' ρ)
        ≡⟨ decode-Meaning-rep φ' ⟩
          decode-Meaning φ' 〈 ρ 〉
        ≡⟨⟨ rep-congl (⊃-injl φ≡ψ) ⟩⟩
          decode-Meaning φ 〈 ρ 〉
        ≡⟨⟨ decode-Meaning-rep φ ⟩⟩
          decode-Meaning (nfrep φ ρ)
        ∎ in
  computeP-wd {S = S'} {T'} {φ = nfrep ψ ρ} {nfrep ψ' ρ} (computeδ Δ ρ∶Γ⇒RΔ 
    (change-type Δ⊢ε∶φ φ'ρ≡φρ)
    (computeP-wd {S = T} {S} {φ = nfrep φ' ρ} {nfrep φ ρ} computeε φ'ρ≡φρ)) 
  (let open ≡-Reasoning in
    begin
      decode-Meaning (nfrep ψ ρ)
    ≡⟨ decode-Meaning-rep ψ ⟩
      decode-Meaning ψ 〈 ρ 〉
    ≡⟨ rep-congl (⊃-injr φ≡ψ) ⟩
      decode-Meaning ψ' 〈 ρ 〉
    ≡⟨⟨ decode-Meaning-rep ψ' ⟩⟩
      decode-Meaning (nfrep ψ' ρ)
    ∎)

postulate Enf : ∀ {V Γ S} {φ : Meaning V S} {δ} → E Γ (decode-Meaning φ) δ → computeP Γ φ δ

EPropE : ∀ {V S} {Γ : Context V} {φ : Meaning V S} {δ} {εε} →
                 computeP Γ φ δ → allE Γ (domMeaning φ) εε → SN (APPP' δ εε)
EPropE {φ = nf₀ _} computeδ [] = computeδ
EPropE {V} {S imp T} {Γ = Γ} {φ = φ imp ψ} {δ} {εε = ε ∷ εε} computeδ (Eε ∷ Eεε) = 
  EPropE {Γ = Γ} {φ = ψ} {appP δ ε} {εε} 
  (subst₂ (λ a b → computeP Γ a (appP b ε)) nfrep-id rep-idRep 
    (computeδ Γ idRep-typed 
      (change-type (E.typed Eε) (cong decode-Meaning {φ} (Prelims.sym nfrep-id)))
      (subst (λ x → computeP Γ x ε) (Prelims.sym nfrep-id) (Enf Eε)))) 
  Eεε

EPropI : ∀ {V} {Γ : Context V} {S} {φ : Meaning V S} {δ} → valid Γ →
                 (∀ {W} {Δ : Context W} {ρ} {εε} → ρ ∶ Γ ⇒R Δ → valid Δ → allE Δ (listnfrep (domMeaning φ) ρ) εε → SN (APPP' (δ 〈 ρ 〉) εε)) →
                 computeP Γ φ δ
EPropI {φ = nf₀ N} validΓ hyp = subst SN rep-idRep (hyp idRep-typed validΓ [])
EPropI {φ = φ imp ψ} {δ} validΓ hyp Δ {ρ} {ε} ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε = EPropI {φ = nfrep ψ ρ} (context-validity Δ⊢ε∶φ)
  (λ {W'} {Θ} {σ} {εε} σ∶Δ⇒RΘ validΘ Eεε → subst (λ a → SN (APPP' (appP a (ε 〈 σ 〉)) εε)) 
  (rep-comp δ) (hyp {εε = ε 〈 σ 〉 ∷ εε} (•R-typed σ∶Δ⇒RΘ ρ∶Γ⇒RΔ) validΘ 
    (subst (λ a → E Θ a (ε 〈 σ 〉)) (let open ≡-Reasoning in 
      begin
        decode-Meaning (nfrep φ ρ) 〈 σ 〉
      ≡⟨⟨ decode-Meaning-rep (nfrep φ ρ) ⟩⟩
        decode-Meaning (nfrep (nfrep φ ρ) σ)
      ≡⟨⟨ cong decode-Meaning (nfrep-comp {M = φ}) ⟩⟩
        decode-Meaning (nfrep φ (σ •R ρ ))
      ∎) 
      (E-rep (EI Δ⊢ε∶φ (_ ,p nfrep φ ρ ,p ref ,p computeε)) σ∶Δ⇒RΘ validΘ) 
    ∷ subst (λ x → allE Θ x εε) (let open ≡-Reasoning in 
    begin
      listnfrep (domMeaning (nfrep ψ ρ)) σ
    ≡⟨ cong (λ a → listnfrep a σ) domMeaning-rep ⟩
      listnfrep (listnfrep (domMeaning ψ) ρ) σ
    ≡⟨⟨ listnfrep-comp ⟩⟩
      listnfrep (domMeaning ψ) (σ •R ρ)
    ∎) 
    Eεε)))
-- TODO Swap arguments in •R-typed
\end{code}
It is easy to see that $p \vec{\epsilon}$ is well-typed, so it remains to show that $p \vec{\epsilon} \in \SN$.
This holds because each $\epsilon_i$ is strongly normalizing by the induction hypothesis (2).
\item
Let $\delta \in E_\Gamma(\phi)$.  Consider the context $\Delta \equiv \Gamma, p_1 : \psi_1, \ldots, p_n : \psi_n$.
By the induction hypothesis (1), we have that $p_i \in E_\Delta(\psi_i)$, hence
$\delta p_1 \cdots p_n \in E_\Gamma(\chi)$, and so $\delta p_1 \cdots p_n \in \SN$.
It follows that $\delta \in \SN$.
\end{enumerate}
\AgdaHide{
\begin{code}
var-EP {S = S} {L} {p = p} validΓ φ↠L = EI (varR p validΓ) (S ,p L ,p φ↠L ,p var-computeP {S = S})

E-SNP (EI Γ⊢δ∶φ (S ,p L ,p _ ,p computeδ)) = computeP-SN L computeδ (context-validity Γ⊢δ∶φ)
\end{code}
}
\end{proof}

\begin{lemma}
\label{lm:varcompute2}
Let $A$ be a type.
\begin{enumerate}
\item
If $\Gamma \vald$ and $x : A \in \Gamma$ then $x \in E_\Gamma(A)$.

\begin{code}
postulate E-varT : ∀ {V} {Γ : Context V} {x : Var V -Term} → valid Γ → E Γ (typeof x Γ) (var x)
\end{code}
\item
$E_\Gamma(A) \subseteq \SN$.

\begin{code}
postulate E-SNT : ∀ {V} {Γ : Context V} {A} {M : Term V} → E Γ (ty A) M → SN M
\end{code}
\item
If $\Gamma \vald$ and $e : M =_A N \in \Gamma$ and $M, N \in E_\Gamma(A)$ then $e \in E_\Gamma(M =_A N)$.

\begin{code}
E-eq : ∀ {V} → Context V → Equation V → Set
E-eq Γ (app (-eq A) (M ∷ N ∷ [])) = E Γ (ty A) M × E Γ (ty A) N

postulate E-varE : ∀ {V} {Γ : Context V} {x : Var V -Path} → valid Γ → E-eq Γ (typeof x Γ) → E Γ (typeof x Γ) (var x)
\end{code}
\item
For all $M, N \in E_\Gamma(A)$, we have $E_\Gamma(M =_A N) \subseteq \SN$.

\begin{code}
postulate E-SNE : ∀ {V} {Γ : Context V} {Eq : Equation V} {P : Path V} → E Γ Eq P → SN P

postulate E-SN : ∀ {V} {Γ : Context V} {K} {A : Expression V (parent K)} {M : Expression V (varKind K)} → E Γ A M → SN M
\end{code}
\end{enumerate}
\end{lemma}

\begin{proof}
The four parts are proved simultaneously by induction on $A$.  Let $A \equiv A_1 \rightarrow \cdots \rightarrow A_n \rightarrow \Omega$,
and suppose the lemma holds for each $A_i$.
\begin{enumerate}
\item
Let $\Delta \supseteq \Gamma$.  We must prove the following:
\begin{enumerate}
\item
Given $M_i \in E_\Delta(A_i)$ for $1 \leq i \leq n$, we must show that $x M_1 \cdots M_n \in E_\Delta(\Omega)$.  We have that
each $M_i \in \SN$ by the induction hypothesis, hence $x \vec{M} \in \SN$.

Now, let $\delta \in E_\Delta(x \vec{M})$.  We must show that $(x \vec{M}) \{\} ^+ \delta \in E_\Delta(x \vec{M})$,
i.e. $(\reff{x}_{M_1 M_1} M_1 \{\}_{M_2 M_2} \cdots_{M_n M_n} M_n\{\})^+ \delta \in E_\Delta(x \vec{M})$.
Well-typedness is easy, and strong normalization follows from the fact that each $M_i$ and $M_i \{\}$ is strongly
normalizing by the induction hypothesis (2) and (4).  (Note that $\reff{x}$ cannot be part of a redex, as it is not closed.)
\item
Given $M_i \in E_\Delta(A_i)$ for $1 \leq i \leq k$, and $N_j, N_j' \in E_\Delta(A_j)$ and $P_j \in E_\Delta(M_j =_{A_j} N_j)$ for
$k < j \leq n$, we must show that \\
$(x M_1 \cdots M_k)\{\}_{N_{k+1}N_{k+1}'} (P_{k+1})_{N_{k+2}N_{k+2}'} \cdots_{N_n N_n'} P_n \in E_\Delta(x \vec{M} \vec{N} =_\Omega x \vec{M} \vec{N'})$,
i.e.
\begin{align*}
(\reff{x}_{M_1 M_1} M_1\{\} \cdots_{M_k M_k} M_k\{\}_{M_{k+1} N_{k+1}} P_{k+1} \cdots_{M_n N_n} P_n)^+ \\
\in E_\Delta(x \vec{M} \vec{N} \supset x \vec{M} \vec{N'}) \\
(\reff{x}_{M_1 M_1} M_1\{\} \cdots_{M_k M_k} M_k\{\}_{M_{k+1} N_{k+1}} P_{k+1} \cdots_{M_n N_n} P_n)^- \\
\in E_\Delta(x \vec{M} \vec{N'} \supset x \vec{M} \vec{N})
\end{align*}
The proof is similar to the previous part.
\end{enumerate}
\item
Let $M \in E_\Gamma(A)$.  Then using the induction hypothesis $M x_1 \cdots x_n \in E_{\Gamma, x_1 : A_1, \ldots, x_n : A_n}(\Omega) \subseteq \SN$,
hence $M \in \SN$.
\item
Let $\Delta \supseteq \Gamma$.  Let $L_i, L_i' \in E_\Delta(A_i)$ and
$P_i \in E_\Delta(L_i =_{A_i} L_i')$ for $i = 1, \ldots, n$.  We must show that
$e \vec{P} \equiv e_{L_1 L_1'} P_1 \cdots_{L_n L_n'} P_n \in E_\Delta(M L_1 \cdots L_n =_{\Omega} N L_1' \cdots L_n')$, i.e. that
\begin{align*}
(e \vec{P})^+ \in E_\Delta(M \vec{L} \supset N \vec{L'}) \\
(e \vec{P})^- \in E_\Delta(N \vec{L'} \supset M \vec{L})
\end{align*}
We prove the first of these; the second is similar.

Let $\Theta \supseteq \Delta$.  Let $\delta \in E_\Theta(M \vec{L})$.
Let $\nf{N \vec{L'}} \equiv \phi_1 \supset \cdots \supset \phi_m \supset \chi$,
where $\chi$ is $\bot$ or neutral.  (We know $\nf{N \vec{L'}}$ exists because
$N \vec{L'} \in E_\Delta(\Omega)$.)  Let $\epsilon_j \in E_\Theta(\phi_j)$ for
$j = 1, \ldots, m$.  Then we must show that
\[ (e \vec{P})^+ \delta \epsilon_1 \cdots \epsilon_m \in E_\Theta(\chi) \]
Well-typedness is easy to show, so it remains to show $(e \vec{P})^+ \delta \vec{\epsilon} \in \SN$.  This holds as each $P_i$, $\delta$ and $\epsilon_j$ is
strongly normalizing.
\item
Let $P \in E_\Gamma(M =_A N)$.  Let $\Delta$ be the context
\[ \Gamma, x_1 : A_1, y_1 : A_1, e_1 : x_1 =_{A_1} y_1, \ldots, x_n : A_n, y_n : A_n, e_n : x_n =_{A_n} y_n \enspace \]
Then using the induction hypothesis $P \vec{e} \equiv P_{x_1 y_1} e_1 \cdots_{x_n y_n} e_n \in E_\Gamma(M \vec{x} =_\Omega N \vec{y})$ and so
$(P \vec{e})^+ \in E_\Gamma(M \vec{x} \supset N \vec{y}) \subseteq \SN$, hence $P \in \SN$.
\end{enumerate}
\end{proof}

\begin{proposition}
\begin{enumerate}
\item
If $\delta \in E_\Gamma(\phi)$, $\phi \simeq \psi$ and $\Gamma \vdash \psi : \Omega$, then $\delta \in E_\Gamma(\psi)$.
\begin{code}
not-APPl-var-osr-imp : ∀ {V} {x : Var V -Term} {MM : snocList (Term V)} {φ ψ : Term V} →
  APPl (var x) MM ⇒ φ ⊃ ψ → Empty
not-APPl-var-osr-imp {MM = []} ()
not-APPl-var-osr-imp {MM = MM snoc M} xMM⇒φ⊃ψ = {!!}

osr-computeP : ∀ {V S T} {Γ : Context V} {L : Meaning V S} {M : Meaning V T} {δ} →
               computeP Γ L δ → decode-Meaning L ⇒ decode-Meaning M →
               Γ ⊢ decode-Meaning M ∶ ty Ω → computeP Γ M δ
osr-computeP {L = nf₀ (neutral (app x x₁))} {nf₀ (neutral (app x₂ x₃))} computeLδ _ _ = computeLδ
osr-computeP {L = nf₀ (neutral (app x x₁))} {nf₀ bot} computeLδ _ _ = computeLδ
osr-computeP {L = nf₀ (neutral (app x x₁))} {M imp M₁} computeLδ L⇒M x₂ Δ ρ∶Γ⇒RΔ Δ⊢ε∶φ computeε = {!!}
osr-computeP {L = nf₀ bot} computeLδ L⇒M Γ⊢M∶Ω = {!!}
osr-computeP {L = L imp L₁} computeLδ L⇒M Γ⊢M∶Ω = {!!}

conv-computeP : ∀ {V S T} {Γ : Context V} {L : Meaning V S} {M : Meaning V T} {δ} →
                computeP Γ L δ → decode-Meaning L ≃ decode-Meaning M →
                Γ ⊢ decode-Meaning M ∶ ty Ω → computeP Γ M δ
conv-computeP = {!!}
\end{code}
\item
If $P \in E_\Gamma(M =_A N)$, $M \simeq M'$, $N \simeq N'$ and $\Gamma \vdash M : A$ and $\Gamma \vdash N : A$, then $P \in E_\Gamma(M' =_A N')$.
\AgdaHide{
\begin{code}
postulate conv-computeE : ∀ {V} {Γ : Context V} {M} {M'} {A} {N} {N'} {P} →
                        computeE Γ M A N P → 
                        Γ ⊢ M ∶ ty A → Γ ⊢ N ∶ ty A → Γ ⊢ M' ∶ ty A → Γ ⊢ N' ∶ ty A → M ≃ M' → N ≃ N' →
                        computeE Γ M' A N' P
{- conv-computeE {Γ = Γ} {M = M} {M' = M'} {A = Ω} {N' = N'} {P} (S ,p T ,p φ ,p ψ ,p M↠φ ,p N↠ψ ,p computeP+ ,p computeP-) 
  Γ⊢M∶A Γ⊢N∶A Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N' = 
    let (Q ,p φ↠Q ,p M'↠Q) = Church-Rosser (RSTClose.trans (RSTClose.sym (red-conv M↠φ)) M≃M') in
    let (φ' ,p φ'≡Q) = leaves-red {L = φ} φ↠Q in
    let (R ,p ψ↠R ,p N'↠R) = Church-Rosser (RSTClose.trans (RSTClose.sym (red-conv N↠ψ)) N≃N') in
    let (ψ' ,p ψ'≡R) = leaves-red {L = ψ} ψ↠R in
    S ,p T ,p φ' ,p ψ' ,p subst (_↠_ M') (Prelims.sym φ'≡Q) M'↠Q ,p 
    subst (_↠_ N') (Prelims.sym ψ'≡R) N'↠R ,p 
    (λ Δ {ρ} {ε} ρ∶Γ⇒RΔ Δ⊢ε∶φ'ρ computeε → 
      let step1 : Δ ⊢ decode-Prop (nfrep φ ρ) ∶ ty Ω
          step1 = subst (λ x → Δ ⊢ x ∶ ty Ω) 
            (Prelims.sym (decode-rep φ)) 
            (weakening 
              (subject-reduction 
                Γ⊢M∶A M↠φ) (context-validity Δ⊢ε∶φ'ρ) ρ∶Γ⇒RΔ) in
      let step1a : decode-Prop (nfrep φ' ρ) ≃ decode-Prop (nfrep φ ρ)
          step1a = subst₂ _≃_ (Prelims.sym (Prelims.trans (decode-rep φ') (rep-congl φ'≡Q))) (Prelims.sym (decode-rep φ)) (conv-rep {M = Q} {N = decode-Prop φ} 
            (RSTClose.sym (red-conv φ↠Q))) in 
      let step2 : Δ ⊢ ε ∶ decode-Prop (nfrep φ ρ)
          step2 = convR Δ⊢ε∶φ'ρ step1 step1a in
      let step3 : computeP Δ (nfrep φ ρ) ε
          step3 = conv-computeP {L = nfrep φ' ρ} {M = nfrep φ ρ} computeε step1a step1 in
      let step4 : computeP Δ (nfrep ψ ρ) (appP (plus P 〈 ρ 〉) ε)
          step4 = computeP+ Δ ρ∶Γ⇒RΔ step2 step3 in 
      let step5 : decode-Prop (nfrep ψ' ρ) ≃ decode-Prop (nfrep ψ ρ)
          step5 = subst₂ _≃_ (Prelims.sym (Prelims.trans (decode-rep ψ') (rep-congl ψ'≡R))) (Prelims.sym (decode-rep ψ)) (conv-rep {M = R} {N = decode-Prop ψ} 
            (RSTClose.sym (red-conv ψ↠R))) in
      let step6 : Δ ⊢ decode-Prop (nfrep ψ' ρ) ∶ ty Ω
          step6 = subst (λ x → Δ ⊢ x ∶ ty Ω) (Prelims.sym (decode-rep ψ')) 
                (weakening 
                  (subst (λ x → Γ ⊢ x ∶ ty Ω) (Prelims.sym ψ'≡R) 
                  (subject-reduction Γ⊢N'∶A N'↠R)) 
                (context-validity Δ⊢ε∶φ'ρ) 
                ρ∶Γ⇒RΔ) in
      conv-computeP {L = nfrep ψ ρ} {M = nfrep ψ' ρ} step4 (RSTClose.sym step5) step6) ,p 
    (    (λ Δ {ρ} {ε} ρ∶Γ⇒RΔ Δ⊢ε∶ψ'ρ computeε → 
      let step1 : Δ ⊢ decode-Prop (nfrep ψ ρ) ∶ ty Ω
          step1 = subst (λ x → Δ ⊢ x ∶ ty Ω) 
            (Prelims.sym (decode-rep ψ)) 
            (weakening 
              (subject-reduction 
                Γ⊢N∶A N↠ψ) (context-validity Δ⊢ε∶ψ'ρ) ρ∶Γ⇒RΔ) in
      let step1a : decode-Prop (nfrep ψ' ρ) ≃ decode-Prop (nfrep ψ ρ)
          step1a = subst₂ _≃_ (Prelims.sym (Prelims.trans (decode-rep ψ') (rep-congl ψ'≡R))) (Prelims.sym (decode-rep ψ)) (conv-rep {M = R} {N = decode-Prop ψ} 
            (RSTClose.sym (red-conv ψ↠R))) in 
      let step2 : Δ ⊢ ε ∶ decode-Prop (nfrep ψ ρ)
          step2 = convR Δ⊢ε∶ψ'ρ step1 step1a in
      let step3 : computeP Δ (nfrep ψ ρ) ε
          step3 = conv-computeP {L = nfrep ψ' ρ} {M = nfrep ψ ρ} computeε step1a step1 in
      let step4 : computeP Δ (nfrep φ ρ) (appP (minus P 〈 ρ 〉) ε)
          step4 = computeP- Δ ρ∶Γ⇒RΔ step2 step3 in 
      let step5 : decode-Prop (nfrep φ' ρ) ≃ decode-Prop (nfrep φ ρ)
          step5 = subst₂ _≃_ (Prelims.sym (Prelims.trans (decode-rep φ') (rep-congl φ'≡Q))) (Prelims.sym (decode-rep φ)) (conv-rep {M = Q} {N = decode-Prop φ} 
            (RSTClose.sym (red-conv φ↠Q))) in
      let step6 : Δ ⊢ decode-Prop (nfrep φ' ρ) ∶ ty Ω
          step6 = subst (λ x → Δ ⊢ x ∶ ty Ω) (Prelims.sym (decode-rep φ')) 
                (weakening 
                  (subst (λ x → Γ ⊢ x ∶ ty Ω) (Prelims.sym φ'≡Q) 
                  (subject-reduction Γ⊢M'∶A M'↠Q)) 
                (context-validity Δ⊢ε∶ψ'ρ) 
                ρ∶Γ⇒RΔ) in
      conv-computeP {L = nfrep φ ρ} {M = nfrep φ' ρ} step4 (RSTClose.sym step5) step6))
conv-computeE {A = A ⇛ B} computeP Γ⊢M∶A Γ⊢N∶A Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N' Δ ρ∶Γ⇒RΔ Δ⊢Q∶N≡N' computeN computeN' computeQ = 
  conv-computeE {A = B} 
  (computeP Δ ρ∶Γ⇒RΔ Δ⊢Q∶N≡N' computeN computeN' computeQ) 
    (appR (weakening Γ⊢M∶A (context-validity Δ⊢Q∶N≡N') ρ∶Γ⇒RΔ) 
      (equation-validity₁ Δ⊢Q∶N≡N')) 
    (appR (weakening Γ⊢N∶A (context-validity Δ⊢Q∶N≡N') ρ∶Γ⇒RΔ) 
      (equation-validity₂ Δ⊢Q∶N≡N'))
    (appR (weakening Γ⊢M'∶A (context-validity Δ⊢Q∶N≡N') ρ∶Γ⇒RΔ) (equation-validity₁ Δ⊢Q∶N≡N')) 
    (appR (weakening Γ⊢N'∶A (context-validity Δ⊢Q∶N≡N') ρ∶Γ⇒RΔ) (equation-validity₂ Δ⊢Q∶N≡N')) 
    (appT-convl (conv-rep M≃M')) (appT-convl (conv-rep N≃N')) -}
--TODO Common pattern
\end{code}
}

\begin{code}
postulate convE-E : ∀ {V} {Γ : Context V} {M N M' N' : Term V} {A} {P : Path V} →
                  E Γ (M ≡〈 A 〉 N) P → M ≃ M' → N ≃ N' → Γ ⊢ M' ∶ ty A → Γ ⊢ N' ∶ ty A → 
                  E Γ (M' ≡〈 A 〉 N') P
\end{code}

\AgdaHide{
\begin{code}
--convE-E (EI Γ⊢P∶M≡N computeP) M≃M' N≃N' Γ⊢M'∶A Γ⊢N'∶A = EI (convER Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') 
--  (conv-computeE computeP (equation-validity₁ Γ⊢P∶M≡N) (equation-validity₂ Γ⊢P∶M≡N) Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N')
\end{code}
}
\end{enumerate}
\end{proposition}

\AgdaHide{
\begin{code}
E-⊥ : ∀ {V} {Γ : Context V} → valid Γ → E Γ (ty Ω) ⊥
E-⊥ validΓ = EI (⊥R validΓ) (nf-SN nf⊥)

postulate ⊃-E : ∀ {V} {Γ : Context V} {φ} {ψ} → E Γ (ty Ω) φ → E Γ (ty Ω) ψ → E Γ (ty Ω) (φ ⊃ ψ)

postulate appT-E : ∀ {V} {Γ : Context V} {M N : Term V} {A} {B} →
                 valid Γ → E Γ (ty (A ⇛ B)) M → E Γ (ty A) N → E Γ (ty B) (appT M N)

postulate appP-E : ∀ {V} {Γ : Context V} {δ ε : Proof V} {φ} {ψ} →
                  E Γ (φ ⊃ ψ) δ → E Γ φ ε → E Γ ψ (appP δ ε)
postulate plus-E : ∀ {V} {Γ : Context V} {P : Path V} {φ ψ : Term V} →
                  E Γ (φ ≡〈 Ω 〉 ψ) P → E Γ (φ ⊃ ψ) (plus P)
postulate minus-E : ∀ {V} {Γ : Context V} {P : Path V} {φ ψ : Term V} →
                   E Γ (φ ≡〈 Ω 〉 ψ) P → E Γ (ψ ⊃ φ) (minus P)

postulate funcP-E : ∀ {U} {Γ : Context U} {δ : Proof U} {φ} {ψ} →
                  (∀ V Δ (ρ : Rep U V) (ε : Proof V) → ρ ∶ Γ ⇒R Δ → E Δ (φ 〈 ρ 〉) ε → E Δ (ψ 〈 ρ 〉) (appP (δ 〈 ρ 〉) ε)) → 
                  Γ ⊢ δ ∶ φ ⊃ ψ → E Γ (φ ⊃ ψ) δ

postulate ref-E : ∀ {V} {Γ : Context V} {M : Term V} {A : Type} → E Γ (ty A) M → E Γ (M ≡〈 A 〉 M) (reff M)
postulate ⊃*-E : ∀ {V} {Γ : Context V} {φ φ' ψ ψ' : Term V} {P Q : Path V} →
                  E Γ (φ ≡〈 Ω 〉 φ') P → E Γ (ψ ≡〈 Ω 〉 ψ') Q → E Γ (φ ⊃ ψ ≡〈 Ω 〉 φ' ⊃ ψ') (P ⊃* Q)
postulate univ-E : ∀ {V} {Γ : Context V} {φ ψ : Term V} {δ ε : Proof V} →
                  E Γ (φ ⊃ ψ) δ → E Γ (ψ ⊃ φ) ε → E Γ (φ ≡〈 Ω 〉 ψ) (univ φ ψ δ ε)
postulate app*-E : ∀ {V} {Γ : Context V} {M} {M'} {N} {N'} {A} {B} {P} {Q} →
                  E Γ (M ≡〈 A ⇛ B 〉 M') P → E Γ (N ≡〈 A 〉 N') Q →
                  E Γ (ty A) N → E Γ (ty A) N' →
                  E Γ (appT M N ≡〈 B 〉 appT M' N') (app* N N' P Q)

postulate funcE-E : ∀ {U} {Γ : Context U} {A} {B} {M} {M'} {P} →
                  Γ ⊢ P ∶ M ≡〈 A ⇛ B 〉 M' →
                  (∀ V (Δ : Context V) (N N' : Term V) Q ρ → ρ ∶ Γ ⇒R Δ → 
                  E Δ (ty A) N → E Δ (ty A) N' → E Δ (N ≡〈 A 〉 N') Q →
                  E Δ (appT (M 〈 ρ 〉) N ≡〈 B 〉 appT (M' 〈 ρ 〉) N') (app* N N' (P 〈 ρ 〉) Q)) →
                  E Γ (M ≡〈 A ⇛ B 〉 M') P

postulate wteT : ∀ {V} {Γ : Context V} {A M B N} → Γ ,T A ⊢ M ∶ ty B → E Γ (ty A) N → E Γ (ty B) (M ⟦ x₀:= N ⟧) →
                 E Γ (ty B) (appT (ΛT A M) N)

{-
postulate Neutral-computeE : ∀ {V} {Γ : Context V} {M} {A} {N} {P : NeutralP V} →
                           Γ ⊢ decode P ∶ M ≡〈 A 〉 N → computeE Γ M A N (decode P)

postulate NF : ∀ {V} {Γ} {φ : Term V} → Γ ⊢ φ ∶ ty Ω → closed-prop

postulate red-NF : ∀ {V} {Γ} {φ : Term V} (Γ⊢φ∶Ω : Γ ⊢ φ ∶ ty Ω) → φ ↠ cp2term (NF Γ⊢φ∶Ω)

postulate closed-rep : ∀ {U} {V} {ρ : Rep U V} (A : closed-prop) → (cp2term A) 〈 ρ 〉 ≡ cp2term A

postulate red-conv : ∀ {V} {C} {K} {E F : Subexpression V C K} → E ↠ F → E ≃ F

postulate confluent : ∀ {V} {φ : Term V} {ψ ψ' : closed-prop} → φ ↠ cp2term ψ → φ ↠ cp2term ψ' → ψ ≡ ψ'

func-E {δ = δ} {φ = φ} {ψ = ψ} hyp Γ⊢δ∶φ⊃ψ = let Γ⊢φ⊃ψ∶Ω = Prop-Validity Γ⊢δ∶φ⊃ψ in
                      let Γ⊢φ∶Ω = ⊃-gen₁ Γ⊢φ⊃ψ∶Ω in
                      let Γ⊢ψ∶Ω = ⊃-gen₂ Γ⊢φ⊃ψ∶Ω in
                      let φ' = NF Γ⊢φ∶Ω in
                      Γ⊢δ∶φ⊃ψ ,p NF Γ⊢φ∶Ω ⊃C NF Γ⊢ψ∶Ω ,p 
                      Prelims.trans-red (respects-red {f = λ x → x ⊃ ψ} (λ x → app (appl x)) (red-NF Γ⊢φ∶Ω)) 
                                (respects-red {f = λ x → cp2term (NF Γ⊢φ∶Ω) ⊃ x} (λ x → app (appr (appl x))) (red-NF Γ⊢ψ∶Ω)) ,p  --TODO Extract lemma for reduction
                      (λ W Δ ρ ε ρ∶Γ⇒Δ Δ⊢ε∶φ computeε →
                      let φρ↠φ' : φ 〈 ρ 〉 ↠ cp2term φ'
                          φρ↠φ' = subst (λ x → (φ 〈 ρ 〉) ↠ x) (closed-rep φ') (respects-red (respects-osr replacement β-respects-rep) (red-NF Γ⊢φ∶Ω)) in
                      let ε∈EΔψ = hyp W Δ ρ ε (context-validity Δ⊢ε∶φ) ρ∶Γ⇒Δ        
                                  ((convR Δ⊢ε∶φ (weakening Γ⊢φ∶Ω (context-validity Δ⊢ε∶φ) ρ∶Γ⇒Δ) (RSTClose.sym (red-conv φρ↠φ')) ) ,p φ' ,p φρ↠φ' ,p computeε ) in 
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

var-E : ∀ {V} {A} (Γ : Context V) (x : Var V -Term) → 
  valid Γ → typeof x Γ ≡ ty A → E Γ A (var x)
var-E : ∀ {V} (Γ : Context V) (x : Var V -Term) → 
        valid Γ → E Γ (typeof' x Γ) (var x)
computeE-SN : ∀ {V} {Γ : Context V} {M} {N} {A} {P} → computeE Γ M A N P → valid Γ → SN P

computeE-SN {A = Ω} {P} (P+∈EΓM⊃N ,p _) _ = 
  let SNplusP : SN (plus P)
      SNplusP = E-SN P+∈EΓM⊃N 
  in SNsubbodyl (SNsubexp SNplusP)
computeE-SN {V} {Γ} {A = A ⇛ B} {P} computeP validΓ =
  let x₀∈EΓ,AA : E (Γ ,T A) A (var x₀)
      x₀∈EΓ,AA = var-E {A = A} (Γ ,T A) x₀ (ctxTR validΓ) refl in
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
             (var-E {A = A} (Γ ,T A) x₀ (ctxTR (context-validity Γ⊢M∶A⇛B)) refl)) 
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

var-E {A = A} Γ x validΓ x∶A∈Γ = Neutral-E (var x) (change-type (varR x validΓ) x∶A∈Γ)

var-E Γ x validΓ = var-E {A = typeof' x Γ} Γ x validΓ typeof-typeof'

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

appP-E (_ ,p ⊥C ,p φ⊃ψ↠⊥ ,p _) _ = ⊥-elim (⊃-not-⊥ φ⊃ψ↠⊥)
appP-E {V} {Γ} {ε = ε} {φ} {ψ = ψ} (Γ⊢δ∶φ⊃ψ ,p (φ' ⊃C ψ') ,p φ⊃ψ↠φ'⊃ψ' ,p computeδ) (Γ⊢ε∶φ ,p φ'' ,p φ↠φ'' ,p computeε) = 
  (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) ,p ψ' ,p ⊃-inj₂ φ⊃ψ↠φ'⊃ψ' ,p 
  subst (λ x → compute Γ ψ' (appP x ε)) rep-idOp 
  (computeδ V Γ (idRep V) ε idRep-typed 
    (convR Γ⊢ε∶φ (cp-typed φ' (context-validity Γ⊢ε∶φ)) (red-conv (⊃-inj₁ φ⊃ψ↠φ'⊃ψ')))
  (subst (λ x → compute Γ x ε) (confluent φ↠φ'' (⊃-inj₁ φ⊃ψ↠φ'⊃ψ')) computeε))

conv-E φ≃ψ (Γ⊢δ∶φ ,p φ' ,p φ↠φ' ,p computeδ) Γ⊢ψ∶Ω = convR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ ,p φ' ,p confluent₂ {χ = φ'} φ≃ψ φ↠φ' ,p computeδ


postulate rep-E : ∀ {U} {V} {Γ} {Δ} {ρ : Rep U V} {φ} {δ} →
                 E Γ φ δ → ρ ∶ Γ ⇒R Δ → E Δ (φ 〈 ρ 〉) (δ 〈 ρ 〉)

univ-E {V} {Γ} {φ} {ψ} {δ} {ε} δ∈EΓφ⊃ψ ε∈EΓψ⊃φ = 
  let Γ⊢univ∶φ≡ψ : Γ ⊢ univ φ ψ δ ε ∶ φ ≡〈 Ω 〉 ψ
      Γ⊢univ∶φ≡ψ = (univR (E-typed δ∈EΓφ⊃ψ) (E-typed ε∈EΓψ⊃φ)) in
      (Γ⊢univ∶φ≡ψ ,p 
      expand-E δ∈EΓφ⊃ψ (plusR Γ⊢univ∶φ≡ψ) plus-univ ,p 
      expand-E ε∈EΓψ⊃φ (minusR Γ⊢univ∶φ≡ψ) minus-univ)

postulate rep-E : ∀ {U} {V} {Γ} {Δ} {ρ : Rep U V} {E} {P} →
                 E Γ E P → ρ ∶ Γ ⇒R Δ → E Δ (E 〈 ρ 〉) (P 〈 ρ 〉)

imp*-E {Γ = Γ} {φ} {φ'} {ψ = ψ} {ψ'} {P} {Q = Q} P∈EΓφ≡φ' Q∈EΓψ≡ψ' = (⊃*R (E-typed P∈EΓφ≡φ') (E-typed Q∈EΓψ≡ψ')) ,p 
  func-E (λ V Δ ρ ε validΔ ρ∶Γ⇒RΔ ε∈EΔφ⊃ψ →
    let Pρ : E Δ (φ 〈 ρ 〉 ≡〈 Ω 〉 φ' 〈 ρ 〉) (P 〈 ρ 〉)
        Pρ = rep-E P∈EΓφ≡φ' ρ∶Γ⇒RΔ in
    let Qρ : E Δ (ψ 〈 ρ 〉 ≡〈 Ω 〉 ψ' 〈 ρ 〉) (Q 〈 ρ 〉)
        Qρ = rep-E Q∈EΓψ≡ψ' ρ∶Γ⇒RΔ in
    func-E (λ W Θ σ χ validΘ σ∶Δ⇒RΘ χ∈EΘφ' → 
    let Pρσ : E Θ (φ 〈 ρ 〉 〈 σ 〉 ≡〈 Ω 〉 φ' 〈 ρ 〉 〈 σ 〉) (P 〈 ρ 〉 〈 σ 〉)
        Pρσ = rep-E Pρ σ∶Δ⇒RΘ in
    let Pρσ- : E Θ (φ' 〈 ρ 〉 〈 σ 〉 ⊃ φ 〈 ρ 〉 〈 σ 〉) (minus (P 〈 ρ 〉 〈 σ 〉))
        Pρσ- = minus-E Pρσ in
    let Qρσ : E Θ (ψ 〈 ρ 〉 〈 σ 〉 ≡〈 Ω 〉 ψ' 〈 ρ 〉 〈 σ 〉) (Q 〈 ρ 〉 〈 σ 〉)
        Qρσ = rep-E Qρ σ∶Δ⇒RΘ in
    let Qρσ+ : E Θ (ψ 〈 ρ 〉 〈 σ 〉 ⊃ ψ' 〈 ρ 〉 〈 σ 〉) (plus (Q 〈 ρ 〉 〈 σ 〉))
        Qρσ+ = plus-E Qρσ in
    let εσ : E Θ (φ 〈 ρ 〉 〈 σ 〉 ⊃ ψ 〈 ρ 〉 〈 σ 〉) (ε 〈 σ 〉)
        εσ = rep-E ε∈EΔφ⊃ψ σ∶Δ⇒RΘ in
    expand-E 
    (appP-E Qρσ+ (appP-E εσ (appP-E Pρσ- χ∈EΘφ')))
    (appPR (appPR (plusR (⊃*R (E-typed Pρσ) (E-typed Qρσ))) (E-typed εσ)) (E-typed χ∈EΘφ')) 
    imp*-plus) 
    (appPR (plusR (⊃*R (E-typed Pρ) (E-typed Qρ))) (E-typed ε∈EΔφ⊃ψ))) 
  (plusR (⊃*R (E-typed P∈EΓφ≡φ') (E-typed Q∈EΓψ≡ψ'))) ,p 
  func-E (λ V Δ ρ ε validΔ ρ∶Γ⇒RΔ ε∈EΔφ'⊃ψ' →
    let Pρ : E Δ (φ 〈 ρ 〉 ≡〈 Ω 〉 φ' 〈 ρ 〉) (P 〈 ρ 〉)
        Pρ = rep-E P∈EΓφ≡φ' ρ∶Γ⇒RΔ in
    let Qρ : E Δ (ψ 〈 ρ 〉 ≡〈 Ω 〉 ψ' 〈 ρ 〉) (Q 〈 ρ 〉)
        Qρ = rep-E Q∈EΓψ≡ψ' ρ∶Γ⇒RΔ in
    func-E (λ W Θ σ χ validΘ σ∶Δ⇒RΘ χ∈EΘφ' → 
      let Pρσ : E Θ (φ 〈 ρ 〉 〈 σ 〉 ≡〈 Ω 〉 φ' 〈 ρ 〉 〈 σ 〉) (P 〈 ρ 〉 〈 σ 〉)
          Pρσ = rep-E Pρ σ∶Δ⇒RΘ in
      let Pρσ+ : E Θ (φ 〈 ρ 〉 〈 σ 〉 ⊃ φ' 〈 ρ 〉 〈 σ 〉) (plus (P 〈 ρ 〉 〈 σ 〉))
          Pρσ+ = plus-E Pρσ in
      let Qρσ : E Θ (ψ 〈 ρ 〉 〈 σ 〉 ≡〈 Ω 〉 ψ' 〈 ρ 〉 〈 σ 〉) (Q 〈 ρ 〉 〈 σ 〉)
          Qρσ = rep-E Qρ σ∶Δ⇒RΘ in
      let Qρσ- : E Θ (ψ' 〈 ρ 〉 〈 σ 〉 ⊃ ψ 〈 ρ 〉 〈 σ 〉) (minus (Q 〈 ρ 〉 〈 σ 〉))
          Qρσ- = minus-E Qρσ in
      let εσ : E Θ (φ' 〈 ρ 〉 〈 σ 〉 ⊃ ψ' 〈 ρ 〉 〈 σ 〉) (ε 〈 σ 〉)
          εσ = rep-E ε∈EΔφ'⊃ψ' σ∶Δ⇒RΘ in 
      expand-E 
        (appP-E Qρσ- (appP-E εσ (appP-E Pρσ+ χ∈EΘφ'))) 
          (appPR (appPR (minusR (⊃*R (E-typed Pρσ) (E-typed Qρσ))) (E-typed εσ)) (E-typed χ∈EΘφ')) 
        imp*-minus)
    (appPR (minusR (⊃*R (E-typed Pρ) (E-typed Qρ))) (E-typed ε∈EΔφ'⊃ψ'))) 
  (minusR (⊃*R (E-typed P∈EΓφ≡φ') (E-typed Q∈EΓψ≡ψ')))

app*-E {V} {Γ} {M} {M'} {N} {N'} {A} {B} {P} {Q} (Γ⊢P∶M≡M' ,p computeP) (Γ⊢Q∶N≡N' ,p computeQ) N∈EΓA N'∈EΓA = (app*R (E-typed N∈EΓA) (E-typed N'∈EΓA) Γ⊢P∶M≡M' Γ⊢Q∶N≡N') ,p 
  subst₃
    (λ a b c →
       computeE Γ (appT a N) B (appT b N') (app* N N' c Q))
    rep-idOp rep-idOp rep-idOp 
    (computeP V Γ (idRep V) N N' Q idRep-typed Γ⊢Q∶N≡N' 
      N∈EΓA N'∈EΓA computeQ)

func-E {U} {Γ} {A} {B} {M} {M'} {P} Γ⊢P∶M≡M' hyp = Γ⊢P∶M≡M' ,p (λ W Δ ρ N N' Q ρ∶Γ⇒Δ Δ⊢Q∶N≡N' N∈EΔA N'∈EΔA computeQ → 
  proj₂ (hyp W Δ N N' Q ρ ρ∶Γ⇒Δ N∈EΔA N'∈EΔA (Δ⊢Q∶N≡N' ,p computeQ)))

ref-E {V} {Γ} {M} {A} M∈EΓA = refR (E-typed M∈EΓA) ,p ref-compute M∈EΓA

expand-E {V} {Γ} {A} {M} {N} {P} {Q} (Γ⊢Q∶M≡N ,p computeQ) Γ⊢P∶M≡N P▷Q = Γ⊢P∶M≡N ,p expand-computeE computeQ Γ⊢P∶M≡N P▷Q

postulate ⊃-respects-conv : ∀ {V} {φ} {φ'} {ψ} {ψ' : Term V} → φ ≃ φ' → ψ ≃ ψ' →
                          φ ⊃ ψ ≃ φ' ⊃ ψ'

postulate appT-respects-convl : ∀ {V} {M M' N : Term V} → M ≃ M' → appT M N ≃ appT M' N

conv-computeE : ∀ {V} {Γ : Context V} {M} {M'} {N} {N'} {A} {P} →
             computeE Γ M A N P → M ≃ M' → N ≃ N' → 
             Γ ⊢ M' ∶ ty A  → Γ ⊢ N' ∶ ty A  →
             computeE Γ M' A N' P
conv-computeE {M = M} {A = Ω} 
  (EΓM⊃NP+ ,p EΓN⊃MP-) M≃M' N≃N' Γ⊢M'∶Ω Γ⊢N'∶Ω = 
  (conv-E (⊃-respects-conv M≃M' N≃N')
    EΓM⊃NP+ (⊃R Γ⊢M'∶Ω Γ⊢N'∶Ω)) ,p 
  conv-E (⊃-respects-conv N≃N' M≃M') EΓN⊃MP- (⊃R Γ⊢N'∶Ω Γ⊢M'∶Ω)
conv-computeE {M = M} {M'} {N} {N'} {A = A ⇛ B} computeP M≃M' N≃N' Γ⊢M'∶A⇛B Γ⊢N'∶A⇛B =
  λ W Δ ρ L L' Q ρ∶Γ⇒RΔ Δ⊢Q∶L≡L' L∈EΔA L'∈EΔA computeQ → conv-computeE {A = B} 
  (computeP W Δ ρ L L' Q ρ∶Γ⇒RΔ Δ⊢Q∶L≡L' L∈EΔA L'∈EΔA computeQ) 
  (appT-respects-convl (respects-conv (respects-osr replacement β-respects-rep) M≃M')) 
  (appT-respects-convl (respects-conv (respects-osr replacement β-respects-rep) N≃N')) 
  (appR (weakening Γ⊢M'∶A⇛B (context-validity Δ⊢Q∶L≡L') ρ∶Γ⇒RΔ) (E-typed {W} {Γ = Δ} {A = A} {L} L∈EΔA)) 
  (appR (weakening Γ⊢N'∶A⇛B (context-validity Δ⊢Q∶L≡L') ρ∶Γ⇒RΔ) (E-typed L'∈EΔA)) 
--REFACTOR Duplication

conv-E (Γ⊢P∶M≡N ,p computeP) M≃M' N≃N' Γ⊢M'∶A Γ⊢N'∶A = convER Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N' ,p conv-computeE computeP M≃M' N≃N' Γ⊢M'∶A Γ⊢N'∶A
--REFACTOR Duplication                      
                 
E-SN (app (-eq _) (_ ,, _ ,, out)) (Γ⊢P∶E ,p computeP) = computeE-SN computeP (context-validity Γ⊢P∶E) -}

data Emult {V} (Γ : Context V) : ∀ {AA} → snocTypes V AA → snocListExp V AA → Set where
  [] : Emult Γ [] []
  _snoc_ : ∀ {KK K AA} {A : Expression (snoc-extend V KK) (parent K)} {MM M} → Emult Γ {KK} AA MM → E {K = K} Γ (A ⟦ xx₀:= MM ⟧) M → Emult Γ (AA snoc A) (MM snoc M)

postulate Emult-rep : ∀ {U V Γ Δ KK AA} {MM : snocListExp U KK} {ρ : Rep U V} → Emult Γ AA MM → ρ ∶ Γ ⇒R Δ → valid Δ → Emult Δ (snocTypes-rep AA ρ) (snocListExp-rep MM ρ)
{- Emult-rep [] _ _ = []
Emult-rep {U} {V} {Γ} {Δ = Δ} {KK snoc K} {AA = AA snoc A} {MM = MM snoc M} {ρ} (MM∈EΓAA snoc M∈EΓA) ρ∶Γ⇒RΔ validΔ = 
  (Emult-rep MM∈EΓAA ρ∶Γ⇒RΔ validΔ) snoc subst (λ x → E Δ x (M 〈 ρ 〉)) (liftsnocRep-botSub {U} {V} {KK} {E = A}) (E-rep M∈EΓA ρ∶Γ⇒RΔ validΔ) -}
\end{code}
}

