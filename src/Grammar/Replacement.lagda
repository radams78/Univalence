\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.Replacement (G : Grammar) where

open import Function
open import Prelims
open Grammar G
open import Grammar.OpFamily.PreOpFamily G
open import Grammar.OpFamily.LiftFamily G
open import Grammar.OpFamily.OpFamily G
\end{code}
}

\subsection{Replacement}

The operation family of \emph{replacement} is defined as follows.  A replacement $\rho : U \rightarrow V$ is a function
that maps every variable in $U$ to a variable in $V$ of the same kind.  Application, identity and composition are simply
function application, the identity function and function composition.  The successor is the canonical injection $V \rightarrow (V, K)$,
and $(\sigma , K)$ is the extension of $\sigma$ that maps $x_0$ to $x_0$.

\begin{code}
Rep : Alphabet → Alphabet → Set
Rep U V = ∀ K → Var U K → Var V K

liftRep : ∀ {U} {V} K → Rep U V → Rep (U , K) (V , K)
liftRep _ _ _ x₀ = x₀
liftRep _ ρ K (↑ x) = ↑ (ρ K x)

upRep : ∀ {V} {K} → Rep V (V , K)
upRep _ = ↑

idRep : ∀ V → Rep V V
idRep _ _ x = x

pre-replacement : PreOpFamily
pre-replacement = record { 
  Op = Rep; 
  apV = λ ρ x → var (ρ _ x); 
  up = upRep; 
  apV-up = refl; 
  idOp = idRep; 
  apV-idOp = λ _ → refl }

_∼R_ : ∀ {U} {V} → Rep U V → Rep U V → Set
_∼R_ = PreOpFamily._∼op_ pre-replacement

liftRep-cong : ∀ {U} {V} {K} {ρ ρ' : Rep U V} → 
  ρ ∼R ρ' → liftRep K ρ ∼R liftRep K ρ'
\end{code}

\AgdaHide{
\begin{code}
liftRep-cong ρ-is-ρ' x₀ = refl
liftRep-cong ρ-is-ρ' (↑ x) = cong (var ∘ ↑) (var-inj (ρ-is-ρ' x))
\end{code}
}

\begin{code}
proto-replacement : LiftFamily
proto-replacement = record { 
  preOpFamily = pre-replacement ; 
  lifting = record { 
    liftOp = liftRep ; 
    liftOp-cong = liftRep-cong } ; 
  isLiftFamily = record { 
    liftOp-x₀ = refl ; 
    liftOp-↑ = λ _ → refl } }

infix 70 _〈_〉
_〈_〉 : ∀ {U} {V} {C} {K} → 
  Subexpression U C K → Rep U V → Subexpression V C K
E 〈 ρ 〉 = LiftFamily.ap proto-replacement ρ E

infixl 75 _•R_
_•R_ : ∀ {U} {V} {W} → Rep V W → Rep U V → Rep U W
(ρ' •R ρ) K x = ρ' K (ρ K x)

liftRep-comp : ∀ {U} {V} {W} {K} {ρ' : Rep V W} {ρ : Rep U V} → 
  liftRep K (ρ' •R ρ) ∼R liftRep K ρ' •R liftRep K ρ
\end{code}

\AgdaHide{
\begin{code}
liftRep-comp x₀ = refl
liftRep-comp (↑ _) = refl

postulate liftRep-comp₄ : ∀ {U} {V1} {V2} {V3} {V4} {K} {ρ1 : Rep U V1} {ρ2 : Rep V1 V2} {ρ3 : Rep V2 V3} {ρ4 : Rep V3 V4} →
                       liftRep K (ρ4 •R ρ3 •R ρ2 •R ρ1) ∼R liftRep K ρ4 •R liftRep K ρ3 •R liftRep K ρ2 •R liftRep K ρ1
\end{code}
}

\begin{code}
replacement : OpFamily
replacement = record { 
  liftFamily = proto-replacement ; 
  comp = record { 
    _∘_ = _•R_ ; 
    apV-comp = refl ; 
    liftOp-comp = liftRep-comp } }
\end{code}

\AgdaHide{
\begin{code}
open OpFamily replacement public using () 
  renaming (ap-congl to rep-congr;
           ap-congr to rep-congl;
           ap-idOp to rep-idOp;
           ap-comp to rep-comp;
           liftOp-idOp to liftRep-idOp;
           liftOp-up to liftRep-upRep)

postulate rep-comp₄ : ∀ {U} {V1} {V2} {V3} {V4} 
                      {ρ1 : Rep U V1} {ρ2 : Rep V1 V2} {ρ3 : Rep V2 V3} {ρ4 : Rep V3 V4} 
                      {C} {K} (E : Subexpression U C K) →
                      E 〈 ρ4 •R ρ3 •R ρ2 •R ρ1 〉 ≡ E 〈 ρ1 〉 〈 ρ2 〉 〈 ρ3 〉 〈 ρ4 〉
\end{code}
}

We write $E \uparrow$ for $E \langle \uparrow \rangle$.

\begin{code}
infixl 70 _⇑
_⇑ : ∀ {V} {K} {C} {L} → Subexpression V C L → Subexpression (V , K) C L
E ⇑ = E 〈 upRep 〉
\end{code}

We define the unique replacement $\emptyset \rightarrow V$ for any V, and prove it unique:

\begin{code}
magic : ∀ {V} → Rep ∅ V
magic _ ()

magic-unique : ∀ {V} {ρ : Rep ∅ V} → ρ ∼R magic
\end{code}

\AgdaHide{
\begin{code}
magic-unique {V} {ρ} ()
\end{code}
}

\begin{code}
magic-unique' : ∀ {U} {V} {C} {K}
  (E : Subexpression ∅ C K) {ρ : Rep U V} → 
  E 〈 magic 〉 〈 ρ 〉 ≡ E 〈 magic 〉
\end{code}

\AgdaHide{
\begin{code}
magic-unique' E {ρ} = let open ≡-Reasoning in
  begin
    E 〈 magic 〉 〈 ρ 〉
  ≡⟨⟨ rep-comp E ⟩⟩
    E 〈 ρ •R magic 〉
  ≡⟨ rep-congr (magic-unique {ρ = ρ •R magic}) E ⟩
    E 〈 magic 〉
  ∎

liftRep-upRep₂ : ∀ {U} {V} {C} {K} {L} {M} (E : Subexpression U C M) {σ : Rep U V} → E ⇑ ⇑ 〈 liftRep K (liftRep L σ) 〉 ≡ E 〈 σ 〉 ⇑ ⇑
liftRep-upRep₂ {U} {V} {C} {K} {L} {M} E {σ} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ 〈 liftRep K (liftRep L σ) 〉
  ≡⟨ liftRep-upRep (E ⇑) ⟩
    E ⇑ 〈 liftRep L σ 〉 ⇑
  ≡⟨ rep-congl (liftRep-upRep E) ⟩
    E 〈 σ 〉 ⇑ ⇑
  ∎

liftRep-upRep₃ : ∀ {U} {V} {C} {K} {L} {M} {N} (E : Subexpression U C N) {σ : Rep U V} → 
  E ⇑ ⇑ ⇑ 〈 liftRep K (liftRep L (liftRep M σ)) 〉 ≡ E 〈 σ 〉 ⇑ ⇑ ⇑
liftRep-upRep₃ {U} {V} {C} {K} {L} {M} E {σ} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ ⇑ 〈 liftRep K (liftRep L (liftRep M σ)) 〉
  ≡⟨ liftRep-upRep₂ (E ⇑) ⟩
    E ⇑ 〈 liftRep M σ 〉 ⇑ ⇑
  ≡⟨ rep-congl (rep-congl (liftRep-upRep E)) ⟩
    E 〈 σ 〉 ⇑ ⇑ ⇑
  ∎

postulate liftRep-upRep₄' : ∀ {U} {V} (ρ : Rep U V) {K1} {K2} {K3} → upRep •R upRep •R upRep •R ρ ∼R liftRep K1 (liftRep K2 (liftRep K3 ρ)) •R upRep •R upRep •R upRep
\end{code}
}
