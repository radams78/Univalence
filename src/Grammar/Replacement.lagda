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
Rep : Alphabet VarKind → Alphabet VarKind → Set
Rep U V = ∀ K → Var U K → Var V K

rep↑ : ∀ {U} {V} K → Rep U V → Rep (U , K) (V , K)
rep↑ _ _ _ x₀ = x₀
rep↑ _ ρ K (↑ x) = ↑ (ρ K x)

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

rep↑-cong : ∀ {U} {V} {K} {ρ ρ' : Rep U V} → 
  ρ ∼R ρ' → rep↑ K ρ ∼R rep↑ K ρ'
\end{code}

\AgdaHide{
\begin{code}
rep↑-cong ρ-is-ρ' x₀ = refl
rep↑-cong ρ-is-ρ' (↑ x) = cong (var ∘ ↑) (var-inj (ρ-is-ρ' x))
\end{code}
}

\begin{code}
proto-replacement : LiftFamily
proto-replacement = record { 
  preOpFamily = pre-replacement ; 
  lifting = record { 
    liftOp = rep↑ ; 
    liftOp-cong = rep↑-cong } ; 
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

rep↑-comp : ∀ {U} {V} {W} {K} {ρ' : Rep V W} {ρ : Rep U V} → 
  rep↑ K (ρ' •R ρ) ∼R rep↑ K ρ' •R rep↑ K ρ
\end{code}

\AgdaHide{
\begin{code}
rep↑-comp x₀ = refl
rep↑-comp (↑ _) = refl

postulate rep↑-comp₄ : ∀ {U} {V1} {V2} {V3} {V4} {K} {ρ1 : Rep U V1} {ρ2 : Rep V1 V2} {ρ3 : Rep V2 V3} {ρ4 : Rep V3 V4} →
                       rep↑ K (ρ4 •R ρ3 •R ρ2 •R ρ1) ∼R rep↑ K ρ4 •R rep↑ K ρ3 •R rep↑ K ρ2 •R rep↑ K ρ1
\end{code}
}

\begin{code}
replacement : OpFamily
replacement = record { 
  liftFamily = proto-replacement ; 
  isOpFamily = record { 
    _∘_ = _•R_ ; 
    apV-comp = refl ; 
    liftOp-comp = rep↑-comp } }
\end{code}

\AgdaHide{
\begin{code}
open OpFamily replacement public using () 
  renaming (ap-congl to rep-congr;
           ap-congr to rep-congl;
           ap-idOp to rep-idOp;
           ap-circ to rep-comp;
           liftOp-idOp to rep↑-idOp;
           liftOp-up' to rep↑-upRep)

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
  ≡⟨ rep-congr E (magic-unique {ρ = ρ •R magic}) ⟩
    E 〈 magic 〉
  ∎

rep↑-upRep₂ : ∀ {U} {V} {C} {K} {L} {M} (E : Subexpression U C M) {σ : Rep U V} → E ⇑ ⇑ 〈 rep↑ K (rep↑ L σ) 〉 ≡ E 〈 σ 〉 ⇑ ⇑
rep↑-upRep₂ {U} {V} {C} {K} {L} {M} E {σ} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ 〈 rep↑ K (rep↑ L σ) 〉
  ≡⟨ rep↑-upRep (E ⇑) ⟩
    E ⇑ 〈 rep↑ L σ 〉 ⇑
  ≡⟨ rep-congl (rep↑-upRep E) ⟩
    E 〈 σ 〉 ⇑ ⇑
  ∎

rep↑-upRep₃ : ∀ {U} {V} {C} {K} {L} {M} {N} (E : Subexpression U C N) {σ : Rep U V} → 
  E ⇑ ⇑ ⇑ 〈 rep↑ K (rep↑ L (rep↑ M σ)) 〉 ≡ E 〈 σ 〉 ⇑ ⇑ ⇑
rep↑-upRep₃ {U} {V} {C} {K} {L} {M} E {σ} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ ⇑ 〈 rep↑ K (rep↑ L (rep↑ M σ)) 〉
  ≡⟨ rep↑-upRep₂ (E ⇑) ⟩
    E ⇑ 〈 rep↑ M σ 〉 ⇑ ⇑
  ≡⟨ rep-congl (rep-congl (rep↑-upRep E)) ⟩
    E 〈 σ 〉 ⇑ ⇑ ⇑
  ∎

postulate rep↑-upRep₄' : ∀ {U} {V} (ρ : Rep U V) {K1} {K2} {K3} → upRep •R upRep •R upRep •R ρ ∼R rep↑ K1 (rep↑ K2 (rep↑ K3 ρ)) •R upRep •R upRep •R upRep
\end{code}
}
