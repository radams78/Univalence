\begin{code}
open import Function
open import Data.Nat
open import Prelims
open import Grammar
import Grammar.OpFamily

module Grammar.Replacement (G : Grammar) where
  open Grammar.Grammar G
  open Grammar.OpFamily G
\end{code}

\subsection{Replacement}

The operation family of \emph{replacement} is defined as follows.  A replacement $\rho : U \rightarrow V$ is a function
that maps every variable in $U$ to a variable in $V$ of the same kind.  Application, idOpentity and composition are simply
function application, the idOpentity function and function composition.  The successor is the canonical injection $V \rightarrow (V, K)$,
and $(\sigma , K)$ is the extension of $\sigma$ that maps $x_0$ to $x_0$.

\begin{code}
  Rep : Alphabet → Alphabet → Set
  Rep U V = ∀ K → Var U K → Var V K

  Rep↑ : ∀ {U} {V} K → Rep U V → Rep (U , K) (V , K)
  Rep↑ _ _ _ x₀ = x₀
  Rep↑ _ ρ K (↑ x) = ↑ (ρ K x)

  upRep : ∀ {V} {K} → Rep V (V , K)
  upRep _ = ↑

  idOpRep : ∀ V → Rep V V
  idOpRep _ _ x = x

  pre-replacement : PreOpFamily
  pre-replacement = record { 
      Op = Rep; 
      apV = λ ρ x → var (ρ _ x); 
      up = upRep; 
      apV-up = refl; 
      idOp = idOpRep; 
      apV-idOp = λ _ → refl }

  _∼R_ : ∀ {U} {V} → Rep U V → Rep U V → Set
  _∼R_ = PreOpFamily._∼op_ pre-replacement

  Rep↑-cong : ∀ {U} {V} {K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → Rep↑ K ρ ∼R Rep↑ K ρ'
  Rep↑-cong ρ-is-ρ' x₀ = refl
  Rep↑-cong ρ-is-ρ' (↑ x) = cong (var ∘ ↑) (var-inj (ρ-is-ρ' x))

  proto-replacement : LiftFamily
  proto-replacement = record { 
      preOpFamily = pre-replacement ; 
      lifting = record { 
        liftOp = Rep↑ ; 
        liftOp-cong = Rep↑-cong } ; 
      isLiftFamily = record { 
        liftOp-x₀ = refl ; 
        liftOp-↑ = λ _ → refl } }

  infix 60 _〈_〉
  _〈_〉 : ∀ {U} {V} {C} {K} → Subexpression U C K → Rep U V → Subexpression V C K
  E 〈 ρ 〉 = LiftFamily.ap proto-replacement ρ E

  infixl 75 _•R_
  _•R_ : ∀ {U} {V} {W} → Rep V W → Rep U V → Rep U W
  (ρ' •R ρ) K x = ρ' K (ρ K x)

  Rep↑-comp : ∀ {U} {V} {W} {K} {ρ' : Rep V W} {ρ : Rep U V} → Rep↑ K (ρ' •R ρ) ∼R Rep↑ K ρ' •R Rep↑ K ρ
  Rep↑-comp x₀ = refl
  Rep↑-comp (↑ _) = refl

  replacement : OpFamily
  replacement = record { 
      liftFamily = proto-replacement ; 
      isOpFamily = record { 
        comp = _•R_ ; 
        apV-comp = refl ; 
        liftOp-comp = Rep↑-comp } }

  rep-cong : ∀ {U} {V} {C} {K} {E : Subexpression U C K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → E 〈 ρ 〉 ≡ E 〈 ρ' 〉
  rep-cong {U} {V} {C} {K} {E} {ρ} {ρ'} ρ-is-ρ' = OpFamily.ap-congl replacement E ρ-is-ρ'

  rep-idOp : ∀ {V} {C} {K} {E : Subexpression V C K} → E 〈 idOpRep V 〉 ≡ E
  rep-idOp = OpFamily.ap-idOp replacement

  rep-comp : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {ρ : Rep U V} {σ : Rep V W} →
      E 〈 σ •R ρ 〉 ≡ E 〈 ρ 〉 〈 σ 〉
  rep-comp {U} {V} {W} {C} {K} {E} {ρ} {σ} = OpFamily.ap-comp replacement E

  Rep↑-idOp : ∀ {V} {K} → Rep↑ K (idOpRep V) ∼R idOpRep (V , K)
  Rep↑-idOp = OpFamily.liftOp-idOp replacement
--TODO Inline many of these
\end{code}

This providOpes us with the canonical mapping from an expression over $V$ to an expression over $(V , K)$:
\begin{code}
  liftE : ∀ {V} {K} {L} → Expression V L → Expression (V , K) L
  liftE E = E 〈 upRep 〉
--TOOD Inline this
\end{code}

Let $\mathsf{embedl}$ be the canonical injection $A \rightarrow \mathsf{extend}\ A\ K\ F$, which
is a replacement.

\begin{code}
  embedl : ∀ {A} {K} {F} → Rep A (extend A K F)
  embedl {F = zero} _ x = x
  embedl {F = suc F} K x = ↑ (embedl {F = F} K x)
\end{code}
