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

Rep↑ : ∀ {U} {V} K → Rep U V → Rep (U , K) (V , K)
Rep↑ _ _ _ x₀ = x₀
Rep↑ _ ρ K (↑ x) = ↑ (ρ K x)

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

Rep↑-cong : ∀ {U} {V} {K} {ρ ρ' : Rep U V} → 
  ρ ∼R ρ' → Rep↑ K ρ ∼R Rep↑ K ρ'
\end{code}

\AgdaHide{
\begin{code}
Rep↑-cong ρ-is-ρ' x₀ = refl
Rep↑-cong ρ-is-ρ' (↑ x) = cong (var ∘ ↑) (var-inj (ρ-is-ρ' x))
\end{code}
}

\begin{code}
proto-replacement : LiftFamily
proto-replacement = record { 
  preOpFamily = pre-replacement ; 
  lifting = record { 
    liftOp = Rep↑ ; 
    liftOp-cong = Rep↑-cong } ; 
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

Rep↑-comp : ∀ {U} {V} {W} {K} {ρ' : Rep V W} {ρ : Rep U V} → 
  Rep↑ K (ρ' •R ρ) ∼R Rep↑ K ρ' •R Rep↑ K ρ
\end{code}

\AgdaHide{
\begin{code}
Rep↑-comp x₀ = refl
Rep↑-comp (↑ _) = refl
\end{code}
}

\begin{code}
replacement : OpFamily
replacement = record { 
  liftFamily = proto-replacement ; 
  isOpFamily = record { 
    _∘_ = _•R_ ; 
    apV-comp = refl ; 
    liftOp-comp = Rep↑-comp } }
\end{code}

\AgdaHide{
\begin{code}
open OpFamily replacement public using () 
  renaming (ap-congl to rep-congr;
           ap-congr to rep-congl;
           ap-idOp to rep-idOp;
           ap-circ to rep-comp;
           liftOp-idOp to Rep↑-idOp;
           liftOp-up' to Rep↑-upRep)
\end{code}
}

We write $E \uparrow$ for $E \langle \uparrow \rangle$.

\begin{code}
infixl 60 _⇑
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
\end{code}
}
