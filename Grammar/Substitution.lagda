\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.Substitution (G : Grammar) where
open import Data.List
open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G
\end{code}
}

\subsection{Substitution}

A \emph{substitution} $\sigma$ from alphabet $U$ to alphabet $V$, $\sigma : U \Rightarrow V$, is a function $\sigma$ that maps every variable $x$ of kind $K$ in $U$ to an
\emph{expression} $\sigma(x)$ of kind $K$ over $V$.  We now aim to prov that the substitutions form a family of operations, with application and idOpentity being simply function application and idOpentity.

\begin{code}
Sub : Alphabet → Alphabet → Set
Sub U V = ∀ K → Var U K → Expression V (varKind K)

upSub : ∀ {V} {K} → Sub V (V , K)
upSub _ x = var (↑ x)

pre-substitution : PreOpFamily
pre-substitution = record { 
  Op = Sub; 
  apV = λ σ x → σ _ x; 
  up = upSub;
  apV-up = refl; 
  idOp = λ _ _ → var; 
  apV-idOp = λ _ → refl }

open PreOpFamily pre-substitution using () renaming (_∼op_ to _∼_;idOp to idOpSub) public

Sub↑ : ∀ {U} {V} K → Sub U V → Sub (U , K) (V , K)
Sub↑ _ _ _ x₀ = var x₀
Sub↑ _ σ K (↑ x) = (σ K x) 〈 upRep 〉

Sub↑-cong : ∀ {U} {V} {K} {σ σ' : Sub U V} → σ ∼ σ' → Sub↑ K σ ∼ Sub↑ K σ'
Sub↑-cong {K = K} σ-is-σ' x₀ = refl
Sub↑-cong σ-is-σ' (↑ x) = cong (λ E → E 〈 upRep 〉) (σ-is-σ' x)

SUB↑ : Lifting pre-substitution
SUB↑ = record { liftOp = Sub↑ ; liftOp-cong = Sub↑-cong }
\end{code}
    
Then, given an expression $E$ of kind $K$ over $U$, we write $E[\sigma]$ for the application of $\sigma$ to $E$, which is the result of substituting $\sigma(x)$ for $x$ for each variable in $E$, avoidOping capture.

\begin{code}    
infix 60 _⟦_⟧
_⟦_⟧ : ∀ {U} {V} {C} {K} → Subexpression U C K → Sub U V → Subexpression V C K
E ⟦ σ ⟧ = Lifting.ap SUB↑ σ E

rep2sub : ∀ {U} {V} → Rep U V → Sub U V
rep2sub ρ K x = var (ρ K x)

Rep↑-is-Sub↑ : ∀ {U} {V} {ρ : Rep U V} {K} → rep2sub (Rep↑ K ρ) ∼ Sub↑ K (rep2sub ρ)
Rep↑-is-Sub↑ x₀ = refl
Rep↑-is-Sub↑ (↑ _) = refl

up-is-up : ∀ {V} {K} → rep2sub (upRep {V} {K}) ∼ upSub
up-is-up _ = refl
\end{code}

Replacement is a special case of substitution:
\begin{lemma}
Let $\rho$ be a replacement $U \rightarrow V$.
\begin{enumerate}
\item
The replacement $(\rho , K)$ and the substitution $(\rho , K)$ are equal.
\item
$$ E \langle \rho \rangle \equiv E [ \rho ] $$
\end{enumerate}
\end{lemma}

\begin{code}
module Substitution where
  open PreOpFamily pre-substitution
  open Lifting SUB↑

  liftOp'-is-liftOp' : ∀ {U} {V} {ρ : Rep U V} {A} → rep2sub (OpFamily.liftOp' replacement A ρ) ∼ liftOp' A (rep2sub ρ)
  liftOp'-is-liftOp' {ρ = ρ} {A = []} = ∼-refl {σ = rep2sub ρ}
  liftOp'-is-liftOp' {U} {V} {ρ} {K ∷ A} = let open EqReasoning (OP _ _) in 
    begin
      rep2sub (OpFamily.liftOp' replacement A (Rep↑ K ρ))
    ≈⟨ liftOp'-is-liftOp' {A = A} ⟩
      liftOp' A (rep2sub (Rep↑ K ρ))
    ≈⟨ liftOp'-cong A Rep↑-is-Sub↑ ⟩
      liftOp' A (Sub↑ K (rep2sub ρ))
    ∎

  rep-is-sub : ∀ {U} {V} {K} {C} (E : Subexpression U K C) {ρ : Rep U V} → E 〈 ρ 〉 ≡ E ⟦ rep2sub ρ ⟧
  rep-is-sub (var _) = refl
  rep-is-sub (app c E) = cong (app c) (rep-is-sub E)
  rep-is-sub out = refl
  rep-is-sub {U} {V} (_,,_ {A = A} {L = L} E F) {ρ} = cong₂ _,,_ 
    (let open ≡-Reasoning {A = Expression (extend V A) L} in
    begin 
      E 〈 OpFamily.liftOp' replacement A ρ 〉
    ≡⟨ rep-is-sub E ⟩
      E ⟦ (λ K x → var (OpFamily.liftOp' replacement A ρ K x)) ⟧ 
    ≡⟨ ap-congl E (liftOp'-is-liftOp' {A = A}) ⟩
      E ⟦ liftOp' A (λ K x → var (ρ K x)) ⟧
    ∎)
    (rep-is-sub F)

  up-is-up' : ∀ {V} {C} {K} {L} {E : Subexpression V C K} → E 〈 upRep {K = L} 〉 ≡ E ⟦ upSub ⟧
  up-is-up' {E = E} = rep-is-sub E

open Substitution public

proto-substitution : LiftFamily
proto-substitution = record { 
  preOpFamily = pre-substitution ; 
  lifting = SUB↑ ; 
  isLiftFamily = record { liftOp-x₀ = refl ; liftOp-↑ = λ {_} {_} {_} {_} {σ} x → rep-is-sub (σ _ x) } }

infix 75 _•₁_
_•₁_ : ∀ {U} {V} {W} → Rep V W → Sub U V → Sub U W
(ρ •₁ σ) K x = (σ K x) 〈 ρ 〉

Sub↑-comp₁ : ∀ {U} {V} {W} {K} {ρ : Rep V W} {σ : Sub U V} → Sub↑ K (ρ •₁ σ) ∼ Rep↑ K ρ •₁ Sub↑ K σ
Sub↑-comp₁ {K = K} x₀ = refl
Sub↑-comp₁ {U} {V} {W} {K} {ρ} {σ} {L} (↑ x) = let open ≡-Reasoning {A = Expression (W , K) (varKind L)} in 
  begin 
    (σ L x) 〈 ρ 〉 〈 upRep 〉
  ≡⟨⟨ rep-comp (σ L x) ⟩⟩
    (σ L x) 〈 upRep •R ρ 〉
  ≡⟨⟩
    (σ L x) 〈 Rep↑ K ρ •R upRep 〉
  ≡⟨ rep-comp (σ L x) ⟩
    (σ L x) 〈 upRep 〉 〈 Rep↑ K ρ 〉
  ∎

COMP₁ : Composition proto-replacement proto-substitution proto-substitution
COMP₁ = record { 
  circ = _•₁_ ; 
  liftOp-circ = Sub↑-comp₁ ; 
  apV-circ = refl }

sub-comp₁ : ∀ {U} {V} {W} {C} {K} (E : Subexpression U C K) {ρ : Rep V W} {σ : Sub U V} →
      E ⟦ ρ •₁ σ ⟧ ≡ E ⟦ σ ⟧ 〈 ρ 〉
sub-comp₁ E = Composition.ap-circ COMP₁ E

infix 75 _•₂_
_•₂_ : ∀ {U} {V} {W} → Sub V W → Rep U V → Sub U W
(σ •₂ ρ) K x = σ K (ρ K x)

Sub↑-comp₂ : ∀ {U} {V} {W} {K} {σ : Sub V W} {ρ : Rep U V} → Sub↑ K (σ •₂ ρ) ∼ Sub↑ K σ •₂ Rep↑ K ρ
Sub↑-comp₂ {K = K} x₀ = refl
Sub↑-comp₂ (↑ x) = refl

COMP₂ : Composition proto-substitution proto-replacement proto-substitution
COMP₂ = record { 
  circ = _•₂_ ; 
  liftOp-circ = Sub↑-comp₂ ; 
  apV-circ = refl }

sub-comp₂ : ∀ {U} {V} {W} {C} {K} (E : Subexpression U C K) {σ : Sub V W} {ρ : Rep U V} → E ⟦ σ •₂ ρ ⟧ ≡ E 〈 ρ 〉 ⟦ σ ⟧
sub-comp₂ E = Composition.ap-circ COMP₂ E
\end{code}

Composition is defined by $(\sigma \circ \rho)(x) \equiv \rho(x) [ \sigma ]$.

\begin{code}
infix 75 _•_
_•_ : ∀ {U} {V} {W} → Sub V W → Sub U V → Sub U W
(σ • ρ) K x = ρ K x ⟦ σ ⟧

Sub↑-comp : ∀ {U} {V} {W} {ρ : Sub U V} {σ : Sub V W} {K} → Sub↑ K (σ • ρ) ∼ Sub↑ K σ • Sub↑ K ρ
Sub↑-comp x₀ = refl
Sub↑-comp {W = W} {ρ = ρ} {σ = σ} {K = K} {L} (↑ x) = 
  let open ≡-Reasoning in 
  begin 
    ρ L x ⟦ σ ⟧ 〈 upRep 〉
  ≡⟨⟨ sub-comp₁ (ρ L x) ⟩⟩
    ρ L x ⟦ upRep •₁ σ ⟧
  ≡⟨⟩
    ρ L x ⟦ Sub↑ K σ •₂ upRep ⟧
  ≡⟨ sub-comp₂ (ρ L x) ⟩
     ρ L x 〈 upRep 〉 ⟦ Sub↑ K σ ⟧ 
  ∎

substitution : OpFamily
substitution = record { 
  liftFamily = proto-substitution ; 
  isOpFamily = record { 
    _∘_ = _•_ ; 
    liftOp-comp = Sub↑-comp ; 
    apV-comp = refl } 
  }

open OpFamily substitution using (assoc) 
  renaming (liftOp-idOp to Sub↑-idOp;
           ap-idOp to sub-idOp;
           ap-circ to sub-comp;
           ap-congl to sub-cong;
           unitl to sub-unitl;
           unitr to sub-unitr)
  public
\end{code}
