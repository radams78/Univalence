\AgdaHide{
\begin{code}
--Variable convention: ρ ranges over replacements
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

upRep : ∀ {V} {K} → Rep V (V , K)
upRep _ = ↑

idRep : ∀ V → Rep V V
idRep _ _ x = x

Rep∶POF : PreOpFamily
Rep∶POF = record { 
  Op = Rep; 
  apV = λ ρ x → var (ρ _ x); 
  up = upRep; 
  apV-up = refl; 
  idOp = idRep; 
  apV-idOp = λ _ → refl }

_∼R_ : ∀ {U} {V} → Rep U V → Rep U V → Set
_∼R_ = PreOpFamily._∼op_ Rep∶POF

liftRep : ∀ {U} {V} K → Rep U V → Rep (U , K) (V , K)
liftRep _ _ _ x₀ = x₀
liftRep _ ρ K (↑ x) = ↑ (ρ K x)

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
Rep∶LF : LiftFamily
Rep∶LF = record { 
  preOpFamily = Rep∶POF ; 
  lifting = record { 
    liftOp = liftRep ; 
    liftOp-cong = liftRep-cong } ; 
  isLiftFamily = record { 
    liftOp-x₀ = refl ; 
    liftOp-↑ = λ _ → refl } }

infix 70 _〈_〉
_〈_〉 : ∀ {U} {V} {C} {K} → Subexp U C K → Rep U V → Subexp V C K
E 〈 ρ 〉 = LiftFamily.ap Rep∶LF ρ E

liftsRep : ∀ {U V} KK → Rep U V → Rep (extend U KK) (extend V KK)
liftsRep = LiftFamily.liftsOp Rep∶LF

liftsnocRep : ∀ {U V} KK → Rep U V → Rep (snoc-extend U KK) (snoc-extend V KK)
liftsnocRep [] ρ = ρ
liftsnocRep (KK snoc K) ρ = liftRep K (liftsnocRep KK ρ)

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
\end{code}
}

\begin{code}
REP : OpFamily
REP = record { 
  liftFamily = Rep∶LF ; 
  comp = record { 
    _∘_ = _•R_ ; 
    apV-comp = refl ; 
    liftOp-comp' = liftRep-comp } }
\end{code}

\AgdaHide{
\begin{code}
•R-congl : ∀ {U V W} {ρ₁ ρ₂ : Rep V W} → ρ₁ ∼R ρ₂ → ∀ (ρ₃ : Rep U V) → ρ₁ •R ρ₃ ∼R ρ₂ •R ρ₃
•R-congl = OpFamily.comp-congl REP

•R-congr : ∀ {U V W} {ρ₁ : Rep V W} {ρ₂ ρ₃ : Rep U V} → ρ₂ ∼R ρ₃ → ρ₁ •R ρ₂ ∼R ρ₁ •R ρ₃
•R-congr {ρ₁ = ρ₁} = OpFamily.comp-congr REP ρ₁

rep-congr : ∀ {U V C K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → ∀ (E : Subexp U C K) → E 〈 ρ 〉 ≡ E 〈 ρ' 〉
rep-congr = OpFamily.ap-congl REP

rep-congl : ∀ {U V C K} {ρ : Rep U V} {E F : Subexp U C K} → E ≡ F → E 〈 ρ 〉 ≡ F 〈 ρ 〉
rep-congl = OpFamily.ap-congr REP

rep-idRep : ∀ {V C K} {E : Subexp V C K} → E 〈 idRep V 〉 ≡ E
rep-idRep = OpFamily.ap-idOp REP

rep-comp : ∀ {U V W C K} (E : Subexp U C K) {σ : Rep V W} {ρ} → E 〈 σ •R ρ 〉 ≡ E 〈 ρ 〉 〈 σ 〉
rep-comp = OpFamily.ap-comp REP

liftRep-idRep : ∀ {V K} → liftRep K (idRep V) ∼R idRep (V , K)
liftRep-idRep = OpFamily.liftOp-idOp REP

liftRep-upRep : ∀ {U V C K L} {σ : Rep U V} (E : Subexp U C K) → E 〈 upRep 〉 〈 liftRep L σ 〉 ≡ E 〈 σ 〉 〈 upRep 〉
liftRep-upRep = OpFamily.liftOp-up REP

liftRep-comp₄ : ∀ {U} {V1} {V2} {V3} {V4} {K} {ρ1 : Rep U V1} {ρ2 : Rep V1 V2} {ρ3 : Rep V2 V3} {ρ4 : Rep V3 V4} →
                liftRep K (ρ4 •R ρ3 •R ρ2 •R ρ1) ∼R liftRep K ρ4 •R liftRep K ρ3 •R liftRep K ρ2 •R liftRep K ρ1
liftRep-comp₄ {U} {V1} {V2} {V3} {V4} {K} {ρ1} {ρ2} {ρ3} {ρ4} =
  let open Prelims.EqReasoning (PreOpFamily.OP Rep∶POF (U , K) (V4 , K)) in 
  begin
    liftRep K (ρ4 •R ρ3 •R ρ2 •R ρ1)
  ≈⟨ liftRep-comp ⟩
    liftRep K (ρ4 •R ρ3 •R ρ2) •R liftRep K ρ1
  ≈⟨ •R-congl liftRep-comp (liftRep K ρ1)⟩
    liftRep K (ρ4 •R ρ3) •R liftRep K ρ2 •R liftRep K ρ1
  ≈⟨ •R-congl (•R-congl liftRep-comp (liftRep K ρ2)) (liftRep K ρ1)⟩
    liftRep K ρ4 •R liftRep K ρ3 •R liftRep K ρ2 •R liftRep K ρ1
  ∎

rep-comp₄ : ∀ {U} {V1} {V2} {V3} {V4} 
            {ρ1 : Rep U V1} {ρ2 : Rep V1 V2} {ρ3 : Rep V2 V3} {ρ4 : Rep V3 V4} 
            {C} {K} (E : Subexp U C K) →
            E 〈 ρ4 •R ρ3 •R ρ2 •R ρ1 〉 ≡ E 〈 ρ1 〉 〈 ρ2 〉 〈 ρ3 〉 〈 ρ4 〉
rep-comp₄ {U} {V1} {V2} {V3} {V4} {ρ1} {ρ2} {ρ3} {ρ4} {C} {K} E = 
  let open ≡-Reasoning in 
  begin
    E 〈 ρ4 •R ρ3 •R ρ2 •R ρ1 〉
      ≡⟨ rep-comp E ⟩
    E 〈 ρ1 〉 〈 ρ4 •R ρ3 •R ρ2 〉
      ≡⟨ rep-comp (E 〈 ρ1 〉) ⟩
    E 〈 ρ1 〉 〈 ρ2 〉 〈 ρ4 •R ρ3 〉
      ≡⟨ rep-comp (E 〈 ρ1 〉 〈 ρ2 〉) ⟩
    E 〈 ρ1 〉 〈 ρ2 〉 〈 ρ3 〉 〈 ρ4 〉
  ∎
\end{code}
}

We write $E \uparrow$ for $E \langle \uparrow \rangle$.

\begin{code}
infixl 70 _⇑
_⇑ : ∀ {V} {K} {C} {L} → Subexp V C L → Subexp (V , K) C L
E ⇑ = E 〈 upRep 〉

ups : ∀ {V} KK → Rep V (snoc-extend V KK)
ups [] = idRep _
ups (KK snoc K) = upRep •R ups KK

infix 70 _⇑⇑
_⇑⇑ : ∀ {V C K KK} → Subexp V C K → Subexp (snoc-extend V KK) C K
_⇑⇑ {KK = KK} E = E 〈 ups KK 〉

liftsnocRep-ups : ∀ {U V C K} KK (E : Subexp U C K) {ρ : Rep U V} → (_⇑⇑ {KK = KK} E) 〈 liftsnocRep KK ρ 〉 ≡ (_⇑⇑ {KK = KK} (E 〈 ρ 〉))
liftsnocRep-ups {U} {V} [] E {ρ} = let open ≡-Reasoning in
  begin
    E 〈 idRep U 〉 〈 ρ 〉
  ≡⟨ rep-congl (rep-idRep {E = E}) ⟩
    E 〈 ρ 〉
  ≡⟨⟨ rep-idRep ⟩⟩
    E 〈 ρ 〉 〈 idRep V 〉
  ∎
liftsnocRep-ups (KK snoc K) E {ρ} = let open ≡-Reasoning in 
  begin
    E 〈 upRep •R ups KK 〉 〈 liftRep K (liftsnocRep KK ρ) 〉
  ≡⟨ rep-congl (rep-comp E) ⟩
    E 〈 ups KK 〉 ⇑ 〈 liftRep K (liftsnocRep KK ρ) 〉
  ≡⟨ liftRep-upRep (E 〈 ups KK 〉) ⟩
    E 〈 ups KK 〉 〈 liftsnocRep KK ρ 〉 ⇑
  ≡⟨ rep-congl (liftsnocRep-ups KK E) ⟩
    E 〈 ρ 〉 〈 ups KK 〉 ⇑
  ≡⟨⟨ rep-comp (E 〈 ρ 〉) ⟩⟩
    E 〈 ρ 〉 〈 upRep •R ups KK 〉
  ∎
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
  (E : Subexp ∅ C K) {ρ : Rep U V} → 
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

liftRep-upRep₂ : ∀ {U} {V} {C} {K} {L} {M} (E : Subexp U C M) {ρ : Rep U V} → E ⇑ ⇑ 〈 liftRep K (liftRep L ρ) 〉 ≡ E 〈 ρ 〉 ⇑ ⇑
liftRep-upRep₂ {U} {V} {C} {K} {L} {M} E {ρ} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ 〈 liftRep K (liftRep L ρ) 〉
  ≡⟨ liftRep-upRep (E ⇑) ⟩
    E ⇑ 〈 liftRep L ρ 〉 ⇑
  ≡⟨ rep-congl (liftRep-upRep E) ⟩
    E 〈 ρ 〉 ⇑ ⇑
  ∎

liftRep-upRep₃ : ∀ {U} {V} {C} {K} {L} {M} {N} (E : Subexp U C N) {ρ : Rep U V} → 
  E ⇑ ⇑ ⇑ 〈 liftRep K (liftRep L (liftRep M ρ)) 〉 ≡ E 〈 ρ 〉 ⇑ ⇑ ⇑
liftRep-upRep₃ {U} {V} {C} {K} {L} {M} E {ρ} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ ⇑ 〈 liftRep K (liftRep L (liftRep M ρ)) 〉
  ≡⟨ liftRep-upRep₂ (E ⇑) ⟩
    E ⇑ 〈 liftRep M ρ 〉 ⇑ ⇑
  ≡⟨ rep-congl (rep-congl (liftRep-upRep E)) ⟩
    E 〈 ρ 〉 ⇑ ⇑ ⇑
  ∎

postulate liftRep-upRep₄' : ∀ {U} {V} (ρ : Rep U V) {K1} {K2} {K3} → upRep •R upRep •R upRep •R ρ ∼R liftRep K1 (liftRep K2 (liftRep K3 ρ)) •R upRep •R upRep •R upRep

Types-rep : ∀ {U V KK} → Types U KK → Rep U V → Types V KK
Types-rep [] _ = []
Types-rep (B , BB) ρ = B 〈 ρ 〉 , Types-rep BB (liftRep _ ρ)

snocTypes-rep : ∀ {U V KK} → snocTypes U KK → Rep U V → snocTypes V KK
snocTypes-rep [] _ = []
snocTypes-rep {KK = KK snoc _} (AA snoc A) ρ = snocTypes-rep AA ρ snoc A 〈 liftsnocRep KK ρ 〉

snocListExp-rep : ∀ {U V KK} → HetsnocList (VExpression U) KK → Rep U V → HetsnocList (VExpression V) KK
snocListExp-rep [] _ = []
snocListExp-rep (MM snoc M) ρ = snocListExp-rep MM ρ snoc (M 〈 ρ 〉)

snocVec-rep : ∀ {U V C K n} → snocVec (Subexp U C K) n → Rep U V → snocVec (Subexp V C K) n
snocVec-rep [] ρ = []
snocVec-rep (EE snoc E) ρ = snocVec-rep EE ρ snoc E 〈 ρ 〉
\end{code}
}
