\begin{code}
module PHOPL.MainProp where
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import Prelims
open import PHOPL
open import PHOPL.Rules
open import PHOPL.PathSub

close : ∀ {V} → Type V → Type ∅
close (app -Omega out) = Ω
close (app -func (A ,, B ,, out)) = close A ⇛ close B

APP : ∀ {V} → Term V → List (Term V) → Term V
APP M [] = M
APP M (N ∷ NN) = APP (appT M N) NN

data R : Reduction where

open import Reduction PHOPL R renaming (_⇒_ to _⇒R_;redex to redexR;app to appR;appl to applR;appr to apprR;creates' to creates'R)

R-creates-rep : creates'R replacement
R-creates-rep = λ _ ()

data Neutral {V} : Term V → Set where
  var : ∀ (x : Var V -Term) → Neutral (var x)
  app : ∀ {M N : Term V} → Neutral M → SN N → Neutral (appT M N)

Neutral-rep : ∀ {U} {V} (M : Term U) (ρ : Rep U V) → Neutral M → Neutral (M 〈 ρ 〉)
Neutral-rep .(var x) ρ (var x) = var (ρ _ x)
Neutral-rep {U} {V} .(appT M N) ρ (app {M} {N} M-neutral N-SN) = 
  app (Neutral-rep {U} {V} M ρ M-neutral) (SNrep R-creates-rep N-SN)

varSN : ∀ {V} (x : Var V -Term) → SN (var x)
varSN x = SNI (var x) (λ _ ())

⊥SN : ∀ {V} → SN {V} ⊥
⊥SN {V} = SNI ⊥ ⊥SN' where
  ⊥SN' : ∀ (F : Term V) → ⊥ ⇒R F → SN F
  ⊥SN' _ (redexR ())
  ⊥SN' _ (appR ())

⊃SN : ∀ {V} {φ ψ : Term V} → SN φ → SN ψ → SN (φ ⊃ ψ)
⊃SN' : ∀ {V} {φ ψ F : Term V} → SN φ → SN ψ → φ ⊃ ψ ⇒R F → SN F

⊃SN {V} {φ} {ψ} SNφ SNψ = SNI (φ ⊃ ψ) (λ _ → ⊃SN' SNφ SNψ)

⊃SN' _ _ (redexR ())
⊃SN' (SNI φ SNφ) SNψ (appR (applR {E' = φ'} φ⇒φ')) = ⊃SN (SNφ φ' φ⇒φ') SNψ
⊃SN' SNφ (SNI ψ SNψ) (appR (apprR (applR {E' = ψ'} ψ⇒ψ'))) = ⊃SN SNφ (SNψ ψ' ψ⇒ψ')
⊃SN' _ _ (appR (apprR (apprR ())))

all-SN : ∀ {V} → List (Term V) → Set
all-SN [] = ⊤
all-SN (M ∷ MM) = SN M × all-SN MM

var-APP-SN : ∀ {V} (x : Var V -Term) (MM : List (Term V)) →
  all-SN MM → SN (APP (var x) MM)
var-APP-SN {V} x MM SN-MM = {!!}

Neutral-SN-aux : ∀ {V} {M : Term V} {NN} → Neutral M → all-SN NN → SN (APP M NN)
Neutral-SN-aux (var x) NN-SN = var-APP-SN x _ NN-SN
Neutral-SN-aux (app M-neutral N-SN) NN-SN = Neutral-SN-aux {NN = _ ∷ _} M-neutral (N-SN ,p NN-SN)

Neutral-SN : ∀ {V} {M : Term V} → Neutral M → SN M
Neutral-SN (var x) = varSN x
Neutral-SN (app M-neutral N-SN) = Neutral-SN-aux {NN = [ _ ]} M-neutral (N-SN ,p tt)

E : ∀ {V} → Context V → Type ∅ → Term V → Set
E Γ (app -Omega out) φ = Γ ⊢ φ ∶ Ω × SN φ
E {V} Γ (app -func (A ,, B ,, out)) M = ∀ U Δ (ρ : Rep V U) N → E Δ A N → E Δ B (appT (M 〈 ρ 〉) N)

Neutral-E : ∀ {V} {Γ : Context V} {A : Type V} {M : Term V} →
  Neutral M → Γ ⊢ M ∶ A → E Γ (close A) M
Neutral-E {A = app -Omega out} M-neutral Γ⊢M∶Ω = Γ⊢M∶Ω ,p Neutral-SN M-neutral
Neutral-E {A = app -func (A ,, B ,, out)} {M} M-neutral Γ⊢M∶A⇒B 
  U Δ ρ N N∈EΔA = {!!}
--Neutral-E {U} {Δ} {{!A 〈 ρ 〉!}} {appT (M 〈 ρ 〉) N} (app {!!} {!!}) {!!}

var-E : ∀ {V} {Γ : Context V} {x : Var V -Term} → 
  valid Γ → E Γ (close (typeof x Γ)) (var x)
var-E {V} {Γ} {x} Γvalid = Neutral-E (var x) (varR x Γvalid)

E-sub-SN : ∀ V (Γ : Context V) A M → E Γ A M → SN M
E-sub-SN _ _ (app -Omega out) _ = proj₂
E-sub-SN V Γ (app -func (A ,, B ,, out)) M M∈EΓA⇒B = 
  {!!}

⊥-E : ∀ {V} {Γ : Context V} → valid Γ → E Γ Ω ⊥
⊥-E Γvalid = ⊥R Γvalid ,p ⊥SN

⊃-E : ∀ {V} {Γ : Context V} {φ} {ψ} → E Γ Ω φ → E Γ Ω ψ → E Γ Ω (φ ⊃ ψ)
⊃-E (Γ⊢φ∶Ω ,p φSN) (Γ⊢ψ∶Ω ,p ψSN) = impR Γ⊢φ∶Ω Γ⊢ψ∶Ω ,p ⊃SN φSN ψSN

appT-E : ∀ {V} {Γ : Context V} {M N : Term V} {A} {B} →
  E Γ (A ⇛ B) M → E Γ A N → E Γ B (appT M N)
appT-E {V} {Γ} {M} {N} {A} {B} EM EN = subst (E Γ B) 
  (cong (λ x → appT x N) rep-idOp) 
  (EM V Γ (idRep V) N EN)

EP : ∀ {V} → Context V → Term V → Proof V → Set
EP Γ φ δ = ⊤

appP-EP : ∀ {V} {Γ : Context V} {δ ε : Proof V} {φ} {ψ} →
  EP Γ (φ ⊃ ψ) δ → EP Γ φ ε → EP Γ ψ (appP δ ε)
appP-EP {V} {Γ} {δ} {ε} {φ} {ψ} tt tt = tt

EE : ∀ {V} → Context V → Equation V → Path V → Set
EE Γ E P = ⊤

_∶_⇒C_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set
σ ∶ Γ ⇒C Δ = (∀ x → E Δ (close (typeof x Γ)) (σ _ x)) × (∀ x → EP Δ (typeof x Γ ⟦ σ ⟧) (σ _ x))

_∶_∼_∶_⇒C_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ ρ ∼ σ ∶ Γ ⇒C Δ = ∀ x → EE Δ (ρ _ x ≡〈 typeof x Γ ⟦ ρ ⟧ 〉 σ _ x) (τ x)

Computable-Substitution : ∀ U V (σ : Sub U V) Γ Δ M A → 
  σ ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → valid Δ → E Δ (close A) (M ⟦ σ ⟧)
Computable-Substitution _ _ _ _ _ _ _ σ∶Γ⇒Δ (varR x _) _ = proj₁ σ∶Γ⇒Δ x
Computable-Substitution _ V _ _ Δ .⊥ .Ω _ (⊥R _) Δvalid = ⊥-E {V} {Δ} Δvalid
Computable-Substitution U V σ Γ Δ .(φ ⊃ ψ) .Ω σ∶Γ⇒Δ (impR {φ = φ} {ψ} Γ⊢φ∶Ω Γ⊢ψ∶Ω) Δvalid = ⊃-E 
  (Computable-Substitution U V σ Γ Δ φ Ω σ∶Γ⇒Δ Γ⊢φ∶Ω Δvalid) 
  (Computable-Substitution U V σ Γ Δ ψ Ω σ∶Γ⇒Δ Γ⊢ψ∶Ω Δvalid)
Computable-Substitution U V σ Γ Δ .(appT M N) .B σ∶Γ⇒Δ (appR {M = M} {N} {A} {B} Γ⊢M∶A⇒B Γ⊢N∶A) Δvalid = appT-E 
  (Computable-Substitution U V σ Γ Δ M (A ⇛ B) σ∶Γ⇒Δ Γ⊢M∶A⇒B Δvalid) 
  (Computable-Substitution U V σ Γ Δ N A σ∶Γ⇒Δ Γ⊢N∶A Δvalid)
Computable-Substitution U V σ Γ Δ _ _ σ∶Γ⇒Δ (ΛR Γ⊢M∶A) Δvalid W Θ ρ N N∈EΔA = {!!}

Computable-Proof-Substitution : ∀ U V (σ : Sub U V) Γ Δ δ φ →
  σ ∶ Γ ⇒C Δ → Γ ⊢ δ ∶ φ → valid Δ → EP Δ (φ ⟦ σ ⟧) (δ ⟦ σ ⟧)
Computable-Proof-Substitution U V σ Γ Δ .(var x) .(typeof x Γ) σ∶Γ⇒Δ (varR x x₁) Δvalid = proj₂ σ∶Γ⇒Δ x
Computable-Proof-Substitution U V σ Γ Δ .(appP δ ε) .ψ σ∶Γ⇒Δ (appPR {δ = δ} {ε} {φ} {ψ} Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) Δvalid = appP-EP {V} {Δ} {δ ⟦ σ ⟧} {ε ⟦ σ ⟧} {φ ⟦ σ ⟧} {ψ ⟦ σ ⟧}
  (Computable-Proof-Substitution U V σ Γ Δ δ (φ ⊃ ψ) σ∶Γ⇒Δ Γ⊢δ∶φ⊃ψ Δvalid) 
  (Computable-Proof-Substitution U V σ Γ Δ ε φ σ∶Γ⇒Δ Γ⊢ε∶φ Δvalid)
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒Δ (ΛPR Γ⊢δ∶φ) Δvalid = {!!}
Computable-Proof-Substitution U V σ Γ Δ δ φ σ∶Γ⇒Δ (convR Γ⊢δ∶φ Γ⊢δ∶φ₁ x) Δvalid = {!!}
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒Δ (plusR Γ⊢δ∶φ) Δvalid = {!!}
Computable-Proof-Substitution U V σ Γ Δ _ _ σ∶Γ⇒Δ (minusR Γ⊢δ∶φ) Δvalid = {!!}

Computable-Path-Substitution : ∀ U V (τ : PathSub U V) σ σ' Γ Δ M A → τ ∶ σ ∼ σ' ∶ Γ ⇒C Δ → Γ ⊢ M ∶ A → 
  EE Δ (M ⟦ σ ⟧ ≡〈 A ⟦ σ ⟧ 〉 M ⟦ σ' ⟧) (M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧) 
Computable-Path-Substitution = λ U V τ σ σ' Γ Δ M A _ _₁ → tt

Strong-Normalization : ∀ V K (Γ : Context V) (M : Expression V (varKind K)) A → Γ ⊢ M ∶ A → SN M
Strong-Normalization V -Proof Γ δ φ Γ⊢δ∶φ = {!!}
Strong-Normalization V -Term Γ M A Γ⊢M∶A = E-sub-SN V Γ (close A) M 
  (subst (E Γ (close A)) sub-idOp 
  (Computable-Substitution V V (idSub V) Γ Γ M A {!!} Γ⊢M∶A {!!}))
Strong-Normalization V -Path Γ P E Γ⊢P∶E = {!!}
\end{code}
