module PHOPL.HeadRed where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.PathSub
open import PHOPL.Rules

data _⇒_ : ∀ {V K} → VExpression V K → VExpression V K → Set where
  βP : ∀ {V A} {M N : Term V} {P Q} → app* M N (λλλ A P) Q ⇒ P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧
  appPl : ∀ {V} {δ δ' ε : Proof V} → δ ⇒ δ' → appP δ ε ⇒ appP δ' ε

_↠_ : ∀ {V K} → VExpression V K → VExpression V K → Set
_↠_ = RTClose _⇒_

data Neutral {V} : Proof V → Set
data Nmble : ∀ {V K} → VExpression V K → Set

data Neutral {V} where
  var : ∀ (p : Var V -Proof) → Neutral (var p)
  app : ∀ {δ ε} → Neutral δ → Nmble ε → Neutral (appP δ ε)

data Nmble where
  neutral : ∀ {V} {δ : Proof V} → Neutral δ → Nmble δ
  Λ       : ∀ {V} {φ : Term V} {δ} → Nmble δ → Nmble (ΛP φ δ)

data PCtxt : Alphabet → Set where
  〈〉 : PCtxt ∅
  _,_ : ∀ {V} → PCtxt V → Term V → PCtxt (V , -Proof)

data CanonForm : Set where
  bot : CanonForm
  _imp_ : CanonForm → CanonForm → CanonForm

decode : ∀ {V} → CanonForm → Term V
decode bot = ⊥
decode (φ imp ψ) = decode φ ⊃ decode ψ

CProof : ∀ {V} → Proof V → CanonForm → Set
CProof {V} δ bot = Σ[ ε ∈ Proof V ] Neutral ε × δ ↠ ε
CProof δ (φ imp ψ) = ∀ ε → CProof ε φ → CProof (appP δ ε) φ

CProofWTE : ∀ {V} {δ ε : Proof V} {φ : CanonForm} → δ ⇒ ε → CProof ε φ → CProof δ φ
CProofWTE {φ = bot} δ⇒ε (ε' ,p neutralε' ,p ε↠ε') = ε' ,p neutralε' ,p RTClose.trans (inc δ⇒ε) ε↠ε'
CProofWTE {φ = φ imp ψ} δ⇒ε computeε ε' computeε' = CProofWTE (appPl δ⇒ε) (computeε ε' computeε')

CPath : ∀ {V} → Path V → Term V → Type → Term V → Set
CPath P φ Ω ψ = Σ[ φ' ∈ CanonForm ] Σ[ ψ' ∈ CanonForm ] φ ↠ decode φ' × ψ ↠ decode ψ' × CProof (plus P) (φ' imp ψ') × CProof (minus P) (ψ' imp φ') 
CPath P M (A ⇛ B) M' = ∀ {N N' Q} → CPath Q N A N' → CPath (app* N N' P Q) (appT M N) B (appT M' N') 

repSub : ∀ {V} → PathSub V V
repSub {∅} ()
repSub {V , -Proof} (↑ x) = repSub {V} x ⇑
repSub {V , -Term} x = reff (var x)
repSub {V , -Path} (↑ x) = repSub {V} x ⇑

⊩_∶_ : ∀ {V K} → VExpression V K → Expression V (parent K) → Set
⊩_∶_ {K = -Proof} δ φ = Σ[ ψ ∈ CanonForm ] φ ↠ decode ψ × CProof δ ψ
⊩_∶_ {K = -Path} P (app (-eq A) (M ∷ N ∷ [])) = CPath P M A N
⊩_∶_ {V} {K = -Term} M (app (-ty A) []) = CPath (M ⟦⟦ repSub ∶ idSub V ∼ idSub V ⟧⟧) M A M

Lmapp* : ∀ {V} {M M' N N' : Term V} {P Q A B} → ⊩ P ∶ M ≡〈 A ⇛ B 〉 M' → ⊩ Q ∶ N ≡〈 A 〉 N' →
  ⊩ app* N N' P Q ∶ appT M N ≡〈 B 〉 appT M' N'
Lmapp* ⊩P∶M≡M' = ⊩P∶M≡M'

Lmapp : ∀ {V} {M N : Term V} {A} {B} → ⊩ M ∶ ty (A ⇛ B) → ⊩ N ∶ ty A → ⊩ appT M N ∶ ty B
Lmapp {V} {M} {N} {A} {B} ⊩M∶A⇛B ⊩N∶A = subst
  (λ x →
    CPath
    (app* (N ⟦ idSub V ⟧) (N ⟦ idSub V ⟧)
      (M ⟦⟦ repSub ∶ idSub V ∼ idSub V ⟧⟧)
      (N ⟦⟦ repSub ∶ idSub V ∼ idSub V ⟧⟧))
      (appT M x) B (appT M x))
  sub-idSub (Lmapp* {V} {M} {M} {N ⟦ idSub V ⟧} {N ⟦ idSub V ⟧} {M ⟦⟦ repSub ∶ idSub V ∼ idSub V ⟧⟧} {N ⟦⟦ repSub ∶ idSub V ∼ idSub V ⟧⟧} {A} {B} ⊩M∶A⇛B 
  (subst₂ (λ a b → CPath (N ⟦⟦ repSub ∶ idSub V ∼ idSub V ⟧⟧) a A b) (Prelims.sym sub-idSub) (Prelims.sym sub-idSub) ⊩N∶A))

WTE : ∀ {V K E E' A} → E ⇒ E' → ⊩_∶_ {V} {K} E' A → ⊩ E ∶ A
WTE {K = -Proof} δ⇒δ' (φ' ,p φ↠φ' ,p computeδ') = φ' ,p φ↠φ' ,p CProofWTE δ⇒δ' computeδ'
WTE {K = -Term} E⇒E' ⊩E'∶A = {!!}
WTE {K = -Path} E⇒E' ⊩E'∶A = {!!}

⊩s_∶_ : ∀ {U V} → Sub V U → Context V → Set
⊩s σ ∶ Δ = ∀ {K} z → ⊩_∶_ {K = K} (σ K z) (typeof z Δ ⟦ σ ⟧)

⊩p_∶_≡_∶_ : ∀ {U V} → PathSub V U → Sub V U → Sub V U → Context V → Set
⊩p τ ∶ ρ ≡ σ ∶ Γ = ∀ x → ⊩ (τ x) ∶ (ρ _ x) ≡〈 yt (typeof x Γ) 〉 (σ _ x)

MainTheorem : ∀ {U V K Γ} {E : VExpression V K} {A : Expression V (parent K)} {σ : Sub V U} →
  Γ ⊢ E ∶ A → ⊩s σ ∶ Γ → ⊩ E ⟦ σ ⟧ ∶ A ⟦ σ ⟧
MainTheoremP : ∀ {U V Γ} {M : Term V} {A : Type} {τ : PathSub V U} {ρ σ} →
  Γ ⊢ M ∶ ty A → ⊩p τ ∶ ρ ≡ σ ∶ Γ → ⊩ M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ∶ M ⟦ ρ ⟧ ≡〈 A 〉 M ⟦ σ ⟧

MainTheorem (varR x validΓ) ⊩sσ∶Γ = ⊩sσ∶Γ x
MainTheorem (appR Γ⊢M∶A⇛B Γ⊢N∶A) ⊩sσ∶Γ = Lmapp (MainTheorem Γ⊢M∶A⇛B ⊩sσ∶Γ) (MainTheorem Γ⊢N∶A ⊩sσ∶Γ)
MainTheorem (ΛR Γ⊢E∶A) ⊩sσ∶Γ ⊩Q∶N≡N' = {!!}
MainTheorem (⊥R validΓ) ⊩sσ∶Γ = {!!}
MainTheorem (⊃R Γ⊢E∶A Γ⊢E∶A₁) ⊩sσ∶Γ = {!!}
MainTheorem (appPR Γ⊢E∶A Γ⊢E∶A₁) ⊩sσ∶Γ = {!!}
MainTheorem (ΛPR Γ⊢E∶A Γ⊢E∶A₁ Γ⊢E∶A₂) ⊩sσ∶Γ = {!!}
MainTheorem (convR Γ⊢E∶A Γ⊢E∶A₁ x) ⊩sσ∶Γ = {!!}
MainTheorem (refR Γ⊢E∶A) ⊩sσ∶Γ = {!!}
MainTheorem (⊃*R Γ⊢E∶A Γ⊢E∶A₁) ⊩sσ∶Γ = {!!}
MainTheorem (univR Γ⊢E∶A Γ⊢E∶A₁) ⊩sσ∶Γ = {!!}
MainTheorem (plusR Γ⊢E∶A) ⊩sσ∶Γ = {!!}
MainTheorem (minusR Γ⊢E∶A) ⊩sσ∶Γ = {!!}
MainTheorem (lllR Γ⊢E∶A) ⊩sσ∶Γ x = {!!}
MainTheorem (app*R Γ⊢E∶A Γ⊢E∶A₁ Γ⊢E∶A₂ Γ⊢E∶A₃) ⊩sσ∶Γ = {!!}
MainTheorem (convER Γ⊢E∶A Γ⊢E∶A₁ Γ⊢E∶A₂ M≃M' N≃N') ⊩sσ∶Γ = {!!}

MainTheoremP = {!!}
