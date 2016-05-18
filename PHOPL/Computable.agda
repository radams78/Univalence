module PHOPL.Computable where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Sum
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL
open import PHOPL.Neutral
open import PHOPL.Rules
open import PHOPL.Close
open import PHOPL.Red
open import PHOPL.Meta

record EΩ {V} (Γ : Context V) (M : Term V) : Set where
  field
    typed : Γ ⊢ M ∶ Ω
    sn    : SN M

--TODO Reorganised as typed plus condition

E : ∀ {V} → Context V → Type ∅ → Term V → Set
E Γ (app -Omega out) = EΩ Γ
E Γ (app -func (A ,, B ,, out)) M = Γ ⊢ M ∶ ty A ⇛ ty B × (∀ W (Δ : Context W) ρ N → ρ ∶ Γ ⇒R Δ → E Δ A N → E Δ B (appT (M 〈 ρ 〉) N)) 

postulate Neutral-E : ∀ {V} {Γ : Context V} {A : Type V} {M : Term V} →
              Neutral M → Γ ⊢ M ∶ A → E Γ (close A) M

var-E : ∀ {V} {Γ : Context V} {x : Var V -Term} → 
  valid Γ → E Γ (close (typeof x Γ)) (var x)
var-E {V} {Γ} {x} Γvalid = Neutral-E (var x) (varR x Γvalid)

postulate E-SN : ∀ {V} {Γ : Context V} A {M} → E Γ A M → SN M

postulate ⊥-E : ∀ {V} {Γ : Context V} → valid Γ → E Γ Ω ⊥

postulate ⊃-E : ∀ {V} {Γ : Context V} {φ} {ψ} → E Γ Ω φ → E Γ Ω ψ → E Γ Ω (φ ⊃ ψ)

postulate appT-E : ∀ {V} {Γ : Context V} {M N : Term V} {A} {B} →
                 valid Γ → E Γ (A ⇛ B) M → E Γ A N → E Γ B (appT M N)

postulate func-E : ∀ {U} {Γ : Context U} {M : Term U} {A} {B} →
                   (∀ V Δ (ρ : Rep U V) (N : Term V) → valid Δ → ρ ∶ Γ ⇒R Δ → E Δ A N → E Δ B (appT (M 〈 ρ 〉) N)) →
                   E Γ (A ⇛ B) M

postulate expand-E : ∀ {V} {Γ : Context V} {A : Type V} {B : Type ∅} {M : Term (V , -Term)} {N : Term V} →
                   E Γ B (M ⟦ x₀:= N ⟧) → E Γ B (appT (ΛT A M) N)

postulate E-typed : ∀ {V} {Γ : Context V} {A} {M} → E Γ A M → Γ ⊢ M ∶ A 〈 magic 〉

data closed-prop : Set where
  ⊥C : closed-prop
  _⊃C_ : closed-prop → closed-prop → closed-prop

cp2term : ∀ {V} → closed-prop → Term V
cp2term ⊥C = ⊥
cp2term (φ ⊃C ψ) = cp2term φ ⊃ cp2term ψ

postulate cp-typed : ∀ {V} {Γ : Context V} {A} → valid Γ → Γ ⊢ cp2term A ∶ Ω

postulate closed-rep : ∀ {U} {V} {ρ : Rep U V} (A : closed-prop) → (cp2term A) 〈 ρ 〉 ≡ cp2term A

compute : ∀ {V} → Context V → closed-prop → Proof V → Set
compute Γ ⊥C δ = SN δ
compute Γ (φ ⊃C ψ) δ = ∀ W (Δ : Context W) ρ ε → ρ ∶ Γ ⇒R Δ → Δ ⊢ ε ∶ cp2term φ → compute Δ φ ε → compute Δ ψ (appP (δ 〈 ρ 〉) ε)

EP : ∀ {V} → Context V → Term V → Proof V → Set
EP Γ φ δ = Γ ⊢ δ ∶ φ × Σ[ ψ ∈ closed-prop ] (φ ↠ cp2term ψ × compute Γ ψ δ)

postulate red-conv : ∀ {V} {C} {K} {E F : Subexpression V C K} → E ↠ F → E ≃ F

postulate ⊃-not-⊥ : ∀ {V} {φ ψ : Term V} → φ ⊃ ψ ↠ ⊥ → Empty

postulate ⊃-inj₁ : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ↠ φ' ⊃ ψ' → φ ↠ φ'

postulate ⊃-inj₂ : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ↠ φ' ⊃ ψ' → ψ ↠ ψ'

postulate confluent : ∀ {V} {φ : Term V} {ψ ψ' : closed-prop} → φ ↠ cp2term ψ → φ ↠ cp2term ψ' → ψ ≡ ψ'

postulate confluent₂ : ∀ {V} {φ ψ : Term V} {χ : closed-prop} → φ ≃ ψ → φ ↠ cp2term χ → ψ ↠ cp2term χ

postulate NF : ∀ {V} {Γ} {φ : Term V} → Γ ⊢ φ ∶ Ω → closed-prop

postulate red-NF : ∀ {V} {Γ} {φ : Term V} (Γ⊢φ∶Ω : Γ ⊢ φ ∶ Ω) → φ ↠ cp2term (NF Γ⊢φ∶Ω)

postulate EP-typed : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} →
                   EP Γ φ δ → Γ ⊢ δ ∶ φ

appP-EP : ∀ {V} {Γ : Context V} {δ ε : Proof V} {φ} {ψ} →
          EP Γ (φ ⊃ ψ) δ → EP Γ φ ε → EP Γ ψ (appP δ ε)
appP-EP (_ ,p ⊥C ,p φ⊃ψ↠⊥ ,p _) _ = ⊥-elim (⊃-not-⊥ φ⊃ψ↠⊥)
appP-EP {V} {Γ} {ε = ε} {φ} {ψ = ψ} (Γ⊢δ∶φ⊃ψ ,p (φ' ⊃C ψ') ,p φ⊃ψ↠φ'⊃ψ' ,p computeδ) (Γ⊢ε∶φ ,p φ'' ,p φ↠φ'' ,p computeε) = 
  (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) ,p ψ' ,p ⊃-inj₂ φ⊃ψ↠φ'⊃ψ' ,p 
  subst (λ x → compute Γ ψ' (appP x ε)) rep-idOp 
  (computeδ V Γ (idRep V) ε idRep-typed 
    (convR Γ⊢ε∶φ (cp-typed {A = φ'} (Context-Validity Γ⊢ε∶φ)) (red-conv (⊃-inj₁ φ⊃ψ↠φ'⊃ψ')))
  (subst (λ x → compute Γ x ε) (confluent φ↠φ'' (⊃-inj₁ φ⊃ψ↠φ'⊃ψ')) computeε))

conv-EP : ∀ {V} {Γ : Context V} {φ ψ : Term V} {δ : Proof V} →
          φ ≃ ψ → EP Γ φ δ → Γ ⊢ ψ ∶ Ω → EP Γ ψ δ
conv-EP φ≃ψ (Γ⊢δ∶φ ,p φ' ,p φ↠φ' ,p computeδ) Γ⊢ψ∶Ω = convR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ ,p φ' ,p confluent₂ {χ = φ'} φ≃ψ φ↠φ' ,p computeδ

func-EP : ∀ {U} {Γ : Context U} {δ : Proof U} {φ} {ψ} →
          (∀ V Δ (ρ : Rep U V) (ε : Proof V) → valid Δ → ρ ∶ Γ ⇒R Δ → EP Δ (φ 〈 ρ 〉) ε → EP Δ (ψ 〈 ρ 〉) (appP (δ 〈 ρ 〉) ε)) → -- TODO Remove "valid Δ"?
          Γ ⊢ δ ∶ φ ⊃ ψ → EP Γ (φ ⊃ ψ) δ
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
                      let ε∈EΔψ = hyp W Δ ρ ε (Context-Validity Δ⊢ε∶φ) ρ∶Γ⇒Δ        
                                  ((convR Δ⊢ε∶φ (Weakening Γ⊢φ∶Ω (Context-Validity Δ⊢ε∶φ) ρ∶Γ⇒Δ) (sym-conv (red-conv φρ↠φ')) ) ,p φ' ,p φρ↠φ' ,p computeε ) in 
                      let ψ' = proj₁ (proj₂ ε∈EΔψ) in 
                      let ψρ↠ψ' : ψ 〈 ρ 〉 ↠ cp2term ψ'
                          ψρ↠ψ' = proj₁ (proj₂ (proj₂ ε∈EΔψ)) in 
                      subst (λ a → compute Δ a (appP (δ 〈 ρ 〉) ε)) (confluent ψρ↠ψ' 
                        (subst (λ x → (ψ 〈 ρ 〉) ↠ x) (closed-rep (NF Γ⊢ψ∶Ω)) (respects-red (respects-osr replacement β-respects-rep) (red-NF Γ⊢ψ∶Ω)))) 
                        (proj₂ (proj₂ (proj₂ ε∈EΔψ))))

postulate expand-EP : ∀ {V} {Γ : Context V} {φ : Term V} {δ ε : Proof V} →
                   EP Γ φ ε → Γ ⊢ δ ∶ φ → δ ⇒R ε → SN δ → EP Γ φ δ

postulate EP-SN : ∀ {V} {Γ : Context V} {δ} {φ} → EP Γ φ δ → SN δ

postulate EE : ∀ {V} → Context V → Equation V → Path V → Set

postulate ref-EE : ∀ {V} {Γ : Context V} {M : Term V} {A : Type V} → E Γ (close A) M → EE Γ (M ≡〈 A 〉 M) (reff M)

postulate univ-EE : ∀ {V} {Γ : Context V} {φ ψ : Term V} {δ ε : Proof V} →
                  EP Γ (φ ⊃ ψ) δ → EP Γ (ψ ⊃ φ) ε → EE Γ (φ ≡〈 Ω 〉 ψ) (univ φ ψ δ ε)

postulate imp*-EE : ∀ {V} {Γ : Context V} {φ φ' ψ ψ' : Term V} {P Q : Path V} →
                  EE Γ (φ ≡〈 Ω 〉 φ') P → EE Γ (ψ ≡〈 Ω 〉 ψ') Q → EE Γ (φ ⊃ ψ ≡〈 Ω 〉 φ' ⊃ ψ') (P ⊃* Q)

postulate app*-EE : ∀ {V} {Γ : Context V} {M} {M'} {N} {N'} {A} {B} {P} {Q} →
                  EE Γ (M ≡〈 A ⇛ B 〉 M') P → EE Γ (N ≡〈 A 〉 N') Q →
                  EE Γ (appT M N ≡〈 B 〉 appT M' N') (app* N N' P Q)

postulate plus-EP : ∀ {V} {Γ : Context V} {P : Path V} {φ ψ : Term V} →
                  EE Γ (φ ≡〈 Ω 〉 ψ) P → EP Γ (φ ⊃ ψ) (plus P)

postulate minus-EP : ∀ {V} {Γ : Context V} {P : Path V} {φ ψ : Term V} →
                   EE Γ (φ ≡〈 Ω 〉 ψ) P → EP Γ (ψ ⊃ φ) (minus P)

postulate func-EE : ∀ {U} {Γ : Context U} {A} {B} {M} {M'} {P} →
                   (∀ V (Δ : Context V) (N N' : Term V) Q ρ → ρ ∶ Γ ⇒R Δ → valid Δ → 
                     E Δ (close A) N → E Δ (close A) N' → EE Δ (N ≡〈 A 〈 ρ 〉 〉 N') Q →
                     EE Δ (appT (M 〈 ρ 〉) N ≡〈 B 〈 ρ 〉 〉 appT (M' 〈 ρ 〉) N') (app* N N' (P 〈 ρ 〉) Q)) →
                   EE Γ (M ≡〈 A ⇛ B 〉 M') P

postulate expand-EE : ∀ {V} {Γ : Context V} {A} {M N : Term V} {P Q} →
                   EE Γ (M ≡〈 A 〉 N) Q → Γ ⊢ P ∶ M ≡〈 A 〉 N → P ⇒R Q → SN P → EE Γ (M ≡〈 A 〉 N) P

postulate conv-EE : ∀ {V} {Γ : Context V} {E} {E'} {P} →
                  EE Γ E P → E ≃ E' → EE Γ E' P

postulate rep-EE : ∀ {U} {V} {Γ} {Δ} {ρ : Rep U V} {E} {P} →
                 EE Γ E P → ρ ∶ Γ ⇒R Δ → EE Δ (E 〈 ρ 〉) (P 〈 ρ 〉)

postulate EE-typed : ∀ {V} {Γ : Context V} {E} {P} →
                   EE Γ E P → Γ ⊢ P ∶ E

postulate EE-SN : ∀ {V} {Γ : Context V} E {P} → EE Γ E P → SN P
