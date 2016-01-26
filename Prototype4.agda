module Prototype4 where

data AbsKind (ExpKind : Set) : Set where
  out : ExpKind → AbsKind ExpKind
  Π   : ExpKind → AbsKind ExpKind → AbsKind ExpKind

data ConKind {ExpKind : Set} (E : ExpKind) : Set where
  out : ConKind E
  Π   : AbsKind ExpKind → ConKind E → ConKind E

record Grammar : Set₁ where
  field
    ExpKind : Set
    Constructor : ∀ {E : ExpKind} → ConKind E → Set

  data Alphabet : Set where
    ∅ : Alphabet
    _,_ : Alphabet → ExpKind → Alphabet

  data Symbol : Alphabet → ExpKind → Set where
    ⊥ : ∀ {A} {E} → Symbol (A , E) E
    ↑ : ∀ {A} {E} {F} → Symbol A F → Symbol (A , E) F

  mutual
    data Expression (A : Alphabet) (E : ExpKind) : Set where
      var : Symbol A E → Expression A E
      app : ∀ {C : ConKind E} →
            Constructor C → Body A E C → Expression A E

    data Body (A : Alphabet) (E : ExpKind) : ConKind E → Set where
      [] : Body A E out
      _∷_ : ∀ {B} {C} → Abstraction A B → Body A E C → Body A E (Π B C)

    data Abstraction : Alphabet → AbsKind ExpKind → Set where
      out : ∀ {A} {E} → Expression A E → Abstraction A (out E)
      Λ   : ∀ {A} {B} {C} → Abstraction (A , B) C → Abstraction A (Π B C)

  Rep : Alphabet → Alphabet → Set
  Rep A B = ∀ E → Symbol A E → Symbol B E

  Rep↑ : ∀ {A} {B} {E} → Rep A B → Rep (A , E) (B , E)
  Rep↑ _ _ ⊥ = ⊥
  Rep↑ ρ E (↑ x) = ↑ (ρ E x)

  mutual
    repE : ∀ {A} {B} {E} → Rep A B → Expression A E → Expression B E
    repE ρ (var x) = var (ρ _ x)
    repE ρ (app c EE) = app c (repB ρ EE)

    repB : ∀ {A} {B} {E} {C} → Rep A B → Body A E C → Body B E C
    repB _ [] = []
    repB ρ (A ∷ EE) = repA ρ A ∷ repB ρ EE

    repA : ∀ {A} {B} {K} → Rep A B → Abstraction A K → Abstraction B K
    repA ρ (out E) = out (repE ρ E)
    repA ρ (Λ E) = Λ (repA (Rep↑ ρ) E)

  Sub : Alphabet → Alphabet → Set
  Sub A B = ∀ E → Symbol A E → Expression B E

  Sub↑ : ∀ {A} {B} {E} → Sub A B → Sub (A , E) (B , E)
  Sub↑ _ _ ⊥ = var ⊥
  Sub↑ σ E (↑ x) = repE (λ _ → ↑) (σ E x)

  mutual
    subE : ∀ {A} {B} {E} → Sub A B → Expression A E → Expression B E
    subE σ (var x) = σ _ x
    subE σ (app c EE) = app c (subB σ EE)

    subB : ∀ {A} {B} {E} {C} → Sub A B → Body A E C → Body B E C
    subB _ [] = []
    subB σ (A ∷ EE) = subA σ A ∷ subB σ EE

    subA : ∀ {A} {B} {K} → Sub A B → Abstraction A K → Abstraction B K
    subA σ (out E) = out (subE σ E)
    subA σ (Λ A₁) = Λ (subA (Sub↑ σ) A₁)

data PLExpKind : Set where
  Proof : PLExpKind
  Prp  : PLExpKind

data PLConstant : ∀ (E : PLExpKind) → ConKind E → Set where
  ⊥ : PLConstant Prp out
  ⇒ : PLConstant Prp (Π (out Prp) (Π (out Prp) out))
  app : PLConstant Proof (Π (out Proof) (Π (out Proof) out))
  Λ   : PLConstant Proof (Π (out Prp) (Π (Π Proof (out Proof)) out))

Propositional-Logic : Grammar
Propositional-Logic = record { 
  ExpKind = PLExpKind; 
  Constructor = PLConstant _ }

PROOF : Grammar.Alphabet Propositional-Logic → Set
PROOF A = Grammar.Expression Propositional-Logic A Proof
