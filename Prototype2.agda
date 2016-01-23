module Prototype2 where

data Arity0 : Set where
  * : Arity0

data Arity1 : Set where
  * : Arity1
  [_]_ : Arity0 → Arity1 → Arity1

data Arity2 : Set where
  * : Arity2
  [_]_ : Arity1 → Arity2 → Arity2

Arity↑ : Arity1 → Arity2
Arity↑ * = *
Arity↑ ([ * ] β) = [ * ] Arity↑ β

data Arity3 : Set where
  * : Arity3
  [_]_ : Arity2 → Arity3 → Arity3

data VariableSet : Set where
  ∅ : VariableSet
  _,* : VariableSet → VariableSet

data Variable : VariableSet → Set where
  ⊥ : ∀ {V} → Variable (V ,*)
  ↑ : ∀ {V} → Variable V → Variable (V ,*)

RepV↑ : ∀ {U} {V} → (Variable U → Variable V) → Variable (U ,*) → Variable (V ,*)
RepV↑ ρ ⊥ = ⊥
RepV↑ ρ (↑ x) = ↑ (ρ x)

data ParameterSet : Set where
  ∅ : ParameterSet
  _,_ : ParameterSet → Arity1 → ParameterSet

data Parameter : ParameterSet → Arity1 → Set where
  ⊥ : ∀ {P} {α} → Parameter (P , α) α
  ↑ : ∀ {P} {α} {β} → Parameter P β → Parameter (P , α) β

RepP↑ : ∀ {P} {Q} {α} → (∀ β → Parameter P β → Parameter Q β) → ∀ β → Parameter (P , α) β → Parameter (Q , α) β
RepP↑ ρ _ ⊥ = ⊥
RepP↑ ρ β (↑ p) = ↑ (ρ β p)

Lift : VariableSet → ParameterSet
Lift ∅ = ∅
Lift (X ,*) = Lift X , *

data ConstantSet : Set where
  ∅ : ConstantSet
  _,_ : ConstantSet → Arity2 → ConstantSet

data Constant : ConstantSet → Arity2 → Set where
  ⊥ : ∀ {C} {α} → Constant (C , α) α
  ↑ : ∀ {C} {α} {β} → Constant C α → Constant (C , β) α

mutual
  data In (C : ConstantSet) (P : ParameterSet) :  VariableSet → Arity1 → Set where
    out : ∀ {V} → Out C P V * → In C P V *
    Λ   : ∀ {V} {β} → In C P (V ,*) β → In C P V ([ * ] β)

  data Out (C : ConstantSet) (P : ParameterSet) (V : VariableSet) : Arity2 → Set where
    const : ∀ {α} → Constant C α → Out C P V α
    param : ∀ {α} → Parameter P α → Out C P V (Arity↑ α)
    var   : Variable V → Out C P V *
    app   : ∀ {α} {β} → Out C P V ([ α ] β) → In C P V α → Out C P V β

  data Kind (C : ConstantSet) : ParameterSet → VariableSet → Arity2 → Set where
    Type : ∀ {P} {V} → Kind C P V *
    El   : ∀ {P} {V} → Out C P V * → Kind C P V *
    Π    : ∀ {P} {V} {α} {β} → Kind C P V (Arity↑ α) → Kind C (P , α) V β → 
                         Kind C P V ([ α ] β) 

mutual
  repIV : ∀ {C} {P} {U} {V} {α} → In C P U α → (Variable U → Variable V) → In C P V α
  repIV (out M) ρ = out (repOV M ρ)
  repIV (Λ E) ρ = Λ (repIV E (RepV↑ ρ))

  repOV : ∀ {C} {P} {U} {V} {α} → Out C P U α → (Variable U → Variable V) → Out C P V α
  repOV (const c) _ = const c
  repOV (param p) _ = param p
  repOV (var x) ρ = var (ρ x)
  repOV (app M E) ρ = app (repOV M ρ) (repIV E ρ)

  repKV : ∀ {C} {P} {U} {V} {α} → Kind C P U α → (Variable U → Variable V) → Kind C P V α
  repKV Type _ = Type
  repKV (El M) ρ = El (repOV M ρ)
  repKV (Π A B) ρ = Π (repKV A ρ) (repKV B ρ)

mutual
  repOP : ∀ {C} {P} {Q} {V} {α} → Out C P V α → (∀ β → Parameter P β → Parameter Q β) → Out C Q V α
  repOP (const c) _ = const c
  repOP (param p) ρ = param (ρ _ p)
  repOP (var x) _ = var x
  repOP (app M E) ρ = app (repOP M ρ) (repIP E ρ)  

  repIP : ∀ {C} {P} {Q} {V} {α} → In C P V α → (∀ β → Parameter P β → Parameter Q β) → In C Q V α
  repIP (out M) ρ = out (repOP M ρ)
  repIP (Λ E) ρ = Λ (repIP E ρ)

  repKP : ∀ {C} {P} {Q} {V} {α} → Kind C P V α → (∀ β → Parameter P β → Parameter Q β) → Kind C Q V α
  repKP Type _ = Type
  repKP (El M) ρ = El (repOP M ρ)
  repKP (Π A B) ρ = Π (repKP A ρ) (repKP B (RepP↑ ρ))

inn : ∀ {C} {P} {V} → In C P V * → Out C P V *
inn (out M) = M

eta : ∀ {C} {P} {V} {α} → Out C P V (Arity↑ α) → In C P V α
eta {C} {P} {V} {*} M = out M
eta {C} {P} {V} {[ * ] α} M = Λ (eta (app (repOV M ↑) (out (var ⊥))))

Applicator : ConstantSet → ParameterSet → VariableSet → Arity2 → Set
Applicator C P V * = Out C P V *
Applicator C P V ([ α ] β) = In C P V α → Applicator C P V β

apply : ∀ {C} {P} {V} {α} → Out C P V α → Applicator C P V α
apply {α = *} M = M
apply {α = [ α ] β} M = λ E → apply (app M E)

Sub↑ : ∀ {C} {P} {U} {V} → (Variable U → Out C P V *) → Variable (U ,*) → Out C P (V ,*) *
Sub↑ σ ⊥ = var ⊥
Sub↑ σ (↑ x) = repOV (σ x) ↑

⊥:= : ∀ {C} {P} {V} → Out C P V * → Variable (V ,*) → Out C P V *
⊥:= M ⊥ = M
⊥:= _ (↑ x) = var x

mutual
  subO : ∀ {C} {P} {U} {V} {α} → Out C P U α → (Variable U → Out C P V *) → Out C P V α
  subO (const c) σ = const c
  subO (param p) σ = param p
  subO (var x) σ = σ x
  subO (app M E) σ = app (subO M σ) (subI E σ)

  subI : ∀ {C} {P} {U} {V} {α} → In C P U α → (Variable U → Out C P V *) → In C P V α
  subI (out M) σ = out (subO M σ)
  subI (Λ E) σ = Λ (subI E (Sub↑ σ))

  subK : ∀ {C} {P} {U} {V} {α} → Kind C P U α → (Variable U → Out C P V *) → Kind C P V α
  subK Type σ = Type
  subK (El M) σ = El (subO M σ)
  subK (Π A B) σ = Π (subK A σ) (subK B (λ x → repOP (σ x) (λ _ → ↑)))

App : ∀ {C} {P} {V} {α} → In C P V α → Applicator C P V (Arity↑ α)
App {C} {P} {V} {*} (out M) = M
App {C} {P} {V} {[ * ] α} (Λ E) = λ F → App (subI E (⊥:= (inn F)))

SubP↑ : ∀ {C} {P} {Q} {V} {β} → (∀ α → Parameter P α → In C Q V α) → ∀ α → Parameter (P , β) α → In C (Q , β) V α
SubP↑ σ α ⊥ = eta (param ⊥)
SubP↑ σ α (↑ p) = repIP (σ α p) (λ _ → ↑)

mutual
  SubO : ∀ {C} {P} {Q} {V} {α} → Out C P V α → (forall β → Parameter P β → In C Q V β) → Applicator C Q V α
  SubO (const c) _ = apply (const c)
  SubO (param p) σ = App (σ _ p)
  SubO (var x) _ = var x
  SubO (app M E) σ = SubO M σ (SubI E σ)

  SubI : ∀ {C} {P} {Q} {V} {α} → In C P V α → (∀ β → Parameter P β → In C Q V β) → In C Q V α
  SubI (out M) σ = out (SubO M σ)
  SubI (Λ E) σ = Λ (SubI E (λ β p → repIV (σ β p) ↑))

  SubK : ∀ {C} {P} {Q} {V} {α} → Kind C P V α → (∀ β → Parameter P β → In C Q V β) → Kind C Q V α
  SubK Type _ = Type
  SubK (El M) σ = El (SubO M σ)
  SubK (Π A B) σ = Π (SubK A σ) (SubK B (SubP↑ σ))
