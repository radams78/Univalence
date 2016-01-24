module Prototype3 where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data Arity : ℕ → Set where
  * : ∀ {n} → Arity n
  [_]_ : ∀ {n} → Arity n → Arity (succ n) → Arity (succ n)

Arity↑ : ∀ {n} → Arity n → Arity (succ n)
Arity↑ * = *
Arity↑ ([ α ] β) = [ Arity↑ α ] Arity↑ β

data SymbolSet : ℕ → Set where
  ∅ : ∀ {n} → SymbolSet n
  _,_ : ∀ {n} → SymbolSet n → Arity n → SymbolSet n

data Symbol {n} : SymbolSet n → Arity n → Set where
  ⊥ : ∀ {S} {α} → Symbol (S , α) α
  ↑ : ∀ {S} {α} {β} → Symbol S β → Symbol (S , α) β

Rep : ∀ {n} → SymbolSet n → SymbolSet n → Set
Rep U V = ∀ α → Symbol U α → Symbol V α

Rep↑ : ∀ {n} {U} {V} {α} → Rep {n} U V → Rep (U , α) (V , α)
Rep↑ _ _ ⊥ = ⊥
Rep↑ ρ β (↑ x) = ↑ (ρ β x)

mutual
  data Out (C : SymbolSet (succ (succ zero))) (P : SymbolSet (succ zero)) (V : SymbolSet zero) : Arity (succ (succ zero)) → Set where
    const : ∀ {α} → Symbol C α → Out C P V α
    param : ∀ {α} → Symbol P α → Out C P V (Arity↑ α)
    var   : Symbol V * → Out C P V *
    app   : ∀ {α} {β} → Out C P V ([ α ] β) → In C P V α → Out C P V β

  data In (C : SymbolSet (succ (succ zero))) (P : SymbolSet (succ zero)) :  SymbolSet zero → Arity (succ zero) → Set where
    out : ∀ {V} → Out C P V * → In C P V *
    Λ   : ∀ {V} {β} → In C P (V , *) β → In C P V ([ * ] β)

  data Kind (C : SymbolSet (succ (succ zero))) : SymbolSet (succ zero) → SymbolSet zero → Arity (succ (succ zero)) → Set where
    Type : ∀ {P} {V} → Kind C P V *
    El   : ∀ {P} {V} → Out C P V * → Kind C P V *
    Π    : ∀ {P} {V} {α} {β} → Kind C P V (Arity↑ α) → Kind C (P , α) V β → 
                         Kind C P V ([ α ] β) 

inn : ∀ {C} {P} {V} → In C P V * → Out C P V *
inn (out M) = M

Applicator : SymbolSet (succ (succ zero)) → SymbolSet (succ zero) → SymbolSet zero → Arity (succ (succ zero)) → Set
Applicator C P V * = Out C P V *
Applicator C P V ([ α ] β) = In C P V α → Applicator C P V β

apply : ∀ {C} {P} {V} {α} → Out C P V α → Applicator C P V α
apply {α = *} M = M
apply {α = [ α ] β} M = λ E → apply (app M E)

mutual
  repOV : ∀ {C} {P} {U} {V} {α} → Out C P U α → Rep U V → Out C P V α
  repOV (const c) _ = const c
  repOV (param p) _ = param p
  repOV (var x) ρ = var (ρ _ x)
  repOV (app M E) ρ = app (repOV M ρ) (repIV E ρ)

  repIV : ∀ {C} {P} {U} {V} {α} → In C P U α → Rep U V → In C P V α
  repIV (out M) ρ = out (repOV M ρ)
  repIV (Λ E) ρ = Λ (repIV E (Rep↑ ρ))

repKV : ∀ {C} {P} {U} {V} {α} → Kind C P U α → Rep U V → Kind C P V α
repKV Type _ = Type
repKV (El M) ρ = El (repOV M ρ)
repKV (Π A B) ρ = Π (repKV A ρ) (repKV B ρ)

mutual
  repOP : ∀ {C} {P} {Q} {V} {α} → Out C P V α → Rep P Q → Out C Q V α
  repOP (const c) _ = const c
  repOP (param p) ρ = param (ρ _ p)
  repOP (var x) _ = var x
  repOP (app M E) ρ = app (repOP M ρ) (repIP E ρ)  

  repIP : ∀ {C} {P} {Q} {V} {α} → In C P V α → Rep P Q → In C Q V α
  repIP (out M) ρ = out (repOP M ρ)
  repIP (Λ E) ρ = Λ (repIP E ρ)

repKP : ∀ {C} {P} {Q} {V} {α} → Kind C P V α → Rep P Q → Kind C Q V α
repKP Type _ = Type
repKP (El M) ρ = El (repOP M ρ)
repKP (Π A B) ρ = Π (repKP A ρ) (repKP B (Rep↑ ρ))

eta : ∀ {C} {P} {V} {α} → Out C P V (Arity↑ α) → In C P V α
eta {C} {P} {V} {*} M = out M
eta {C} {P} {V} {[ * ] α} M = Λ (eta (app (repOV M (λ _ → ↑)) (out (var ⊥))))

SubV : SymbolSet (succ (succ zero)) → SymbolSet (succ zero) → SymbolSet zero → SymbolSet zero → Set
SubV C P U V = Symbol U * → Out C P V *

Sub↑ : ∀ {C} {P} {U} {V} → SubV C P U V → SubV C P (U , *) (V , *)
Sub↑ σ ⊥ = var ⊥
Sub↑ σ (↑ x) = repOV (σ x) (λ _ → ↑)

⊥:= : ∀ {C} {P} {V} → Out C P V * → SubV C P (V , *) V
⊥:= M ⊥ = M
⊥:= _ (↑ x) = var x

mutual
  subOV : ∀ {C} {P} {U} {V} {α} → Out C P U α → SubV C P U V → Out C P V α
  subOV (const c) σ = const c
  subOV (param p) σ = param p
  subOV (var x) σ = σ x
  subOV (app M E) σ = app (subOV M σ) (subIV E σ)

  subIV : ∀ {C} {P} {U} {V} {α} → In C P U α → SubV C P U V → In C P V α
  subIV (out M) σ = out (subOV M σ)
  subIV (Λ E) σ = Λ (subIV E (Sub↑ σ))

subKV : ∀ {C} {P} {U} {V} {α} → Kind C P U α → SubV C P U V → Kind C P V α
subKV Type σ = Type
subKV (El M) σ = El (subOV M σ)
subKV (Π A B) σ = Π (subKV A σ) (subKV B (λ x → repOP (σ x) (λ _ → ↑)))

App : ∀ {C} {P} {V} {α} → In C P V α → Applicator C P V (Arity↑ α)
App {C} {P} {V} {*} (out M) = M
App {C} {P} {V} {[ * ] α} (Λ E) = λ F → App (subIV E (⊥:= (inn F)))

SubP↑ : ∀ {C} {P} {Q} {V} {β} → (∀ α → Symbol P α → In C Q V α) → ∀ α → Symbol (P , β) α → In C (Q , β) V α
SubP↑ σ α ⊥ = eta (param ⊥)
SubP↑ σ α (↑ p) = repIP (σ α p) (λ _ → ↑)

mutual
  SubOP : ∀ {C} {P} {Q} {V} {α} → Out C P V α → (forall β → Symbol P β → In C Q V β) → Applicator C Q V α
  SubOP (const c) _ = apply (const c)
  SubOP (param p) σ = App (σ _ p)
  SubOP (var x) _ = var x
  SubOP (app M E) σ = SubOP M σ (SubIP E σ)

  SubIP : ∀ {C} {P} {Q} {V} {α} → In C P V α → (∀ β → Symbol P β → In C Q V β) → In C Q V α
  SubIP (out M) σ = out (SubOP M σ)
  SubIP (Λ E) σ = Λ (SubIP E (λ β p → repIV (σ β p) (λ _ → ↑)))

SubKP : ∀ {C} {P} {Q} {V} {α} → Kind C P V α → (∀ β → Symbol P β → In C Q V β) → Kind C Q V α
SubKP Type _ = Type
SubKP (El M) σ = El (SubOP M σ)
SubKP (Π A B) σ = Π (SubKP A σ) (SubKP B (SubP↑ σ))
