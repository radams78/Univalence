module Prototype where

postulate Lift : Set → Set

data Type : Set where
  Ω : Type
  _⇛_ : Type → Type → Type

data Term : Set → Set where
  var : ∀ {V} → V → Term V
  ⊥ : ∀ {V} → Term V
  app : ∀ {V} → Term V → Term V → Term V
  Λ : ∀ {V} → Type → Term (Lift V) → Term V
  _⊃_ : ∀ {V} → Term V → Term V → Term V

data Proof (V : Set) : Set → Set where
  var : ∀ {P} → P → Proof V P
  app : ∀ {P} → Proof V P → Proof V P → Proof V P
  Λ : ∀ {P} → Term V → Proof V (Lift P) → Proof V P

  
