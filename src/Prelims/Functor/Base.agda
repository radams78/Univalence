module Prelims.Functor.Base where
open import Function
open import Relation.Binary.PropositionalEquality

record Functor : Set₁ where
  field
    F : Set → Set
    map : ∀ {A B} → (A → B) → F A → F B
    map-cong : ∀ {A B} {f g : A → B} {aa} → (∀ x → f x ≡ g x) → map f aa ≡ map g aa
    map-id : ∀ {A} {aa : F A} → map (λ x → x) aa ≡ aa
    map-comp : ∀ {A B C} {g : B → C} {f : A → B} {aa} →
      map (g ∘ f) aa ≡ map g (map f aa)
