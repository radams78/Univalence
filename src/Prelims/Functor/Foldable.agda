module Prelims.Functor.Foldable where
open import Level
open import Function
open import Function.Equality hiding (cong) renaming (_∘_ to _○_)
open import Algebra
open import Prelims.EqReasoning
open import Prelims.Functor.Base
open import Prelims.Endo

record IsFoldable (FF : Functor) : Set₂ where
  open Functor FF
  field
    foldl : ∀ {A} {B : Set₁} → (B → A → B) → B → F A → B
    foldl-cong : ∀ {A B} {f g : B → A → B} {b} aa →
      (∀ x y → f x y ≡ g x y) → foldl f b aa ≡ foldl g b aa
    depfold₂ : ∀ {A : Set₁} {B} {C : A → A → Setoid zero zero} {f g : A → B → A} {a₁ a₂} bb →
      (∀ a₁ a₂ b → C a₁ a₂ ⟶ C (f a₁ b) (g a₂ b)) →
      C a₁ a₂ ⟶ C (foldl f a₁ bb) (foldl g a₂ bb)
--TODO Refactor

  foldl₀ : ∀ {A B : Set} → (B → A → B) → B → F A → B
  foldl₀ {A} {B} f b aa = lower (foldl (λ b' a → lift (f (lower b') a)) (lift b) aa)

  module FoldMonoid (MM : Monoid zero zero) where
    open Monoid MM renaming (Carrier to M;_∙_ to _•_)

    fold : F M → M
    fold = foldl₀ _•_ ε

    foldMap : ∀ {A} → (A → M) → F A → M
    foldMap f aa = fold (map f aa)

  open FoldMonoid public

  foldr : ∀ {A B : Set} → (A → B → B) → F A → B → B
  foldr {A} {B} = foldMap (EndoR B)

record FoldFunc : Set₂ where
  field
    functor : Functor
    isFoldable : IsFoldable functor
  open Functor functor public
  open IsFoldable isFoldable public