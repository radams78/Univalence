module Prelims.Foldable where
open import Level
open import Data.List hiding (map;foldl)
open import Algebra
open import Function.Equality hiding (cong)
open import Prelims.EqReasoning
open import Prelims.Endo

record FoldFunc : Set₁ where
  field
    o : Set → Set
    map : ∀ {A B} → (A → B) → o A → o B
    map-cong : ∀ {A B} {f g : A → B} {aa : o A} →
      (∀ x → f x ≡ g x) → map f aa ≡ map g aa
    fold : ∀ (M : Monoid zero zero) → o (Monoid.Carrier M) → Monoid.Carrier M
    depfold₂ : ∀ {A B : Set} {C : A → A → Setoid zero zero} {f : A → B → A} {a₁ a₂} bb →
      (∀ a₁ a₂ b → C a₁ a₂ ⟶ C (f a₁ b) (f a₂ b)) →
      C a₁ a₂ ⟶ C (fold (EndoR A) (map (λ y x → f x y) bb) a₁) (fold (EndoR A) (map (λ y x → f x y) bb) a₂)

  foldMap : ∀ {A} M → (A → Monoid.Carrier M) → o A → Monoid.Carrier M
  foldMap {A} M f aa = fold M (map f aa)

  foldMap-nat : ∀ {A} M {f : A → Monoid.Carrier M} {aa : o A} {g : A → A} {m : Monoid.Carrier M} →
    (∀ x → Monoid._≈_ M (Monoid._∙_ M m (f (g x))) (Monoid._∙_ M (f x) m)) →
    Monoid._≈_ M (Monoid._∙_ M m (foldMap M f (map g aa))) (Monoid._∙_ M (foldMap M f aa) m)
  foldMap-nat M hyp = {!!}

  foldl : ∀ {A B : Set} → (A → B → A) → A → o B → A
  foldl {A} {B} f a bb = foldMap (EndoR A) (λ b a → f a b) bb a

  foldl-map : ∀ {A B : Set} {f : A → B → A} {g : A → A} {h : B → B} {a : A} {bb : o B} →
    (∀ a b → f (g a) (h b) ≡ g (f a b)) →
    g (foldl f a bb) ≡ foldl f (g a) (map h bb)
  foldl-map {A} {B} {f} {g} {h} {a} {bb} hyp = sym (foldMap-nat (EndoR A) {λ x y → f y x} {bb} {h} {g} (λ b a → hyp a b) a)

map-cong : ∀ {A B : Set} {f g : A → B} {aa : List A} → (∀ x → f x ≡ g x) → Data.List.map f aa ≡ Data.List.map g aa
map-cong {aa = []} f≡g = refl
map-cong {aa = a ∷ aa} f≡g = cong₂ _∷_ (f≡g a) (map-cong {aa = aa} f≡g)

fold : ∀ (M : Monoid zero zero) → List (Monoid.Carrier M) → Monoid.Carrier M
fold M [] = Monoid.ε M
fold M (m ∷ mm) = Monoid._∙_ M m (fold M mm)

depfold₂ : ∀ {A B : Set} {C : A → A → Setoid zero zero} {f : A → B → A} {a₁ a₂} bb →
      (∀ a₁ a₂ b → C a₁ a₂ ⟶ C (f a₁ b) (f a₂ b)) →
      C a₁ a₂ ⟶ C (fold (EndoR A) (Data.List.map (λ y x → f x y) bb) a₁) (fold (EndoR A) (Data.List.map (λ y x → f x y) bb) a₂)
depfold₂ [] ff = id
depfold₂ (b ∷ bb) ff = depfold₂ bb ff ∘ ff _ _ b

LIST : FoldFunc 
LIST = record { 
  o = List ;
  map = Data.List.map ;
  map-cong = map-cong ;
  fold = fold ;
  depfold₂ = depfold₂ }

