\begin{code}
module Prelims.Foldable where
open import Level
open import Data.Product renaming (_,_ to _,p_) hiding (map)
open import Data.List hiding (map;foldl)
open import Algebra
open import Function.Equality hiding (cong)
open import Prelims.EqReasoning

EndoR : Set → Monoid zero zero
EndoR A = record { 
    Carrier = A → A ; 
    _≈_ = λ f g → ∀ x → f x ≡ g x ; 
    _∙_ = λ g f x → f (g x) ; 
    ε = λ x → x ; 
    isMonoid = record { 
      isSemigroup = record { 
        isEquivalence = record { 
          refl = λ _ → refl ; 
          sym = λ f≡g x → sym (f≡g x) ; 
          trans = λ f≡g g≡h x → trans (f≡g x) (g≡h x) } ; 
        assoc = λ _ _ _ _ → refl ; 
        ∙-cong = λ {f} {f'} {g} {g'} f≡f' g≡g' x → trans (g≡g' (f x)) (cong g' (f≡f' x)) } ; 
      identity = (λ _ _ → refl) ,p (λ _ _ → refl) } }

record FoldFunc : Set₁ where
  field
    o : Set → Set
    map : ∀ {A B} → (A → B) → o A → o B
    fold : ∀ {M : Monoid zero zero} → o (Monoid.Carrier M) → Monoid.Carrier M
    depfold₂ : ∀ {A B : Set} {C : A → A → Setoid zero zero} {f : A → B → A} {a₁ a₂ bb} →
      (∀ a₁ a₂ b → C a₁ a₂ ⟶ C (f a₁ b) (f a₂ b)) →
      C a₁ a₂ ⟶ C (fold {M = EndoR A} (map (λ y x → f x y) bb) a₁) (fold {M = EndoR A} (map (λ y x → f x y) bb) a₂)

  foldl : ∀ {A B : Set} → (A → B → A) → A → o B → A
  foldl {A} {B} f a bb = fold {M = EndoR A} (map (λ b a → f a b) bb) a

fold : ∀ {M : Monoid zero zero} → List (Monoid.Carrier M) → Monoid.Carrier M
fold {M} [] = Monoid.ε M
fold {M} (m ∷ mm) = Monoid._∙_ M m (fold {M} mm)

depfold₂ : ∀ {A B : Set} {C : A → A → Setoid zero zero} {f : A → B → A} {a₁ a₂ bb} →
      (∀ a₁ a₂ b → C a₁ a₂ ⟶ C (f a₁ b) (f a₂ b)) →
      C a₁ a₂ ⟶ C (fold {M = EndoR A} (Data.List.map (λ y x → f x y) bb) a₁) (fold {M = EndoR A} (Data.List.map (λ y x → f x y) bb) a₂)
depfold₂ {bb = []} ff = id
depfold₂ {bb = b ∷ bb} ff = depfold₂ {bb = bb} ff ∘ ff _ _ b

LIST : FoldFunc 
LIST = record { 
  o = List ;
  map = Data.List.map ;
  fold = λ {M} → fold {M} ;
  depfold₂ = λ {_ _ _ _ _ _ bb} → depfold₂ {bb = bb} }
\end{code}
