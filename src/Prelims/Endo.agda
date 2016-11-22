module Prelims.Endo where
open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Algebra

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
      identity = (λ _ _ → refl) , (λ _ _ → refl) } }

