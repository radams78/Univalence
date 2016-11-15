\begin{code}
module Prelims.Foldable where
open import Level
open import Data.Product renaming (_,_ to _,p_) hiding (map)
open import Data.List hiding (map;foldr)
open import Algebra
open import Prelims hiding (sym;map)

record FoldFunc : Set₁ where
  field
    o : Set → Set
    map : ∀ {A B : Set} → (A → B) → o A → o B
    foldr : ∀ {A B : Set} → (A → B → B) → B → o A → B

  fold : ∀ {i} {M : Monoid zero i} → o (Monoid.Carrier M) → Monoid.Carrier M
  fold {i} {M} = foldr (Monoid._∙_ M) (Monoid.ε M)

  Endo : Set → Monoid zero zero
  Endo A = record { 
    Carrier = A → A ; 
    _≈_ = λ f g → ∀ x → f x ≡ g x ; 
    _∙_ = λ g f x → g (f x) ; 
    ε = λ x → x ; 
    isMonoid = record { 
      isSemigroup = record { 
        isEquivalence = record { 
          refl = λ _ → refl ; 
          sym = λ f≡g x → Prelims.sym (f≡g x) ; 
          trans = λ f≡g g≡h x → Prelims.trans (f≡g x) (g≡h x) } ; 
        assoc = λ _ _ _ _ → refl ; 
        ∙-cong = λ {_} {g} g≡g' f≡f' x → trans (g≡g' _) (Prelims.cong g (f≡f' x)) } ; 
      identity = (λ _ _ → refl) ,p (λ _ _ → refl) } }

  LIST : FoldFunc
  LIST = record { 
    o = List ; 
    map = Data.List.map ; 
    foldr = Data.List.foldr }
\end{code}
