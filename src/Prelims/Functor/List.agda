module Prelims.Functor.List where
open import Level
open import Function
open import Function.Equality using (_⟶_) renaming (_∘_ to _○_)
open import Data.List hiding (foldl)
open import Prelims.EqReasoning
open import Prelims.Functor.Foldable

map-cong : ∀ {A B : Set} {f g : A → B} {aa : List A} →
         (∀ x → f x ≡ g x) → Data.List.map f aa ≡ Data.List.map g aa
map-cong {aa = []} _ = refl
map-cong {aa = a ∷ aa} f≡g = cong₂ _∷_ (f≡g a) (map-cong f≡g)

map-id : ∀ {A : Set} {aa : List A} → Data.List.map (λ x → x) aa ≡ aa
map-id {aa = []} = refl
map-id {aa = a ∷ aa} = cong (λ l → a ∷ l) map-id

map-comp : ∀ {A B C : Set} {g : B → C} {f : A → B} {aa : List A} →
  Data.List.map (g ∘ f) aa ≡ Data.List.map g (Data.List.map f aa)
map-comp {aa = []} = refl
map-comp {g = g} {f} {a ∷ aa} = cong (λ x → g (f a) ∷ x) map-comp

foldl : ∀ {A : Set} {B : Set₁} → (B → A → B) → B → List A → B
foldl f b [] = b
foldl f b (a ∷ aa) = foldl f (f b a) aa

foldl-cong : ∀ {A B} {f g : B → A → B} {b : B} (aa : List A) →
  (∀ x y → f x y ≡ g x y) → foldl f b aa ≡ foldl g b aa
foldl-cong [] f≡g = refl
foldl-cong {f = f} {g} {b} (a ∷ aa) f≡g = let open ≡-Reasoning in 
  begin
    foldl f (f b a) aa
  ≡⟨ foldl-cong aa f≡g ⟩
    foldl g (f b a) aa
  ≡⟨ cong (λ x → foldl g x aa) (f≡g b a) ⟩
    foldl g (g b a) aa
  ∎

depfold₂ : ∀ {A : Set₁} {B} {C : A → A → Setoid zero zero} {f g : A → B → A}
  {a₁ a₂ : A} (bb : List B) →
  (∀ x y z → C x y ⟶ C (f x z) (g y z)) →
  C a₁ a₂ ⟶ C (foldl f a₁ bb) (foldl g a₂ bb)
depfold₂ [] hyp = Function.Equality.id
depfold₂ {a₁ = a₁} {a₂} (b ∷ bb) hyp = depfold₂ bb hyp ○ hyp a₁ a₂ b

LIST : FoldFunc
LIST = record
  { functor = record
    { F = List
    ; map = Data.List.map
    ; map-cong = map-cong
    ; map-id = map-id
    ; map-comp = map-comp
    } 
  ; isFoldable = record 
    { foldl = foldl
    ; foldl-cong = foldl-cong
    ; depfold₂ = depfold₂
    }
  }
