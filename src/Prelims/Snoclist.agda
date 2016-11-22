module Prelims.Snoclist where
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Function.Equality hiding (cong)
open import Algebra
open import Data.Nat
open import Data.Fin
open import Prelims.Endo
open import Prelims.Foldable

infixl 20 _snoc_
data snocList (A : Set) : Set where
  [] : snocList A
  _snoc_ : snocList A → A → snocList A

snocmap : ∀ {A B} → (A → B) → snocList A → snocList B
snocmap f [] = []
snocmap f (aa snoc a) = snocmap f aa snoc f a

snocmapcong : ∀ {A B} {f g : A → B} {l : snocList A} →
  (∀ x → f x ≡ g x) → snocmap f l ≡ snocmap g l
snocmapcong {l = []} f≡g = refl
snocmapcong {l = l snoc x} f≡g = cong₂ _snoc_ (snocmapcong f≡g) (f≡g x)

snocfold : ∀ (M : Monoid Level.zero Level.zero) → snocList (Monoid.Carrier M) → Monoid.Carrier M
snocfold M [] = Monoid.ε M
snocfold M (mm snoc m) = Monoid._∙_ M (snocfold M mm) m

snocdepfold₂ : ∀ {A B : Set} {C : A → A → Setoid Level.zero Level.zero} {f : A → B → A} {a₁ a₂ : A}
      (bb : snocList B) →
      ((a₃ a₄ : A) (b : B) → C a₃ a₄ ⟶ C (f a₃ b) (f a₄ b)) →
      C a₁ a₂ ⟶
      C (snocfold (EndoR A) (snocmap (λ y x → f x y) bb) a₁)
      (snocfold (EndoR A) (snocmap (λ y x → f x y) bb) a₂)
snocdepfold₂ [] _ = id
snocdepfold₂ (bb snoc b) ff = ff _ _ b ∘ snocdepfold₂ bb ff

SNOCLIST : FoldFunc
SNOCLIST = record { 
  o = snocList ; 
  map = snocmap ;
  map-cong = snocmapcong ;
  fold = snocfold ;
  depfold₂ = snocdepfold₂ }

map-id : ∀ {A} {f : A → A} {l : snocList A} →
  (∀ x → f x ≡ x) → snocmap f l ≡ l
map-id {l = []} _ = refl
map-id {l = l snoc a} hyp = cong₂ _snoc_ (map-id hyp) (hyp a)

map-comp : ∀ {A B C} {g : B → C} {f : A → B} {l : snocList A} →
  snocmap (λ x → g (f x)) l ≡ snocmap g (snocmap f l)
map-comp {l = []} = refl
map-comp {g = g} {f = f} {l = l snoc a} = cong (λ x → x snoc g (f a)) map-comp

replicate : ∀ {A} → ℕ → A → snocList A
replicate zero _ = []
replicate (suc n) a = replicate n a snoc a

data snocVec (A : Set) : ℕ → Set where
  [] : snocVec A ℕ.zero
  _snoc_ : ∀ {n} → snocVec A n → A → snocVec A (ℕ.suc n)

lookup : ∀ {A : Set} {n} → Fin n → snocVec A n → A
lookup zero (_ snoc x) = x
lookup (suc i) (v snoc _) = lookup i v
