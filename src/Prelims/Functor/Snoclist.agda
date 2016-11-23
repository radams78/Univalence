module Prelims.Functor.Snoclist where
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Function.Equality hiding (cong)
open import Algebra
open import Data.Nat
open import Data.Fin hiding (lift)
open import Prelims.Endo
open import Prelims.Functor.Foldable

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

snocfoldl : ∀ {A} {B : Set₁} → (B → A → B) → B → snocList A → B
snocfoldl f b [] = b
snocfoldl f b (aa snoc a) = f (snocfoldl f b aa) a

snocfoldl-cong : ∀ {A B} {f g : B → A → B} {b : B} (aa : snocList A) →
  (∀ x y → f x y ≡ g x y) → snocfoldl f b aa ≡ snocfoldl g b aa
snocfoldl-cong [] _ = refl
snocfoldl-cong {f = f} {g} {b} (aa snoc a) f≡g = let open ≡-Reasoning in begin
    f (snocfoldl f b aa) a
  ≡⟨ f≡g _ _ ⟩
    g (snocfoldl f b aa) a
  ≡⟨ cong (λ x → g x a) (snocfoldl-cong aa f≡g) ⟩
    g (snocfoldl g b aa) a
  ∎

snocdepfold₂ : ∀ {A : Set₁} {B} {C : A → A → Setoid Level.zero Level.zero} {f g : A → B → A} {a₁ a₂ : A}
      (bb : snocList B) →
      ((a₃ a₄ : A) (b : B) → C a₃ a₄ ⟶ C (f a₃ b) (g a₄ b)) →
      C a₁ a₂ ⟶
      C (snocfoldl f a₁ bb) (snocfoldl g a₂ bb)
snocdepfold₂ [] _ = id
snocdepfold₂ (bb snoc b) ff = ff _ _ b ∘ snocdepfold₂ bb ff

snocmap-id : ∀ {A} {l : snocList A} →
  snocmap (λ x → x) l ≡ l
snocmap-id {l = []} = refl
snocmap-id {l = l snoc a} = cong₂ _snoc_ (snocmap-id {l = l}) refl

snocmap-comp : ∀ {A B C} {g : B → C} {f : A → B} {l : snocList A} →
  snocmap (λ x → g (f x)) l ≡ snocmap g (snocmap f l)
snocmap-comp {l = []} = refl
snocmap-comp {g = g} {f = f} {l = l snoc a} = cong (λ x → x snoc g (f a)) snocmap-comp

SNOCLIST : FoldFunc
SNOCLIST = record { 
  functor = record {
    F = snocList ; 
    map = snocmap ;
    map-cong = snocmapcong ;
    map-id = snocmap-id ;
    map-comp = snocmap-comp } ;
  isFoldable = record {
    foldl = snocfoldl ;
    foldl-cong = snocfoldl-cong ;
    depfold₂ = snocdepfold₂ } }

replicate : ∀ {A} → ℕ → A → snocList A
replicate zero _ = []
replicate (suc n) a = replicate n a snoc a

data snocVec (A : Set) : ℕ → Set where
  [] : snocVec A ℕ.zero
  _snoc_ : ∀ {n} → snocVec A n → A → snocVec A (ℕ.suc n)

lookup : ∀ {A : Set} {n} → Fin n → snocVec A n → A
lookup zero (_ snoc x) = x
lookup (suc i) (v snoc _) = lookup i v
