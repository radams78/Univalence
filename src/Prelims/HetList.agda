module Prelims.HetList where
open import Function.Equality hiding (setoid;cong)
open import Relation.Binary.PropositionalEquality
open import Data.Unit hiding (setoid)
open import Data.Product hiding (zip)
open import Data.List hiding (zip;all)
open import Prelims.Functor

HetL : ∀ {A} F → (A → Set) → FoldFunc.F F A → Set
HetL F B aa = FoldFunc.foldl F (λ X a → X × B a) ⊤ aa

HetL-map : ∀ {A F} {B C : A → Set} {aa} → (∀ a → B a → C a) → HetL F B aa → HetL F C aa
HetL-map {A} {F} {B} {C} {aa} f bb = FoldFunc.depfold₂ F {Set} {A} {λ X Y → setoid X ⇨ setoid Y} {λ X a → X × B a} {λ X a → X × C a} {⊤} {⊤} aa 
  (λ A₁ A₂ b → record { 
    _⟨$⟩_ = λ g → record { 
      _⟨$⟩_ = λ {(x , y) → g ⟨$⟩ x , f b y} ; 
      cong = cong (λ p → g ⟨$⟩ (proj₁ p) , f b (proj₂ p)) } ; 
    cong = λ g≡g' x≡y → cong₂ _,_ (g≡g' (cong proj₁ x≡y)) (cong (f b) (cong proj₂ x≡y)) }) ⟨$⟩
  id ⟨$⟩ bb
--TODO Refactor

data HetList {A : Set} (B : A → Set) : List A → Set where
  [] : HetList B []
  _∷_ : ∀ {a aa} → B a → HetList B aa → HetList B (a ∷ aa)

K : ∀ A B → List A → Set
K A B = HetList {A} (λ _ → B)

zip : ∀ {A : Set} {B C : A → Set} {aa : List A} → HetList B aa → HetList C aa → 
  HetList (λ a → B a × C a) aa
zip [] [] = []
zip (b ∷ bb) (c ∷ cc) = (b , c) ∷ zip bb cc

data all {A} {B : A → Set} (C : ∀ {a} → B a → Set) : ∀ (aa : List A) → 
  HetList B aa → Set where
  [] : all C [] []
  _∷_ : ∀ {a} {aa} {b} {bb} → C {a} b → all C aa bb → all C (a ∷ aa) (b ∷ bb)

unhet : ∀ {A B aa} → K A B aa → List B
unhet [] = []
unhet (b ∷ bb) = b ∷ unhet bb

infixl 20 _snoc_
data HetsnocList {A} (B : A → Set) : snocList A → Set where
  [] : HetsnocList B []
  _snoc_ : ∀ {aa} {a} → HetsnocList B aa → B a → HetsnocList B (aa snoc a)
