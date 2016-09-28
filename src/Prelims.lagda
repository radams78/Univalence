\begin{frame}
Test
\end{frame}

\AgdaHide{\section{Preliminaries}

\begin{code}
--TODO Add these to standard library?
module Prelims where

open import Relation.Binary public hiding (_⇒_)
import Relation.Binary.EqReasoning
open import Relation.Binary.PropositionalEquality public using (_≡_;refl;sym;trans;cong;cong₂;subst;subst₂)

module Bifunction 
  {r₁ r₂ s₁ s₂ t₁ t₂} {A : Setoid r₁ r₂} {B : Setoid s₁ s₂} {C : Setoid t₁ t₂} 
  (f : Setoid.Carrier A → Setoid.Carrier B → Setoid.Carrier C) (wd : ∀ {a a' b b'} → Setoid._≈_ A a a' → Setoid._≈_ B b b' → Setoid._≈_ C (f a b) (f a' b')) where

  congl : ∀ {a a' b} → Setoid._≈_ A a a' → Setoid._≈_ C (f a b) (f a' b)
  congl a≈a' = wd a≈a' (Setoid.refl B)

  congr : ∀ {a b b'} → Setoid._≈_ B b b' → Setoid._≈_ C (f a b) (f a b')
  congr b≈b' = wd (Setoid.refl A) b≈b'

module EqReasoning {s₁ s₂} (S : Setoid s₁ s₂) where
  open Setoid S using (_≈_)
  open Relation.Binary.EqReasoning S public

  infixr 2 _≡⟨⟨_⟩⟩_
  _≡⟨⟨_⟩⟩_ : ∀ x {y z} → y ≈ x → y ≈ z → x ≈ z
  _ ≡⟨⟨ y≈x ⟩⟩ y≈z = Setoid.trans S (Setoid.sym S y≈x) y≈z

module ≡-Reasoning {a} {A : Set a} where
  open Relation.Binary.PropositionalEquality
  open ≡-Reasoning {a} {A} public

  infixr 2 _≡⟨⟨_⟩⟩_
  _≡⟨⟨_⟩⟩_ : ∀ (x : A) {y z} → y ≡ x → y ≡ z → x ≡ z
  _ ≡⟨⟨ y≡x ⟩⟩ y≡z = trans (sym y≡x) y≡z

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
        a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃ _ refl refl refl = refl

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a' b b' c c' d d'} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → f a b c d ≡ f a' b' c' d'
cong₄ _ refl refl refl refl = refl

subst₃ : ∀ {A B C : Set} (P : A → B → C → Set) {a a' b b' c c'} →
         a ≡ a' → b ≡ b' → c ≡ c' → P a b c → P a' b' c'
subst₃ _ refl refl refl Pabc = Pabc

subst₄ : ∀ {A1 A2 A3 A4 : Set} (P : A1 → A2 -> A3 -> A4  → Set) 
           {a1 a1' a2 a2' a3 a3' a4 a4'} →
         a1 ≡ a1' -> a2 ≡ a2' -> a3 ≡ a3' -> a4 ≡ a4' ->
         P a1 a2 a3 a4 -> P a1' a2' a3' a4'
subst₄ _ refl refl refl refl Paaaa = Paaaa

infixl 20 _snoc_
data snocList (A : Set) : Set where
  [] : snocList A
  _snoc_ : snocList A → A → snocList A
\end{code}
}
