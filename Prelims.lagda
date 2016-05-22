\begin{frame}
Test
\end{frame}

\AgdaHide{\section{Preliminaries}

\begin{code}
module Prelims where

open import Relation.Binary public hiding (_⇒_)
import Relation.Binary.EqReasoning
open import Relation.Binary.PropositionalEquality public using (_≡_;refl;sym;trans;cong;cong₂;subst;subst₂)

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
--TODO Add this to standard library

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

data snocList (A : Set) : Set where
  [] : snocList A
  _∷_ : snocList A → A → snocList A
\end{code}
}
