module Prelims.Setoid where
open import Relation.Binary.PropositionalEquality
open import Function.Equality hiding (setoid;cong)
open import Data.Product

prodf : ∀ {A B C D : Set} → (C → D) → (setoid A ⇨ setoid B) ⟶ (setoid (A × C) ⇨ setoid (B × D))
prodf f = record { 
  _⟨$⟩_ = λ g → record { 
    _⟨$⟩_ = λ { (a , c) → (g ⟨$⟩ a , f c) } ; 
    cong = cong _ } ; -- TODO General construction (A → B) → (setoid A ⟶ setoid B)
  cong = λ g≡g' p≡p' → cong₂ _,_ (g≡g' (cong proj₁ p≡p')) (cong f (cong proj₂ p≡p')) 