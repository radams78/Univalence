open import Data.Unit
open import Data.Product hiding (swap)
open import Relation.Binary.PropositionalEquality
module _ (A : Set) (let T = ⊤ → {p : A × A} → A) (f : T) where

swap : T → T
swap f _ {x , y} = f _ {y , x}
-- becomes by record pattern elimination
-- IS: swap f _ xy = f _ {proj₂ xy , proj₁ xy}
-- SHOULD BE: swap f _ {xy} = f _ {proj₂ xy , proj₁ xy}

test : f ≡ swap (swap f)
test with Set -- triggers internal checking of type
test | _ = refl

