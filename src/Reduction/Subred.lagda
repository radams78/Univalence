\begin{code}
open import Prelims.Closure
open import Grammar.Base

module Reduction.Subred (G : Grammar) where
open Grammar G

_⊆_ : Reduction → Reduction → Set
R ⊆ S = ∀ {V} {AA} {K} {c : Con (SK AA K)} {E : ListAbs V AA} {F} → R c E F → S c E F

module Subred (R S : Reduction) where

  open import Reduction G R as RedR
  open import Reduction G S as RedS

  sub-osr : ∀ {V C K} {E F : Subexp V C K} → R ⊆ S → E RedR.⇒ F → E RedS.⇒ F
  sub-osr R⊆S (RedR.redex E▷F) = RedS.redex (R⊆S E▷F)
  sub-osr R⊆S (RedR.app EE⇒FF) = RedS.app (sub-osr R⊆S EE⇒FF)
  sub-osr R⊆S (RedR.appl E⇒F) = RedS.appl (sub-osr R⊆S E⇒F)
  sub-osr R⊆S (RedR.appr E⇒F) = RedS.appr (sub-osr R⊆S E⇒F)

  sub-red : ∀ {V C K} {E F : Subexp V C K} → R ⊆ S → E RedR.↠ F → E RedS.↠ F
  sub-red R⊆S (inc E⇒F) = inc (sub-osr R⊆S E⇒F)
  sub-red R⊆S ref = ref
  sub-red R⊆S (trans E↠F F↠G) = trans (sub-red R⊆S E↠F) (sub-red R⊆S F↠G)
\end{code}
